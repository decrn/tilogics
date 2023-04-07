From Coq Require Import
  Relations.Relation_Definitions
  Strings.String.
From Em Require Import
     Definitions Context Environment STLC.
From Em Require Symbolic Shallow.

Import ctx.notations.

(* The refinement proof, relating the deeply-embedded or symbolic `generate`
   to the shallowly-embedded `generate` is accomplished
   using a logical relation similar to [Keuchel22]. *)

(* A variation on the definition of `Relation_Definitions.relation` but now
   relating a World-indexed Type `A` to a regular type `a`. Given a world `w`
   and an assignment (or valuation) `ass` assigning concrete types to each
   unification variable in the world, we can relate the world-indexed type `A w`
   to the regular type `a` *)
Definition Relation (A : TYPE) (a : Type) : Type :=
  forall (w : World) (ass : Assignment w),
  A w -> a -> Prop.

(* To start, we define a relation between deeply-embedded object-language types `Ty`
   and shallowly-embedded object-language types `ty` *)
(* These two are related if, given a world and an assignment (or valuation) from unification variables
   in the world to concrete object language types, applying the assignment to the `Ty` is equal to `ty` *)
Definition RTy : Relation Ty ty :=
  fun (w : Ctx nat) (ass : Assignment w) (T : Ty w) (t : ty) =>
    inst T ass = t.

(* We can also relate deeply-embedded free computations `FreeM` to shallowly-embedded free computations `freeM`.
   This is parametric in the relation of values `A` and `a` in their respective free monads *)
(* i.e., RFree : Relation A a -> Relation (FreeM A) (freeM a) *)

Inductive RFree {A a} (RA : Relation A a) (w : World)
                 (ass : Assignment w) : FreeM A w -> freeM a -> Prop :=
| RRet : forall (V : A w) (v : a),
    RA w ass V v ->
    RFree RA w ass (Ret_Free _ _ V) (ret_free _ v)
| RFalse :
    RFree RA w ass (Fail_Free _ _) (fail_free _)
| RAssert : forall T1 T2 t1 t2 Cont cont,
    RTy w ass T1 t1 ->
    RTy w ass T2 t2 ->
    RFree RA w ass Cont cont ->
    RFree RA w ass (Bind_AssertEq_Free _ _ T1 T2 Cont) (bind_asserteq_free _ t1 t2 cont)
| RExists : forall i Cont cont,
    (forall (t : ty),
      RFree RA (w ▻ i) (env.snoc ass i t) Cont (cont t)) ->
      RFree RA w ass (Bind_Exists_Free _ _ i Cont) (bind_exists_free _ cont).

Inductive REnv w ass : Env w -> env -> Prop :=
| RPair : forall k V v Γ γ,
    RTy w ass V v ->
    REnv w ass Γ γ ->
    REnv w ass ((k, V) :: Γ)%list ((k, v) :: γ)%list
| RNil :
    REnv w ass nil%list nil%list.

(* Relating boxed symbolic values is more interesting, since the accessibility witness
   can now contain an arbitrary amount of new unification variables.
   We say that in every accessible world, i.e. given a witness ω: w ⊑ w',
   a symbolic computation x is related to a shallow computation y,
   iff the type assignment in w' subsumes the assignment in w.
   an assignment a subsumes an assignment b iff every type assignment in b
   also occurs in a. E.g.
   { τ₀ -> Bool ; } is subsumed by { τ₀ -> Bool ; τ₁ -> Arrow τ₀ τ₀ }
   But
   { τ₀ -> Bool ; } is NOT subsumed by { τ₀ -> Nat ; τ₁ -> Arrow τ₀ τ₀ }
   since τ₀ has a different assignment.
 *)

Import World.notations.
#[local] Notation "□⁺ A" :=
  (Box Alloc A)
    (at level 9, format "□⁺ A", right associativity)
    : indexed_scope.

Open Scope indexed_scope.

Definition RBox {A a} (RA : Relation A a) : Relation □⁺A a :=
  fun (w : Ctx nat) (ass : Assignment w) (x : □⁺A w) (y : a) =>
    forall (w' : Ctx nat) (ω : Alloc w w') (ass' : Assignment w'),
      ass = inst ω ass' ->
      RA _ ass' (x w' ω) y.

(* For functions/impl: related inputs go to related outputs *)
Definition RArr {A a B b} (RA : Relation A a) (RB : Relation B b) : Relation (Impl A B) (a -> b) :=
  fun w ass fS fs => forall (V : A w) (v : a),
    RA w ass V v -> RB w ass (fS V) (fs v).

Definition RUnit : Relation Unit unit :=
  fun w ass _ _ => True.

Declare Scope rel_scope.
Delimit Scope rel_scope with R.
Notation "A -> B" := (RArr A B) : rel_scope.

(* Using our relation on functions, we can now prove
   relatedness of operations in both free monads *)

Lemma Ret_relates_ret {A a} (RA : Relation A a) :
forall (w : Ctx nat) (ass : Assignment w),
    (RA -> (RFree RA))%R w ass (Ret_Free A w) (ret_free a).
Proof.  constructor. assumption. Qed.

Lemma False_relates_false {A a} (RA : Relation A a) :
forall (w : Ctx nat) (ass : Assignment w),
    RFree RA w ass (Fail_Free A w) (@fail_free a).
Proof.  constructor. Qed.

Lemma Assert_relates_assert :
  forall (w : Ctx nat) (ass : Assignment w),
    (RTy -> RTy -> (RFree RUnit))%R w ass Symbolic.assert Shallow.assert.
  Proof. repeat (constructor; try assumption). Qed.

Lemma Exists_relates_exists :
  forall (w : Ctx nat) (ass : Assignment w),
    (RFree RTy) w ass (Symbolic.exists_Ty w) Shallow.exists_ty.
Proof. repeat constructor. Qed.

Lemma pointwise_equal {w : Ctx nat} (a1 a2 : Assignment w) (e : a1 = a2) :
  forall x (xIn : x ∈ w), env.lookup a1 xIn = env.lookup a2 xIn.
Proof. now subst. Qed.

Lemma Bind_relates_bind {A B a b} (RA : Relation A a) (RB : Relation B b) :
  forall (w : Ctx nat) (ass : Assignment w),
    ((RFree RA) -> (RBox (RA -> RFree RB)) -> (RFree RB))%R w ass (bind (M := FreeM) (w := w)) Shallow.bind.
Proof.
  intros w ass ? ? ?.
  induction H;  cbn; intros F f HF; try constructor; try assumption.
  - unfold RBox in HF. unfold RArr in HF. apply HF.
    symmetry. apply inst_refl. apply H.
  - unfold RBox in IHRFree. unfold RArr in IHRFree. apply IHRFree.
    unfold RBox in HF. unfold RArr in HF. apply HF.
  - intro. apply H0. unfold RBox.
    intros. apply HF. clear HF H0 H. rewrite inst_trans. cbn. now rewrite <- H1.
Qed.

(* Should probably generalize this to any constructor *)
Lemma Func_relates_func :
  forall (w : Ctx nat) (ass : Assignment w) D d C c,
    RTy w ass D d ->
    RTy w ass C c ->
    RTy w ass (Ty_func w D C) (ty_func d c).
Proof. intros. inversion H. inversion H0. constructor. Qed.

Class RefinePersist {A a} `{Persistent Alloc A} (RA : Relation A a) : Type :=
  { refine_persist w1 w2 r12 ass V v :
      RA w1 (inst r12 ass) V v ->
      RA w2 ass (persist w1 V w2 r12) v }.

#[export] Instance RefinePersist_Ty : RefinePersist RTy.
Proof. constructor.
  intros. revert v H. unfold RTy. induction V; cbn; intros. apply H. subst.
  f_equal; auto. subst.
  induction r12. auto. cbn. rewrite IHr12. now destruct env.view.
Qed.

#[export] Instance RefinePersist_Env : RefinePersist REnv.
Proof. constructor.
  intros. revert v H. induction V; intros; inversion H; subst; cbn; try constructor.
  now apply refine_persist. now apply IHV.
Qed.

Lemma lift_preserves_relatedness :
  forall w ass t,
    RTy w ass (lift t w) t.
Proof. induction t. constructor. now apply Func_relates_func. Qed.

Arguments Symbolic.assert    : simpl never.
Arguments Shallow.assert     : simpl never.
Arguments Symbolic.exists_Ty : simpl never.
Arguments Shallow.exists_ty  : simpl never.

Lemma generate_fns_are_related (e : expr) (w : Ctx nat) (ass : Assignment w)
  : (REnv -> (RFree RTy))%R w ass (Symbolic.generate e) (Shallow.generate_no_elab e).
Proof.
  revert ass. revert w. induction e; intros w ass; cbn -[persist].
  - intros Γ γ RΓ. repeat constructor.
  - intros Γ γ RΓ. repeat constructor.
  - intros Γ γ RΓ. eapply Bind_relates_bind.
    apply IHe1. apply RΓ. clear IHe1.
    intros w1 ? ? ? ? ? ?. constructor. apply H0. constructor.
    unfold T. eapply Bind_relates_bind. apply IHe2.
    rewrite trans_refl_r. eapply refine_persist; eauto.
    subst. apply RΓ.
    intros ? ? ? ? ? ? ?. eapply Bind_relates_bind. cbn. apply IHe3.
    eapply refine_persist.
    subst. rewrite inst_trans. apply RΓ.
    intros ? ? ? ? ? ? ?. eapply Bind_relates_bind. apply Assert_relates_assert; cbn.
    eapply refine_persist. subst. assumption. assumption.
    intros ? ? ? ? ? ? ?. eapply Ret_relates_ret.
    eapply refine_persist. rewrite inst_trans. rewrite <- H5. subst. apply H2.
  - intros ? ? ?. induction H. cbn.
    destruct (string_dec s k). now constructor. apply IHREnv.
    cbn. constructor.
  - intros Γ γ RΓ. eapply Bind_relates_bind. apply Exists_relates_exists.
    intros ? ? ? ? ? ? ?. eapply Bind_relates_bind. apply IHe.
    constructor. apply H0.
    apply refine_persist. subst. apply RΓ.
    intros ? ? ? ? ? ? ?. constructor. subst. hnf.
    DepElim.hnf_eq. f_equal; auto.
    refine (refine_persist _ _ _ _ _ _ H0).
  - intros Γ γ RΓ. eapply Bind_relates_bind. apply IHe.
    constructor. apply lift_preserves_relatedness. apply RΓ.
    intros ? ? ? ? ? ? ?. eapply Ret_relates_ret. apply Func_relates_func.
    eapply refine_persist. apply lift_preserves_relatedness. apply H0.
  - intros Γ γ RΓ. eapply Bind_relates_bind. apply Exists_relates_exists.
    intros ? ? ? ? ? ? ?. eapply Bind_relates_bind.
    eapply IHe2. eapply refine_persist. subst. apply RΓ.
    intros ? ? ? ? ? ? ?. eapply Bind_relates_bind.
    eapply IHe1. eapply refine_persist. rewrite inst_trans. subst. apply RΓ.
    intros ? ? ? ? ? ? ?. eapply Bind_relates_bind.
    eapply Assert_relates_assert. apply H4.
    eapply refine_persist. apply Func_relates_func. subst. apply H2.
    eapply refine_persist. subst. apply H0.
    intros ? ? ? ? ? ? ?. apply Ret_relates_ret. eapply refine_persist.
    repeat rewrite inst_trans. rewrite <- H5. rewrite <- H3. subst. apply H0.
Qed.

Inductive RSolved {A a} (RA : Relation A a) (w : Ctx nat) (ass : Assignment w)
  : SolvedM A w -> solvedM a -> Prop :=
| RRetS : forall (V : A w) (v : a),
    RA w ass V v ->
    RSolved RA w ass (Ret_Solved _ _ V) (ret_solved _ v)
| RFailS :
    RSolved RA w ass (Fail_Solved _ _) (fail_solved _)
| RExistsS : forall i Cont cont,
    (forall (t : ty),
      RSolved RA (w ▻ i) (env.snoc ass i t) Cont (cont t)) ->
      RSolved RA w ass (Bind_Exists_Solved _ _ i Cont) (bind_exists_solved _ cont).

(* Definition ROption {A a} (RA : Relation A a) (w : Ctx nat) (ass : Assignment w) *)
(*   : option (A w) -> option a -> Prop := *)
(*   fun O o => *)
(*     match O, o with *)
(*     | Some V, Some v => RA w ass V v *)
(*     | None, None => True *)
(*     | _, _ => False *)
(*     end. *)

(* Lemma solves_are_related {A a} {pA: Persistent Unification.Tri.Tri A} (RA : Relation A a) *)
(*   : (RFree RA -> (RSolved RA))%R ctx.nil env.nil (@Unification.Variant1.solve_ng _ _) (@Shallow.solve a). *)
(* Proof. Admitted. *)

(* Lemma infers_are_related (e : expr) *)
(*   : (RSolved RTy)%R ctx.nil env.nil (Symbolic.infer_ng e) (Shallow.infer_ng e). *)
(* Proof. *)
(*   unfold Symbolic.infer_ng, Shallow.infer_ng. *)
(*   apply solves_are_related. apply generate_fns_are_related. *)
(*   constructor. *)
(* Qed. *)

Section Soundness.

  Import SigTNotations.

  Fixpoint WLP {w} (V : SolvedM Ty w) (Post : ty -> Prop) (gnd : Assignment w) : Prop :=
    match V with
    | Ret_Solved _ _ r => Post (inst r gnd)
    | Fail_Solved _ _ => True
    | Bind_Exists_Solved _ _ i k => forall t, WLP k Post (env.snoc gnd i t)
    end.

  Fixpoint wlp (v : solvedM ty) (Post : ty -> Prop) {struct v} : Prop :=
    match v with
    | ret_solved _ v => Post v
    | fail_solved _ => True
    | bind_exists_solved _ k => forall t, wlp (k t) Post
    end.

  Lemma wlps_are_related : forall ctx gnd V v (R : (RSolved RTy)%R ctx gnd V v) Post,
      (WLP V Post gnd) <-> (wlp v Post).
  Proof.
    intros. revert Post. induction R; cbn; subst.
      + cbn in *. now destruct H.
      + easy.
      + firstorder.
  Qed.

  (* Lemma wlps_infer_ng_equiv : forall e P, *)
  (*     WLP (Symbolic.infer_ng e) P env.nil <-> wlp (Shallow.infer_ng e) P. *)
  (* Proof. intros. apply wlps_are_related. apply infers_are_related. Qed. *)

  Lemma wlp_solved_equiv_unsolved : forall m P,
      Shallow.wlp_freeM m P <-> wlp (Shallow.solve m) P.
  Proof.
    intro. induction m; cbn; intros; try easy.
    destruct Classes.eq_dec. intuition. intuition. cbn. easy.
    firstorder.
  Qed.

  Lemma shallow_infer_ng_sound : forall e,
      wlp (Shallow.infer_ng e) (fun t => exists ee, nil |-- e ; t ~> ee).
  Proof.
    unfold Shallow.infer_ng. intro.
    apply wlp_solved_equiv_unsolved. apply Shallow.generate_no_elab_sound.
  Qed.

  (* Lemma symbolic_infer_ng_sound : forall (e : expr), *)
  (*     WLP (Symbolic.infer_ng e) (fun t => exists ee, nil |-- e ; t ~> ee) env.nil. *)
  (* Proof. *)
  (*   intros. *)
  (*   apply wlps_infer_ng_equiv. apply shallow_infer_ng_sound. *)
  (* Qed. *)

  Lemma symbolic_infer_schematic_sound (e : expr) :
    match Symbolic.infer_schematic e with
    | Some (w; t) => forall ass : Assignment w,
                       exists ee, nil |-- e ; inst t ass ~> ee
    | None        => True
    end.
  Proof.
    (* unfold Symbolic.runTI. intro. *)
    (* pose proof (symbolic_infer_ng_sound e). *)
    (* revert H. apply ground_is_sound. *)
  Admitted.

  Lemma symbolic_infer_grounded_sound : forall e,
    match Symbolic.infer_grounded e with
    | Some t => exists ee, nil |-- e ; t ~> ee
    | None   => True
    end.
  Proof.
    (* unfold Symbolic.runTI. intro. *)
    (* pose proof (symbolic_infer_ng_sound e). *)
    (* revert H. apply ground_is_sound. *)
  Admitted.

  (* Print Assumptions symbolic_infer_schematic_sound. *)

End Soundness.

Section Completeness.

  Import SigTNotations.

  Fixpoint WP {w} (V : SolvedM Ty w) (Post : ty -> Prop) (gnd : Assignment w) : Prop :=
    match V with
    | Ret_Solved _ _ r => Post (inst r gnd)
    | Fail_Solved _ _ => False
    | Bind_Exists_Solved _ _ i k => exists t, WP k Post (env.snoc gnd i t)
    end.

  Fixpoint wp (v : solvedM ty) (Post : ty -> Prop) {struct v} : Prop :=
    match v with
    | ret_solved _ v => Post v
    | fail_solved _ => False
    | bind_exists_solved _ k => exists t, wp (k t) Post
    end.

  Lemma wps_are_related : forall ctx gnd V v (R : (RSolved RTy)%R ctx gnd V v) Post,
      (WP V Post gnd) <-> (wp v Post).
  Proof.
    intros. revert Post. induction R; cbn; subst.
      + cbn in *. now destruct H.
      + easy.
      + firstorder.
  Qed.

  (* Lemma wps_infer_ng_equiv : forall e P, *)
  (*     WP (Symbolic.infer_ng e) P env.nil <-> wp (Shallow.infer_ng e) P. *)
  (* Proof. intros. apply wps_are_related. apply infers_are_related. Qed. *)

  Lemma wp_solved_equiv_unsolved : forall m P,
      Shallow.wp_freeM m P <-> wp (Shallow.solve m) P.
  Proof.
    intro. induction m; cbn; intros; try easy.
    destruct Classes.eq_dec. intuition. intuition. firstorder.
  Qed.

  Lemma shallow_infer_ng_complete : forall e t ee,
      nil |-- e ; t ~> ee -> wp (Shallow.infer_ng e) (fun t' => t = t').
  Proof.
    unfold Shallow.infer_ng. intros.
    apply wp_solved_equiv_unsolved. now apply (Shallow.generate_no_elab_complete _ _ ee).
  Qed.

  Lemma symbolic_infer_schematic_complete (e : expr) t ee :
    nil |-- e ; t ~> ee ->
    match Symbolic.infer_schematic e with
    | Some (w; T) => exists ass : Assignment w, inst T ass = t
    | None        => False
    end.
  Proof.
    (* unfold Symbolic.runTI. intro. *)
    (* pose proof (symbolic_infer_ng_sound e). *)
    (* revert H. apply ground_is_sound. *)
  Admitted.

  (* Print Assumptions symbolic_infer_schematic_complete. *)

End Completeness.

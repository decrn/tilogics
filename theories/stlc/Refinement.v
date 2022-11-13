Require Import Relation_Definitions String.
From Em Require Import
     Context Environment STLC.
Import ctx.notations.
From Em Require Symbolic Shallow.

(* The refinement proof, relating the deeply-embedded or symbolic `infer`
   to the shallowly-embedded `infer` is accomplished
   using a logical relation similar to [Keuchel22]. *)
Definition Assignment : Ctx nat -> Type :=
  env.Env (fun _ => ty).

(* A  variation on the definition of `Relations.Relation_Definitions.relation` but now
   relating a World-indexed Type `A` to a regular type `a` *)
Check relation.
(* Given a world `w` and an assignment (or valuation) `ass` assigning concrete types to
   each unification variable in the world, we can relate the world-indexed type `A w`
   to the regular type `a` *)
Definition Relation (A : Ctx nat -> Type) (a : Type) : Type :=
  forall (w : Ctx nat) (ass : Assignment w),
  A w -> a -> Prop.

(* To start, we define a relation between deeply-embedded object-language types `Ty`
   and shallowly-embedded object-language types `ty` *)
(* These two are related if, given a world and an assignment (or valuation) from unification variables
   in the world to concrete object language types, applying the assignment to the `Ty` is equal to `ty` *)
Definition RTy : Relation Ty ty :=
  fun (w : Ctx nat) (ass : Assignment w) (T : Ty w) (t : ty) =>
    Unification.applyassign T ass = t.

(* We can also relate deeply-embedded free computations `Cstr` to shallowly-embedded free computations `freeM`.
   This is parametric in the relation of values `A` and `a` in their respective free monads *)
(* i.e., RFree : Relation A a -> Relation (Cstr A) (freeM a) *)

Inductive RFree {A a} (RA : Relation A a) (w : Ctx nat)
                 (ass : Assignment w) : Cstr A w -> freeM a -> Prop :=
| RPure : forall (V : A w) (v : a),
    RA w ass V v ->
    RFree RA w ass (C_val _ _ V) (ret_free _ v)
| RFalse :
    RFree RA w ass (C_fls _ _) (fail_free _)
| RAssert : forall T1 T2 t1 t2 Cont cont,
    RTy w ass T1 t1 ->
    RTy w ass T2 t2 ->
    RFree RA w ass Cont cont ->
    RFree RA w ass (C_eqc _ _ T1 T2 Cont) (bind_assert_free _ t1 t2 cont)
| RExists : forall i Cont cont,
    (forall (t : ty),
      RFree RA (w ▻ i) (env.snoc ass i t) Cont (cont t)) ->
      RFree RA w ass (C_exi _ _ i Cont) (bind_exists_free _ cont).

Fixpoint compose {Σ₁ c : Ctx nat} (a : Symbolic.Accessibility Σ₁ c) {struct a} :
  Assignment c -> Assignment Σ₁ :=
  match a in (Symbolic.Accessibility _ c0) return (Assignment c0 -> Assignment Σ₁) with
  | Symbolic.refl _ => fun X0 : Assignment Σ₁ => X0
  | Symbolic.fresh _ α Σ₂ a0 =>
      fun X0 : Assignment Σ₂ =>
        match env.snocView (compose a0 X0) with
        | env.isSnoc E _ => E
        end
  end.

Lemma compose_refl : forall w ass,
    compose (Symbolic.refl w) ass = ass.
Proof. easy. Qed.

Print Symbolic.trans.

Lemma compose_trans {w1 w2 w3 : Ctx nat} : forall ass r12 r23,
  compose r12 (compose r23 ass) = compose (@Symbolic.trans w1 w2 w3 r12 r23) ass.
Proof. intros. induction r12. auto. cbn. rewrite IHr12. reflexivity. Qed.

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

Definition RBox {A a} (RA : Relation A a) : Relation (Symbolic.Box A) a :=
  fun (w : Ctx nat) (ass : Assignment w) (x : Symbolic.Box A w) (y : a) =>
    forall (w' : Ctx nat) (ω : Symbolic.Accessibility w w') (ass' : Assignment w'),
      ass = compose ω ass' ->
      RA _ ass' (x w' ω) y.

(* For functions/impl: related inputs go to related outputs *)
Definition RArr {A a B b} (RA : Relation A a) (RB : Relation B b) : Relation (Symbolic.Impl A B) (a -> b) :=
  fun w ass fS fs => forall (V : A w) (v : a),
    RA w ass V v -> RB w ass (fS V) (fs v).

Definition RUnit : Relation Symbolic.Unit unit :=
  fun w ass _ _ => True.

Declare Scope rel_scope.
Delimit Scope rel_scope with R.
Notation "A -> B" := (RArr A B) : rel_scope.

Definition REnv : Relation Env env :=
  fun (w : Ctx nat) (ass : Assignment w) (Γ : Env w) (γ : env) => forall (pvar : string),
    match (value pvar Γ), (value pvar γ) with
    | Some T, Some t => RTy w ass T t
    | None, None => True
    | _, _ => False
    end.
  (* Binary parametricity translation *)

(* Using our relation on functions, we can now prove
   relatedness of operations in both free monads *)

Lemma Pure_relates_pure {A a} (RA : Relation A a) :
forall (w : Ctx nat) (ass : Assignment w),
    (RA -> (RFree RA))%R w ass (C_val A w) (ret_free a).
Proof.  constructor. assumption. Qed.

Lemma False_relates_false {A a} (RA : Relation A a) :
forall (w : Ctx nat) (ass : Assignment w),
    RFree RA w ass (C_fls A w) (@fail_free a).
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
    ((RFree RA) -> (RBox (RA -> RFree RB)) -> (RFree RB))%R w ass (@Symbolic.bind A B w) Shallow.bind.
Proof.
  intros w ass ? ? ?.
  induction H;  cbn; intros F f HF; try constructor; try assumption.
  - unfold RBox in HF. unfold RArr in HF. apply HF.
    symmetry. apply compose_refl. apply H.
  - unfold RBox in IHRFree. unfold RArr in IHRFree. apply IHRFree.
    unfold RBox in HF. unfold RArr in HF. apply HF.
  - intro. apply H0. unfold RBox.
    intros. apply HF. clear HF H0 H. rewrite <- compose_trans. cbn. now rewrite <- H1.
Qed.

Arguments Symbolic.assert : simpl never.
Arguments Shallow.assert : simpl never.
Arguments Symbolic.exists_Ty : simpl never.
Arguments  Shallow.exists_ty : simpl never.

(* Singleton method or not? *)
Class PersistLaws (A : Ctx nat -> Type) `{Symbolic.Persistent A} : Type :=
  { refine_persist a w1 w2 r12 ass1 ass2 V v
    (RA : Relation A a)
    (A : ass1 = compose r12 ass2)
    (R : RA w1 ass1 V v) :
    RA w2 ass2 (Symbolic.persist w1 V w2 r12) v }.

Instance PersistLaws_Ty : PersistLaws Ty.
Proof.
  constructor.
  intros * R.
Admitted.

Instance PersistLaws_Env : PersistLaws Env.
Proof.
  constructor.
  intros * R.
Admitted.

(* Lemma refine_T {AT A} (RA : Relation AT A) : *)
(*   forall (w : Ctx nat) (ass : Assignment w) bv v, *)
(*     ass = compose (Symbolic.refl w) ass -> *)
(*     RBox (RFree RA)%R w ass bv v -> *)
(*     RFree RA w ass (Symbolic.T _ bv) v. *)
(* Proof. intros ? ? ? ? ? ?. apply H0. apply H. Qed. *)

Lemma persist_refl : forall w1 V,
  Symbolic.persist w1 V w1 (Symbolic.refl w1) = V.
Proof. Admitted.

Lemma persist_cons :
  forall w ass k V v Γ γ,
    RTy w ass V v ->
    REnv w ass ((k, V) :: Γ)%list ((k, v) :: γ)%list.
Proof. Admitted.

Lemma Func_relates_func :
  forall (w : Ctx nat) (ass : Assignment w) D d C c,
    RTy w ass D d ->
    RTy w ass C c ->
    RTy w ass (Ty_func w D C) (ty_func d c).
Proof. Admitted.

Lemma lift_preserves_relatedness :
  forall w ass t,
    RTy w ass (Symbolic.world_index t w) t.
Proof. Admitted.

(* TODO: implicit args for refine_persist *)
(* TODO: some kind of Const relatedness ? See Katamaran, ask Steven *)

Lemma infers_are_related (e : expr) (w : Ctx nat) (ass : Assignment w)
  : (REnv -> (RFree RTy))%R w ass (Symbolic.infer e) (Shallow.infer_no_elab e).
Proof. Set Printing Depth 15.
  revert ass. revert w. induction e; intros w ass; cbn -[Symbolic.persist].
  - intros Γ γ RΓ. repeat constructor.
  - intros Γ γ RΓ. repeat constructor.
  - intros Γ γ RΓ. eapply Bind_relates_bind.
    apply IHe1. apply RΓ. clear IHe1.
    intros w1 ? ? ? ? ? ?. constructor. apply H0. constructor.
    unfold Symbolic.T. eapply Bind_relates_bind. cbn. apply IHe2.
    rewrite Symbolic.trans_refl. eapply refine_persist; eauto.
    intros ? ? ? ? ? ? ?. eapply Bind_relates_bind. cbn. apply IHe3.
    rewrite Symbolic.trans_refl. eapply refine_persist.
    eapply compose_trans. rewrite <- H1. rewrite <- H. apply RΓ.
    intros ? ? ? ? ? ? ?. eapply Bind_relates_bind. cbn. apply Assert_relates_assert; cbn.
    eapply refine_persist. apply H3. apply H2. eapply refine_persist.
    rewrite compose_refl. reflexivity. apply H4.
    intros ? ? ? ? ? ? ?. eapply Pure_relates_pure.
    eapply refine_persist. rewrite <- compose_trans. rewrite <- H5. apply H3. apply H2.
  - intros Γ γ RΓ. unfold REnv in RΓ. specialize (RΓ s).
    destruct (value s Γ), (value s γ); cbn in *;
      try contradiction; now constructor.
  - intros Γ γ RΓ. eapply Bind_relates_bind. apply Exists_relates_exists.
    intros ? ? ? ? ? ? ?. eapply Bind_relates_bind. apply IHe.
    apply persist_cons. apply H0.
    intros ? ? ? ? ? ? ?. constructor. subst. hnf.
    DepElim.hnf_eq. f_equal; auto.
    refine (refine_persist _ _ _ _ _ _ _ _ _ _ H0). reflexivity.
  - intros Γ γ RΓ. eapply Bind_relates_bind. apply IHe.
    apply persist_cons. apply lift_preserves_relatedness.
    intros ? ? ? ? ? ? ?. eapply Pure_relates_pure. apply Func_relates_func.
    eapply refine_persist. apply H. apply lift_preserves_relatedness. apply H0.
  - intros Γ γ RΓ. eapply Bind_relates_bind. apply Exists_relates_exists.
    intros ? ? ? ? ? ? ?. eapply Bind_relates_bind.
    eapply IHe2. eapply refine_persist. apply H. apply RΓ.
    intros ? ? ? ? ? ? ?. eapply Bind_relates_bind.
    eapply IHe1. eapply refine_persist. apply compose_trans. subst.
    apply RΓ.
    intros ? ? ? ? ? ? ?. eapply Bind_relates_bind.
    eapply Assert_relates_assert. apply H4.
    eapply refine_persist. apply H3. apply Func_relates_func. apply H2.
    eapply refine_persist. apply H1. apply H0.
    intros ? ? ? ? ? ? ?. apply Pure_relates_pure. eapply refine_persist.
    repeat rewrite <- compose_trans. rewrite <- H5. rewrite <- H3. apply H1.
    apply H0.
Qed.

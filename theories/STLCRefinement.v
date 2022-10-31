Require Import List.
Require Import Relation_Definitions.
Import ListNotations.
Require Import String.
From Em Require Import
     Context Environment.
From Em Require Import
     STLC.
From Em Require
  Prelude Unification.
Import ctx.notations.

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
  Definition RFree {A a} (RA : Relation A a) : Relation (Cstr A) (freeM a) :=
    fix R (w : Ctx nat) (ass : Assignment w) (F : Cstr A w) (f : freeM a) : Prop :=
      match F, f with
      | C_val _ _ V, ret_free _ v =>
          RA w ass V v
      | C_fls _ _, fail_free _ =>
          True
      | C_eqc _ _ T1 T2 K, bind_assert_free _ t1 t2 k =>
          RTy w ass T1 t1 /\
          RTy w ass T2 t2 /\
          R w ass K k
      | C_exi _ _ i K, bind_exists_free _ k =>
          forall (t : ty),
          R (w ▻ i) (env.snoc ass i t) K (k t)
      | _, _ =>
          False
      end.


  Check RFree.

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


  (*
  Check Symbolic.transient.
  Check @env.lookup.
  Check env.tabulate.

  Definition compose {w0 w1} (ω : Symbolic.Accessibility w0 w1) : Assignment w1 -> Assignment w0.
  refine (
    fun ass => env.tabulate _
  ). Proof.
    intros x xIn.
    apply (Symbolic.transient _ _ _ ω) in xIn.
    hnf in ass.
    Check env.lookup ass xIn.
    exact (env.lookup ass xIn).
    Show Proof.
    Abort. *)

  Definition compose {w0 w1} (ω : Symbolic.Accessibility w0 w1) : Assignment w1 -> Assignment w0 :=
    fun ass => env.tabulate (fun x xIn => env.lookup ass (Symbolic.transient w0 w1 x ω xIn)).

    (* Eval cbv [compose] in @compose. *)

  Lemma composing_refl : forall w ass,
      compose (Symbolic.refl w) ass = ass.
  Proof. unfold compose. cbn. induction ass; cbn; try congruence. Qed.

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

  (* Using our relation on functions, we can now prove that both the symbolic and the shallow return are related *)
  Lemma Pure_relates_pure {A a} (RA : Relation A a) :
    forall (w : Ctx nat) (ass : Assignment w),
      (RA -> (RFree RA))%R w ass (C_val A w) (ret_free a).
  Proof. unfold RArr. unfold RFree. auto. Qed.

  Lemma False_relates_false {A a} (RA : Relation A a) :
    forall (w : Ctx nat) (ass : Assignment w),
      RFree RA w ass (C_fls A w) (@fail_free a).
  Proof. unfold RArr. unfold RFree. auto. Qed.

  (*
  Check C_eqc.

  Check RUnit.
  Check Shallow.assert.
  Check Symbolic.assert.
   *)

  (* RTy -> RTy -> RFree RUnit *)
  Lemma Assert_relates_assert :
    forall (w : Ctx nat) (ass : Assignment w),
      (RTy -> RTy -> (RFree RUnit))%R w ass Symbolic.assert Shallow.assert.
  Proof. firstorder. Qed.

  (*
  Check Shallow.exists_ty.
  Check Symbolic.exists_Ty.
  *)

  Lemma Exists_relates_exists :
    forall (w : Ctx nat) (ass : Assignment w),
      (RFree RTy) w ass (Symbolic.exists_Ty w) Shallow.exists_ty.
  Proof. firstorder. Qed.

  (*
  Check Shallow.bind.
  Check Symbolic.bind.
  *)

  Lemma Bind_relates_bind {A B a b} (RA : Relation A a) (RB : Relation B b) :
    forall (w : Ctx nat) (ass : Assignment w),
      ((RFree RA) -> (RBox (RA -> RFree RB)) -> (RFree RB))%R w ass (@Symbolic.bind A B w) Shallow.bind.
  Proof. cbn. intros w ass. intros X. induction X; intros x rx; destruct x; cbn in rx; try contradiction. admit. Admitted.

  (* As an alternative to messing with fixpoint definitions for the RFree, perhaps it makes
     more sense to define RFree as an inductive relation. *)
  Section WithInductive.

    Inductive RFree' {A a} (RA : Relation A a) (w : Ctx nat)
                     (ass : Assignment w) : Cstr A w -> freeM a -> Prop :=
    | RPure : forall (V : A w) (v : a),
        RA w ass V v ->
        RFree' RA w ass (C_val _ _ V) (ret_free _ v)
    | RFalse :
        RFree' RA w ass (C_fls _ _) (fail_free _)
    | RAssert : forall T1 T2 t1 t2 Cont cont,
        RTy w ass T1 t1 ->
        RTy w ass T2 t2 ->
        RFree' RA w ass Cont cont ->
        RFree' RA w ass (C_eqc _ _ T1 T2 Cont) (bind_assert_free _ t1 t2 cont)
    | RExists : forall i Cont cont,
        (forall (t : ty),
         RFree' RA (w ▻ i) (env.snoc ass i t) Cont (cont t)) ->
        RFree' RA w ass (C_exi _ _ i Cont) (bind_exists_free _ cont).

    (* Binary parametricity translation *)

    Lemma Pure_relates_pure' {A a} (RA : Relation A a) :
    forall (w : Ctx nat) (ass : Assignment w),
        (RA -> (RFree' RA))%R w ass (C_val A w) (ret_free a).
    Proof.  constructor. assumption. Qed.

    Lemma False_relates_false' {A a} (RA : Relation A a) :
    forall (w : Ctx nat) (ass : Assignment w),
        RFree' RA w ass (C_fls A w) (@fail_free a).
    Proof.  constructor. Qed.

    Lemma Assert_relates_assert' :
      forall (w : Ctx nat) (ass : Assignment w),
        (RTy -> RTy -> (RFree' RUnit))%R w ass Symbolic.assert Shallow.assert.
      Proof. repeat (constructor; try assumption). Qed.

    Lemma Exists_relates_exists' :
      forall (w : Ctx nat) (ass : Assignment w),
        (RFree' RTy) w ass (Symbolic.exists_Ty w) Shallow.exists_ty.
    Proof. repeat constructor. Qed.

    Check Symbolic.bind.
    Check Shallow.bind.
    Lemma Bind_relates_bind' {A B a b} (RA : Relation A a) (RB : Relation B b) :
      forall (w : Ctx nat) (ass : Assignment w),
        ((RFree' RA) -> (RBox (RA -> RFree' RB)) -> (RFree' RB))%R w ass (@Symbolic.bind A B w) Shallow.bind.
    Proof. intros w ass ? ? ?.
           induction H;  cbn; intros F f HF; try constructor; try assumption.
           - unfold RBox in HF. unfold RArr in HF. apply HF.
             symmetry. apply composing_refl. apply H.
           - unfold RBox in IHRFree'. unfold RArr in IHRFree'. apply IHRFree'.
             unfold RBox in HF. unfold RArr in HF. apply HF.
           - intro. apply H0. unfold RBox.
             intros. apply HF. clear HF H0 H.
             inversion ω.
    Admitted.

  End WithInductive.

  (*
  Check Symbolic.infer.
  Check Shallow.infer.
  Check RTy.
  *)

  (* TODO: define REnv inductively *)
  Definition REnv : Relation Env env :=
    fun (w : Ctx nat) (ass : Assignment w) (Γ : Env w) (γ : env) => forall (pvar : string),
      match (value pvar Γ), (value pvar γ) with
      | Some T, Some t => RTy w ass T t
      | None, None => True
      | _, _ => False
      end.

  Axiom infer_no_elab : expr -> env -> freeM ty.

  (*
  Lemma infers_are_related (e : expr) (w : Ctx nat) (ass : Assignment w) : Prop.
    Check Symbolic.infer e.
    Check infer_no_elab e.
    Check RArr REnv (RFree' _).
    Check RArr REnv (RFree' RTy).
    Check (RArr REnv (RFree' RTy)) w ass.
    apply (RArr REnv (RFree' RTy) w ass).
    unfold Symbolic.Impl.
    Check Symbolic.infer.
    apply (Symbolic.infer e).
    Check infer_no_elab.
    apply (infer_no_elab e).
    Restart.
    apply (RArr REnv (RFree' RTy) w ass (Symbolic.infer e) (infer_no_elab e)).
  Abort.
  *)

  Lemma infers_are_related (e : expr) (w : Ctx nat) (ass : Assignment w)
    : (RArr REnv (RFree' RTy) w ass (Symbolic.infer e) (infer_no_elab e)).
  Proof.
  Admitted.


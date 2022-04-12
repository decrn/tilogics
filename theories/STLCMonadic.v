Require Import List.
Import ListNotations.
Require Import String.
From MasterThesis Require Import
     Context.
From MasterThesis Require Import
     STLC.
Import ctx.notations.

  (* Monadic type inference for STLC is expressed as a computation inside TypeCheckM.
     Note that STLC requires unification of type variables.
     These type variables are introduced by the exists_ty computation *)
  Class TypeCheckM (M : Type -> Type) : Type :=
    {
      ret    {A : Type} :   A -> M A ;
      bind {A B : Type} : M A -> (A -> M B) -> M B ;
      assert            :  ty -> ty         -> M unit ;
      fail   {A : Type} : M A ;
      exists_ty         : M ty ; (* NEW *)
    }.

  Inductive freeM (A : Type) : Type :=
    | bind_assert_free : ty -> ty -> freeM A -> freeM A
    | ret_free : A -> freeM A
    | fail_free : freeM A
    | bind_exists_free : (ty -> freeM A) -> freeM A.

  Notation "x <- ma ;; mb" :=
          (bind ma (fun x => mb))
            (at level 80, ma at next level, mb at level 200, right associativity).
  Notation "ma ;; mb" := (bind ma (fun _ => mb)) (at level 80, right associativity).
  Notation "' x <- ma ;; mb" :=
          (bind ma (fun x => mb))
            (at level 80, x pattern, ma at next level, mb at level 200, right associativity,
             format "' x  <-  ma  ;;  mb").

(* This section implements type inference for STLC
   using a shallow representation of constraints.
   Essentially, constraints are nothing more than propositions in Coq.
   This results in a fairly straightforward implementation,
   but one which is essentially unusable, because we cannot inspect
   the witnesses for these propositions. This is problematic,
   because these witnesses are the unified type variables
   which give the type and the elaboration of the term. *)
Section Shallow.

  Fixpoint freeM_bind [T1 T2 : Type] (m : freeM T1) (f : T1 -> freeM T2) : freeM T2 :=
    match m with
    | ret_free _ a => f a
    | fail_free _ => fail_free T2
    | bind_assert_free _ t1 t2 k =>
        bind_assert_free T2 t1 t2 (freeM_bind k f)
    | bind_exists_free _ tf =>
        bind_exists_free T2 (fun t : ty => freeM_bind (tf t) f)
    end.

  #[global] Instance TC_free : TypeCheckM freeM :=
    { bind         := freeM_bind ;
      ret T u      := ret_free T u ;
      assert t1 t2 := bind_assert_free _ t1 t2 (ret_free _ tt);
      fail T       := fail_free T;
      exists_ty    := bind_exists_free _ (fun t => ret_free _ t);
    }.

  Fixpoint infer {m} `{TypeCheckM m} (ctx : env) (expression : expr) : m (prod ty expr) :=
    match expression with
    | v_false => ret (ty_bool, expression)
    | v_true  => ret (ty_bool, expression)
    | e_if cnd coq alt =>
        '(t_cnd, e_cnd) <- infer ctx cnd ;;
        '(t_coq, e_coq) <- infer ctx coq ;;
        '(t_alt, e_alt) <- infer ctx alt ;;
        (assert t_cnd ty_bool) ;;
        (assert t_coq t_alt)   ;;
        ret (t_coq, e_if e_cnd e_coq e_alt)
    | e_var var =>
        match (value var ctx) with
        | Some t_var => ret (t_var, expression)
        | None => fail
        end
    | e_app e1 e2 =>
        '(t_e1, e_e1) <- infer ctx e1 ;;
        '(t_e2, e_e2) <- infer ctx e2 ;;
        t_exists_ty <- exists_ty ;;
        (assert t_e1 (ty_func t_e2 t_exists_ty)) ;;
        ret (t_exists_ty, e_app e_e1 e_e2)
    | e_absu var e =>
        t_var <- exists_ty ;;
        '(t_e, e_e) <- infer (cons (var, t_var) ctx) e ;;
        ret (ty_func t_var t_e, e_abst var t_var e_e)
    | e_abst var t_var e =>
        '(t_e, e_e) <- infer (cons (var, t_var) ctx) e ;;
        ret (ty_func t_var t_e, e_abst var t_var e_e)
    end.

  Compute (infer nil (e_app (e_abst "x" ty_bool (e_var "x")) v_true)).
  Compute (infer nil (e_app (e_absu "x" (e_var "x")) v_true)).

  Definition K1 := (e_absu "k1" (e_absu "l" (e_var "k1"))).
  Definition K2 := (e_absu "k2" (e_absu "l" (e_var "k2"))).
  Definition I := (e_absu "i" (e_var "i")).

  Definition KKI := (e_app K1 (e_app K2 I)).
  Compute (infer nil KKI).

  Fixpoint wlp_freeM [A : Type] (m : freeM A) (Q: A -> Prop) : Prop :=
    match m with
    | ret_free _ a => Q a
    | bind_assert_free _ t1 t2 k => t1 = t2 ->
        wlp_freeM k Q
    | fail_free _ => True
    | bind_exists_free _ tf => forall t : ty, wlp_freeM (tf t) Q
    end.

  Fixpoint wp_freeM [A : Type] (m : freeM A) (Q: A -> Prop) :=
    match m with
    | ret_free _ a => Q a
    | bind_assert_free _ t1 t2 k => t1 = t2 /\
        wp_freeM k Q
    | fail_free _ => False
    | bind_exists_free _ tf => exists t : ty, wp_freeM (tf t) Q
    end.

  Lemma wlp_ty_eqb : forall (t1 t2 : ty) (Q : unit -> Prop),
    wlp_freeM (assert t1 t2) Q <-> (t1 = t2 -> Q tt).
  Proof. destruct t1, t2; cbn; intuition discriminate.  Qed.

  Lemma wlp_exists_type : forall (Q: ty -> Prop),
    wlp_freeM (exists_ty) Q <-> (forall t : ty, Q t).
  Proof.  intuition.  Qed.

  Lemma wlp_bind : forall {A B : Type} (m1 : freeM A) (m2 : A -> freeM B) (Q : B -> Prop),
    wlp_freeM (freeM_bind m1 m2) Q <-> wlp_freeM m1 (fun o => wlp_freeM (m2 o) Q).
  Proof.  split; induction m1; cbn; intuition; destruct H0; exists x; intuition.  Qed.

  Lemma wlp_ret : forall {A : Type} (a : A) (Q : A -> Prop),
    wlp_freeM (ret a) Q <-> Q a.
  Proof.  intuition.  Qed.

  Lemma wlp_fail : forall {A : Type} (Q : A -> Prop),
    wlp_freeM (fail) Q <-> True.
  Proof.  intuition.  Qed.

  Lemma wlp_monotone : forall {O : Set} (P Q : O -> Prop) (m : freeM O),
    (forall o : O, P o -> Q o) -> wlp_freeM m P -> wlp_freeM m Q.
  Proof.  intros. induction m; cbn; auto.  Qed.

  Lemma wp_ty_eqb : forall (t1 t2 : ty) (Q : unit -> Prop),
    wp_freeM (assert t1 t2) Q <-> t1 = t2 /\ Q tt.
  Proof.
      split; intros.
      - inversion H. cbn in H1. auto.
      - cbn. apply H.
  Qed.

  Lemma wp_exists_type : forall (Q: ty -> Prop),
    wp_freeM (exists_ty) Q <-> (exists t : ty, Q t).
  Proof.  intuition.  Qed.

  Lemma wp_bind : forall {A B : Type} (m1 : freeM A) (m2 : A -> freeM B) (Q : B -> Prop),
    wp_freeM (freeM_bind m1 m2) Q <-> wp_freeM m1 (fun o => wp_freeM (m2 o) Q).
  Proof.  split; induction m1; cbn; intuition; destruct H0; exists x; intuition.  Qed.

  Lemma wp_ret : forall {A : Type} (a : A) (Q : A -> Prop),
    wp_freeM (ret a) Q <-> Q a.
  Proof.  intuition.  Qed.

  Lemma wp_fail : forall {A : Type} (Q : A -> Prop),
    wp_freeM (fail) Q <-> False.
  Proof.  cbn. intuition.  Qed.

  Lemma wp_monotone : forall {O : Set} (P Q : O -> Prop) (m : freeM O),
    (forall o : O, P o -> Q o) -> wp_freeM m P -> wp_freeM m Q.
  Proof.
      intros. induction m; cbn; auto;
      inversion H0; intuition.
      exists x. apply H1. apply H2.
  Qed.


  Lemma infer_sound : forall (G : env) (e : expr),
   wlp_freeM (infer G e) (fun '(t,ee) => G |-- e ; t ~> ee).
  Proof.
    intros. generalize dependent G. induction e; cbn [infer]; intro;
    repeat (rewrite ?wlp_exists_type, ?wlp_bind, ?wlp_ty_eqb, ?wlp_ret, ?wlp_fail; try destruct o;
        try match goal with
        | IHe : forall G, wlp_freeM (infer G ?e) _ |- wlp_freeM (infer ?g ?e) _ =>
            specialize (IHe g); revert IHe; apply wlp_monotone; intros
        | |- tpb _ _ _ _ =>
            constructor
        | |- ?x = ?y -> _ =>
            intro; subst
        | |- wlp_freeM (match ?t with _ => _ end) _ =>
            destruct t eqn:?
        | |- forall t, _ =>
            intro
        | H : ?g |-- ?e ; ?t ~> ?ee |- ?g' |-- e_app ?e1 ?e2 ; ?t' ~> e_app ?e1' ?e2' =>
            apply (tpb_app _ _ _ _ _ t0 _)
        end; try reflexivity; try assumption).
  Qed.

  Lemma infer_complete : forall  (G : env) (e ee : expr) (t : ty),
    (G |-- e ; t ~> ee) -> wp_freeM (infer G e) (fun '(t',ee')  => t = t' /\ ee = ee').
  Proof.
    intros. induction H; cbn;
    repeat (rewrite ?wp_bind, ?wp_ty_eqb, ?wp_ret, ?wp_fail; try destruct o; cbn; try rewrite H;
        try match goal with
        | IH : wp_freeM (infer ?g ?e) _ |- wp_freeM (infer ?g ?e) _ =>
            revert IH; apply wp_monotone; intros; subst
        | |- ?x = ?y /\ _ =>
            split
        | H : ?x = ?y /\ _ |- _ =>
            destruct H; subst
        end; try reflexivity).
        - exists vt. apply wp_bind. revert IHtpb. apply wp_monotone. intro. destruct o. intro. destruct H0. apply wp_ret. subst. intuition.
        - exists t1. auto.
  Qed.

  Fixpoint gensem (ctx : list (string * ty)) (expression : expr) (type : ty) : Prop :=
    match expression with
    | v_true  => type = ty_bool
    | v_false => type = ty_bool
    | e_if cnd coq alt =>
        gensem ctx cnd ty_bool /\
        gensem ctx coq type    /\
        gensem ctx alt type
    | e_var var =>
        match (value var ctx) with
        | None => False
        | Some t => t = type
        end
    | e_app e1 e2 =>
        exists t2,
        gensem ctx e1 (ty_func t2 type) /\
        gensem ctx e2 t2
    | e_absu var e =>
        exists t_e t_var,
        gensem ((var, t_var) :: ctx) e t_e /\
        type = (ty_func t_var t_e)
    | e_abst var t_var e =>
        exists t_e,
        gensem ((var, t_var) :: ctx) e t_e /\
        type = (ty_func t_var t_e)
    end.

  Lemma ex_gensem1 :
    gensem nil (e_app (e_absu "x" (e_var "x")) v_false) ty_bool.
  Proof.
    compute. repeat eexists.
  Qed.

  Example ex_gensem2 :
  gensem nil (e_app (e_absu "x" (v_true)) (e_absu "x" (e_var "x"))) ty_bool.
  Proof.
    compute. repeat eexists.
    Unshelve. apply ty_bool.
  Qed.

End Shallow.

(* TODO: define infer for the other cases
   TODO: Refinement proof of deep embedding
   TODO: Prenex form of constraints *)

Section Symbolic.

  (* Adapted from Katamaran: Symbolic/Worlds.v *)

  Inductive Accessibility (Σ₁ : Ctx nat) : Ctx nat -> Type :=
    | refl    : Accessibility Σ₁ Σ₁
    | fresh α : forall Σ₂, Accessibility Σ₁ Σ₂ -> Accessibility Σ₁ (Σ₂ ▻ α).

  (* ⊢ A *)
  Definition Valid (A : Ctx nat -> Type) := forall Σ, A Σ.

  (* A → B *)
  Definition Impl (A B : Ctx nat -> Type) : Ctx nat -> Type :=
    fun Σ => (A Σ) -> (B Σ).

  (* □ A *)
  Definition Box A (Σ : Ctx nat) := forall Σ', Accessibility Σ Σ' -> A Σ'.

  (* _[_] *)
  Definition transient : forall (Σ Σ' : Ctx nat) (i : nat),
      Accessibility Σ Σ' ->
      i ∈ Σ ->
      i ∈ Σ'.
  Proof.
    intros. induction H.
    - apply H0.
    - Search "x ∈ x". apply ctx.in_succ. apply IHAccessibility.
  Qed.

  Fixpoint Persistent {Σ₁ Σ₂} (t : Ty Σ₁) {w : Accessibility Σ₁ Σ₂} {struct t} : Ty Σ₂.
  Proof. cbv in *. intros. destruct t eqn:?.
    - apply Ty_bool.
    - constructor 2;
      eapply Persistent. apply t0_1. apply w. apply t0_2. apply w.
    - constructor 3 with i. apply transient with Σ₁. apply w. apply i0.
  Show Proof.
  Defined.

  Definition Persistent' : Valid (Impl Ty (Box Ty)).
  Proof. cbv in *. intros. induction H.
    - apply Ty_bool.
    - constructor 2. apply IHTy1. apply IHTy2.
    - constructor 3 with i. apply transient with Σ. apply H0. apply i0.
  Show Proof.
  Defined.

  (* Not a valid fixp because e is non-decreasing *)
  (*
  Fixpoint Persistent_Env {S S' : Ctx nat} (e : Env S) {w : Accessibility S S'} {struct e} : Env S'.
  Proof. cbv in *. intros. induction w.
    - apply e.
    - apply (fresh _ α) in w. eapply Persistent_Env. apply e. apply w.
      Show Proof.
      Defined. *)

  (* This proof looks dodgy *)
  Definition Persistent_Env : Valid (Impl Env (Box Env)).
  Proof. cbv in *. intros. induction H.
    - apply nil.
    - apply IHlist.
  Show Proof.
  Defined.

  Definition T {A} := fun (Σ : Ctx nat) (a : Box A Σ) => a Σ (refl Σ).

  Check T.

  Definition trans {Σ₁ Σ₂ Σ₃} (w12 : Accessibility Σ₁ Σ₂) (w23 : Accessibility Σ₂ Σ₃) : Accessibility Σ₁ Σ₃.
  Proof. induction w23. apply w12. apply fresh. apply IHw23. Defined.

  Definition _4 {A} : Valid (Impl (Box A) (Box (Box A))).
  Proof. cbv in *. intros.  apply X. eapply trans. apply H. apply H0. Show Proof. Defined.

  Check _4.

  Print Scopes.

  Fixpoint bind' [A B] {Σ} (m : Cstr A Σ) (f : Box (Impl A (Cstr B)) Σ) {struct m} : Cstr B Σ.
  refine (
    match m with
    | C_eqc _ _ t1 t2 C1 => _
    | C_val _ _ v => _
    | C_fls _ _ => C_fls _ _ (* we just fail *)
    | C_exi _ _ i C => _
    end).
  Proof.
    - apply C_eqc. apply t1. apply t2. eapply bind'.
      + apply C1.
      + apply f.
    - apply T in f. unfold Impl in f. apply f. apply v.
    - eapply C_exi. eapply bind'.
      + apply C.
      + apply _4 in f. cbv in *. intros. apply (f _ (fresh _ _ _ (refl Σ)) _ H X).
  Show Proof.
  Defined.

  Eval cbv [bind] in @bind'.

      Local Notation "[ ω ] x <- ma ;; mb" :=
        (bind' ma (fun _ ω x => mb))
          (at level 80, x at next level,
            ma at next level, mb at level 200,
            right associativity).

  Definition Unit (Σ : Ctx nat) := unit.

  Check Unit.

  Definition assert' {Σ} t1 t2 := C_eqc Unit Σ t1 t2 (C_val Unit Σ tt).

  Check Persistent_Env.

  Local Notation "<[ G ~ w ]>" := ((Persistent_Env _ G) _ w).

  Local Notation "w1 .> w2" := (trans w1 w2) (at level 80).

  Local Notation "<{ v ~ w }>" := (@Persistent _ _ v w).

  Fixpoint convert (t : ty) (Σ : Ctx nat) : Ty Σ :=
    match t with
    | ty_bool => Ty_bool Σ
    | ty_func do co => Ty_func Σ (convert do Σ) (convert co Σ)
    end.

  Fixpoint infer'' {Σ : Ctx nat} (Γ : Env Σ) (expression : expr) {struct expression} : Cstr Ty Σ.
  Proof.
  refine (
    match expression with
    | v_true => C_val Ty Σ (Ty_bool Σ)
    | v_false => C_val Ty Σ (Ty_bool Σ)
    | e_if cnd coq alt =>
        [ ω₁ ] t_cnd <- infer'' _ Γ cnd ;;
        [ ω₂ ] _     <- assert' t_cnd (Ty_bool _) ;;
        [ ω₃ ] t_coq <- infer'' _ <[ <[ Γ ~ ω₁ ]> ~ ω₂ ]> coq ;;
        [ ω₄ ] t_alt <- infer'' _ <[ <[ Γ ~ ω₁ ]> ~ ω₂ .> ω₃ ]> alt ;;
        [ ω₅ ] _     <- assert' <{ t_coq ~ ω₄ }>  <{ t_alt ~ (refl _) }> ;;
           C_val Ty _ <{ t_coq ~ ω₄ .> ω₅ }>
    | e_var var =>
        match (value var Γ) with
        | Some t_var => C_val Ty _ t_var
        | None => C_fls Ty Σ
        end
    | e_app f a =>
        [ w1 ] t_co <- _ ;; (* TODO: need an existential here, but what value for i? *)
        [ w2 ] t_do <- infer'' _ <[ Γ ~ w1 ]> a ;;
        [ w3 ] t_fn <- infer'' _ <[ Γ ~ w1 .> w2 ]> f ;;
        [ w4 ] _    <- assert' t_fn <{ (Ty_func _ t_do <{ t_co ~ w2 }> ) ~ w3 }> ;;
           C_val Ty _ <{ t_co ~ w2 .> w3 .> w4 }>
    | e_abst var t_var e =>
        let t_var' := (convert t_var Σ) in
        [ w1 ] t_e <- infer'' _ ((var, t_var') :: Γ) e ;;
          C_val Ty _ (Ty_func _ <{ t_var' ~ w1 }> t_e)
    | e_absu var e =>
        [ w1 ] t_var <- _ ;;
        [ w2 ] t_e <- infer'' _ <[ ((var, t_var) :: Γ) ~ w1 ]> e ;;
          C_val Ty _ (Ty_func _ <{ t_var ~ w1 .> w2 }> t_e)
    end).
    - eapply C_exi. admit.
    - eapply C_exi. admit.
  Admitted.

  Compute infer'' nil (e_if v_true v_true v_false).
  Compute C_eqc Ty ε (Ty_bool ε) (Ty_bool ε) (C_val Ty ε (Ty_bool ε)).

End Symbolic.


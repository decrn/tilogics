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
Module Shallow.

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

  Fixpoint infer {m} `{TypeCheckM m} (expression : expr) (ctx : env) : m (prod ty expr) :=
    match expression with
    | v_false => ret (ty_bool, expression)
    | v_true  => ret (ty_bool, expression)
    | e_if cnd coq alt =>
        '(Tcnd, Ecnd) <- infer cnd ctx ;;
        '(Tcoq, Ecoq) <- infer coq ctx ;;
        '(Talt, Ealt) <- infer alt ctx ;;
        (assert Tcnd ty_bool) ;;
        (assert Tcoq Talt)   ;;
        ret (Tcoq, e_if Ecnd Ecoq Ealt)
    | e_var var =>
        match (value var ctx) with
        | Some Tvar => ret (Tvar, expression)
        | None => fail
        end
    | e_app e1 e2 =>
        '(T1, E1) <- infer e1 ctx ;;
        '(T2, E2) <- infer e2 ctx ;;
        T0 <- exists_ty           ;;
        assert T1 (ty_func T2 T0) ;;
        ret (T0, e_app E1 E2)
    | e_absu var e =>
        Tvar <- exists_ty ;;
        '(T, E) <- infer e (cons (var, Tvar) ctx) ;;
        ret (ty_func Tvar T, e_abst var Tvar E)
    | e_abst var Tvar e =>
        '(T, E) <- infer e (cons (var, Tvar) ctx) ;;
        ret (ty_func Tvar T, e_abst var Tvar E)
    end.

  Compute (infer (e_app (e_abst "x" ty_bool (e_var "x")) v_true) nil).
  Compute (infer (e_app (e_absu "x" (e_var "x")) v_true) nil).

  Definition K1 := (e_absu "k1" (e_absu "l" (e_var "k1"))).
  Definition K2 := (e_absu "k2" (e_absu "l" (e_var "k2"))).
  Definition I := (e_absu "i" (e_var "i")).

  Definition KKI := (e_app K1 (e_app K2 I)).
  Compute (infer KKI nil).

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

  (* (λx.x) (λy.y) *)
  Lemma test : forall (τ : ty) POST,
    wp_freeM (infer
    (e_app (e_absu "x" (e_var "x")) (e_absu "y" (e_var "y"))) nil)
      (POST).
  Proof.
    compute.
    eexists.
    eexists.
    eexists.
    admit.
  Abort.

  Print ex. (* Prop -> Prop *)
  Print sig. (* Prop -> Type *)
  Print sigT. (* Type -> Type *)
  Check eq.
  Check prod.

  Unset Printing Universes.
  Check Prop.
  Check Set.
  Set Printing Universes.
  Check Prop.
  Check Set.

  Check forall (a : Prop), a. (* impredicativity of Prop *)
  Check forall (a : Set), a.


  (* WP but in Type instead of Prop *)
  Fixpoint gen [A : Type] (m : freeM A) : Type :=
    match m with
    | ret_free _ a => unit (* equiv. True in Prop *)
    | bind_assert_free _ t1 t2 k => (t1 = t2) * gen k
    | fail_free _ => Empty_set (* equiv. False in Prop *)
    | bind_exists_free _ tf => { τ : ty & gen (tf τ)}
    end%type.

  (* Generates an A from a computation m and its proof *)
  Fixpoint extract [A : Type] [m : freeM A] {struct m} : gen m -> A.
  Proof.
    destruct m; intros P; cbn in P.
    - destruct P. apply (extract _ _ g).
    - apply a.
    - contradiction P.
    - destruct P. apply (extract _ _ g).
  Defined.

  Print extract.

  Eval compute [extract] in extract. (* normalised *)

  Lemma test : forall (τ : ty),
    gen (infer
    (e_app (e_absu "x" (e_var "x")) (e_absu "y" (e_var "y"))) nil).
  Proof.
    repeat eexists; eauto.
  Unshelve.
    exact τ.
  Qed.

  Eval compute in fun t => extract (test t).

  Lemma infer_sound : forall (G : env) (e : expr),
   wlp_freeM (infer e G) (fun '(t,ee) => G |-- e ; t ~> ee).
  Proof.
    intros. generalize dependent G. induction e; cbn [infer]; intro;
    repeat (rewrite ?wlp_exists_type, ?wlp_bind, ?wlp_ty_eqb, ?wlp_ret, ?wlp_fail; try destruct o;
        try match goal with
        | IHe : forall G, wlp_freeM (infer ?e G) _ |- wlp_freeM (infer ?e ?g) _ =>
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
        end; try firstorder).
  Qed.

  Lemma infer_complete : forall  (G : env) (e ee : expr) (t : ty),
    (G |-- e ; t ~> ee) -> wp_freeM (infer e G) (fun '(t',ee')  => t = t' /\ ee = ee').
  Proof.
    intros. induction H; cbn;
    repeat (rewrite ?wp_bind, ?wp_ty_eqb, ?wp_ret, ?wp_fail; try destruct o; cbn; try rewrite H;
        try match goal with
        | IH : wp_freeM (infer ?e ?g) _ |- wp_freeM (infer ?e ?g) _ =>
            revert IH; apply wp_monotone; intros; subst
        | |- ?x = ?y /\ _ =>
            split
        | H : ?x = ?y /\ _ |- _ =>
            destruct H; subst
        end; try reflexivity).
        - exists vt. apply wp_bind. revert IHtpb. apply wp_monotone. intro. destruct o. intro. firstorder; subst; reflexivity.
        - exists t1. firstorder.
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

Module Symbolic.

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

  Lemma access_any_world_from_empty : forall Σ, Accessibility ctx.nil Σ.
  Proof. intros. induction Σ. apply refl. apply fresh. apply IHΣ. Defined.

  (* _[_] *)
  Definition transient : forall (Σ Σ' : Ctx nat) (i : nat),
      Accessibility Σ Σ' ->
      i ∈ Σ ->
      i ∈ Σ'.
  Proof.
    intros. induction H.
    - apply H0.
    - Search "x ∈ y". apply ctx.in_succ. apply IHAccessibility.
  Defined.

  Eval cbv [transient Accessibility_rec Accessibility_rect] in @transient.

  Check Ty.
  Check Env.
  Check Cstr.


  Class Persistent (A : Ctx nat -> Type) : Type :=
  { persist : Valid (Impl A (Box A)) }.

  #[refine] Instance Persistent_Ty : Persistent Ty := { persist := _ }.
  Proof. cbv in *. intros. induction H.
    - constructor 1.
    - constructor 2. apply IHTy1. apply IHTy2.
    - constructor 3 with i. apply transient with Σ. apply H0. apply i0.
  Show Proof.
  Defined.

  #[refine] Instance Persistent_Env : Persistent Env := { persist := _ }.
  Proof. cbv in *. intro Σ. refine (fix F E := _). intros. destruct E.
  - apply nil.
  - destruct p. apply cons. apply pair. apply s. apply persist in t. apply t. apply H.
    apply F. apply E. apply H.
    Show Proof. (* Something <>< *)
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

  Local Notation "w1 .> w2" := (trans w1 w2) (at level 80).

  Local Notation "<{ A ~ w }>" := (persist _ A _ w).

  Check exists_ty.

  Check Cstr _ _.
  Print freeM.

  Check Cstr Ty _.

  Print ctx.In.
  (* Valid *)
  Definition exists_Ty : forall GS, Cstr Ty GS :=
    fun GS => let i := ctx.length GS in C_exi Ty GS i (C_val _ _ (Ty_hole _ i ctx.in_zero)).

  Check exists_Ty.

  Fixpoint convert (t : ty) (Σ : Ctx nat) : Ty Σ :=
    match t with
    | ty_bool => Ty_bool Σ
    | ty_func do co => Ty_func Σ (convert do Σ) (convert co Σ)
    end.

  Fixpoint infer'' (expression : expr) {Σ : Ctx nat} (Γ : Env Σ) {struct expression} : Cstr Ty Σ :=
    match expression with
    | v_true => C_val Ty Σ (Ty_bool Σ)
    | v_false => C_val Ty Σ (Ty_bool Σ)
    | e_if cnd coq alt =>
        [ ω₁ ] t_cnd <- infer'' cnd Γ ;;
        [ ω₂ ] _     <- assert' t_cnd (Ty_bool _) ;;
        [ ω₃ ] t_coq <- infer'' coq <{ Γ ~ ω₁ .> ω₂ }> ;;
        [ ω₄ ] t_alt <- infer'' alt <{ Γ ~ ω₁ .> ω₂ .> ω₃ }> ;;
        [ ω₅ ] _     <- assert' <{ t_coq ~ ω₄ }>  <{ t_alt ~ (refl _) }> ;;
           C_val Ty _ <{ t_coq ~ ω₄ .> ω₅ }>
    | e_var var =>
        match (value var Γ) with
        | Some t_var => C_val Ty _ t_var
        | None => C_fls Ty Σ
        end
    | e_app f a =>
        [ w1 ] t_co <- exists_Ty Σ ;;
        [ w2 ] t_do <- infer'' a <{ Γ ~ w1 }> ;;
        [ w3 ] t_fn <- infer'' f <{ Γ ~ w1 .> w2 }> ;;
        [ w4 ] _    <- assert' t_fn <{ (Ty_func _ t_do <{ t_co ~ w2 }> ) ~ w3 }> ;;
           C_val Ty _ <{ t_co ~ w2 .> w3 .> w4 }>
    | e_abst var t_var e =>
        let t_var' := (convert t_var Σ) in (* t_var lives in ty, not in (Ty w) *)
        [ w1 ] t_e <- infer'' e ((var, t_var') :: Γ) ;;
          C_val Ty _ (Ty_func _ <{ t_var' ~ w1 }> t_e)
    | e_absu var e =>
        [ w1 ] t_var <- exists_Ty Σ ;;
        [ w2 ] t_e <- infer'' e ((var, t_var) :: <{ Γ ~ w1 }>) ;;
          C_val Ty _ (Ty_func _ <{ t_var ~ w2 }> t_e)
    end.

  (* Submitting a generated constraint to the unifier requires
     converting the constraint into prenex normal form.
     We could do this while generating the constraints,
     but instead we choose to do it afterwards.
     See theories/STLC.v for the datatype *)
  Section PrenexNormalForm.

    (* Insert a given type equality in front of the first non-quantifier.
       This essentially only requires finding the first non quantifier,
       and then weakening the world in which the type equality lives to
       match the current world *)
    Fixpoint insert_tyeq [A] {Σ} (t1 t2 : Ty Σ) (c : Prenex A Σ) : Prenex A Σ :=
      match c with
      | P_Constraint _ _ l => P_Constraint _ _ (C_Equal _ _ t1 t2 l)
      | P_Exist _ _ i cont =>
          P_Exist _ _ i (insert_tyeq <{ t1 ~ (fresh _ i _ (refl _)) }>
                                     <{ t2 ~ (fresh _ i _ (refl _)) }>
                                     cont)
      end.

    (* Turns a given constraint into prenex normal form *)
    Fixpoint pnf [A] {Σ} (c : Cstr A Σ) : Prenex A Σ :=
      match c with
      | C_val _ _ val => P_Constraint _ _ (L_Value _ _ val)
      | C_fls _ _ => P_Constraint _ _ (L_False _ _)
      | C_eqc _ _ t1 t2 cont =>
          insert_tyeq t1 t2 (pnf cont)
      | C_exi _ _ i cont => P_Exist _ _ i (pnf cont)
      end.

    Compute infer'' (e_if v_true (e_absu "x" (e_var "x")) (e_absu "x" (e_var "x"))) nil.
    Compute pnf (infer'' (e_if v_true (e_absu "x" (e_var "x")) (e_absu "x" (e_var "x"))) nil).

    Definition Prenex' A Σ : Type :=
      option { Σ' : Ctx nat & Accessibility Σ Σ' * list (Ty Σ' * Ty Σ') * A Σ' }%type.

    Check Prenex'.

    Fixpoint pnf_conv [A] {Σ} (cstr : Cstr A Σ) : Prenex' A Σ.
    Admitted.

    Fixpoint prenex_convert [A] {Σ} (pnf : Prenex A Σ) : Prenex' A Σ.
    Proof.
      refine(
      match pnf with
      | P_Constraint _ _ c =>
          match c with
          | L_Value _ _ v =>
              _
          | L_False _ _ =>
              None
          | C_Equal _ _ σ τ k =>
              _
          end
      | P_Exist _ _ i c =>
          let t := prenex_convert _ _ c in
          _
      end).
      - (* L_Value *)
        apply Some. exists Σ. repeat apply pair.
        apply refl.  apply nil.  apply v.
      - (* C_Equal *)
        apply Some. exists Σ. repeat apply pair.
        apply refl. eapply cons. apply (pair σ τ).
        admit. admit.
      - (* P_Exist *)
        destruct t. destruct s. destruct p. destruct p.
        apply Some. exists (Σ ▻ i). repeat apply pair.
        Search refl.
        apply fresh. apply refl. admit. admit. admit. (* apply Box in l. apply nil. admit. *)
    Show Proof.
    Admitted.

    Fixpoint ground {Σ} : Unification.Assignment Σ :=
      match Σ with
      | ctx.nil => env.nil
      | Γ ▻ b   => env.snoc ground b ty_bool
      end.

    Definition solve_constraints {AT AV Σ}
      (Aassign : forall Σ, Unification.Assignment Σ -> AT Σ -> AV) :
      Prenex' AT Σ -> option AV.
    Proof.
      intros pn.
      apply (Prelude.option.bind pn).
      intros (Σ' & (_ & cs) & a).
      apply (Prelude.option.bind (Unification.Variant1.solve cs)).
      intros (Σrest & ζ & _).
      apply Some.
      revert a. apply Aassign.
      apply (Unification.compose ζ).
      apply ground.
    Defined.

    Definition runTI : expr -> option ty.
    Proof.
      intros e.
      refine (@solve_constraints Ty ty [] _ _).
      intros ? ass T.
      apply (Unification.applyassign T ass).
      revert e.
    Admitted.

  End PrenexNormalForm.

End Symbolic.

Section Refinement.

  (* The refinement proof, relating the deeply-embedded or symbolic `infer` to the shallowly-embedded `infer` is accomplished
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

  Check Relation.

  (* To start, we define a relation between deeply-embedded object-language types `Ty`
     and shallowly-embedded object-language types `ty` *)
  (* These two are related if, given a world and an assignment (or valuation) from unification variables
     in the world to concrete object language types, applying the assignment to the `Ty` is equal to `ty` *)
  Definition RTy : Relation Ty ty :=
    fun (w : Ctx nat) (ass : Assignment w) (T : Ty w) (t : ty) => Unification.applyassign T ass = t.

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
      | C_eqc _ _ t1 t2 cont, bind_assert_free _ t1' t2' cont' =>
          RTy w ass t1 t1' /\
          RTy w ass t2 t2' /\
          R w ass cont cont'
      | C_exi _ _ i cont, bind_exists_free _ tf =>
          forall (t : ty),
          R (w ▻ i) (env.snoc ass i t) cont (tf t)
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
    Defined.

    Eval cbv [compose] in @compose.

  Definition RBox {A a} (RA : Relation A a) : Relation (Symbolic.Box A) a :=
    fun (w : Ctx nat) (ass : Assignment w) (x : Symbolic.Box A w) (y : a) =>
      forall (w' : Ctx nat) (ω : Symbolic.Accessibility w w') (ass' : Assignment w'),
        ass = compose ω ass' ->
        RA _ ass' (x w' ω) y.

  Check RBox.

  (* For functions/impl: related inputs go to related outputs *)
  Definition RArr {A a B b} (RA : Relation A a) (RB : Relation B b) : Relation (Symbolic.Impl A B) (a -> b) :=
    fun w ass fS fs => forall (V : A w) (v : a),
      RA w ass V v -> RB w ass (fS V) (fs v).

  Check Symbolic.Unit.
  Definition RUnit : Relation Symbolic.Unit unit :=
    fun w ass _ _ => True.

  Declare Scope rel_scope.
  Delimit Scope rel_scope with R.
  Notation "A -> B" := (RArr A B) : rel_scope.

  (* Using our relation on functions, we can now prove that both the symbolic and the shallow return are related *)
  Lemma Pure_relates_pure {A a} (RA : Relation A a) :
    forall (w : Ctx nat) (ass : Assignment w),
      (RA -> (RFree RA))%R w ass (C_val A w) (ret_free a).
  Proof.
    unfold RArr. unfold RFree. auto.
  Qed.

  Lemma False_relates_false {A a} (RA : Relation A a) :
    forall (w : Ctx nat) (ass : Assignment w),
      RFree RA w ass (C_fls A w) (@fail_free a).
  Proof.
    unfold RArr. unfold RFree. auto.
  Qed.

  Check C_eqc.

  Check RUnit.
  Check assert.
  Check Symbolic.assert'.

  (* RTy -> RTy -> RFree RUnit *)
  Lemma Assert_relates_assert :
    forall (w : Ctx nat) (ass : Assignment w),
      (RTy -> RTy -> (RFree RUnit))%R w ass Symbolic.assert' assert.
  Proof. firstorder. Qed.

  Check exists_ty.
  Check Symbolic.exists_Ty.

  Lemma Exists_relates_exists :
    forall (w : Ctx nat) (ass : Assignment w),
      (RFree RTy) w ass (Symbolic.exists_Ty w) exists_ty.
  Proof. firstorder. Qed.

  Check bind.
  Check Symbolic.bind'.

  Lemma Bind_relates_bind {A B a b} (RA : Relation A a) (RB : Relation B b) :
    forall (w : Ctx nat) (ass : Assignment w),
      ((RFree RA) -> (RBox (RA -> RFree RB)) -> (RFree RB))%R w ass (@Symbolic.bind' A B w) bind.
  Proof. cbn. intros w ass. intros X. induction X; intros x rx; destruct x; cbn in rx; try contradiction. admit. Admitted.

  (* As an alternative to messing with fixpoint definitions for the RFree, perhaps it makes
     more sense to define it as an inductive proposition. *)
  Section WithInductive.

  Inductive RFree' {A a} (RA : Relation A a) : Relation (Cstr A) (freeM a) :=
  | RPure : forall w ass V v,
      RFree' RA w ass (C_val _ _ V) (ret_free _ v)
  | RFalse : forall w ass,
      RFree' RA w ass (C_fls _ _) (fail_free _)
  | RAssert : forall w ass T1 T2 t1 t2 Cont cont,
      RTy w ass T1 t1 ->
      RTy w ass T2 t2 ->
      RFree' RA w ass (C_eqc _ _ T1 T2 Cont) (bind_assert_free _ t1 t2 cont)
  | RExists : forall w ass i Cont cont t,
      RFree' RA (w ▻ i) (env.snoc ass i t) Cont (cont t).

    (* Binary parametricity translation *)

  Lemma Pure_relates_pure' {A a} (RA : Relation A a) :
  forall (w : Ctx nat) (ass : Assignment w),
      (RA -> (RFree' RA))%R w ass (C_val A w) (ret_free a).
  Proof.  constructor. Qed.

  Lemma False_relates_false' {A a} (RA : Relation A a) :
  forall (w : Ctx nat) (ass : Assignment w),
      RFree' RA w ass (C_fls A w) (@fail_free a).
  Proof.  constructor. Qed.

  Lemma Assert_relates_assert' :
    forall (w : Ctx nat) (ass : Assignment w),
      (RTy -> RTy -> (RFree' RUnit))%R w ass Symbolic.assert' assert.
  Proof. constructor; assumption. Qed.

  Lemma Exists_relates_exists' :
    forall (w : Ctx nat) (ass : Assignment w),
      (RFree' RTy) w ass (Symbolic.exists_Ty w) exists_ty.
  Proof. admit. Admitted.

  Lemma Bind_relates_bind' {A B a b} (RA : Relation A a) (RB : Relation B b) :
    forall (w : Ctx nat) (ass : Assignment w),
      ((RFree' RA) -> (RBox (RA -> RFree' RB)) -> (RFree' RB))%R w ass (@Symbolic.bind' A B w) bind.
  Proof. intros w ass ? ? ?. induction H. admit.
    Admitted.

  End WithInductive.

End Refinement.

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

  (* Adapted from Katamaran: Symbolic/Worlds.v *)

  Inductive Accessibility (Σ₁ : Ctx nat) : Ctx nat -> Type :=
    | refl    : Accessibility Σ₁ Σ₁
    | fresh α : forall Σ₂, Accessibility Σ₁ Σ₂ ->
                           Accessibility Σ₁ (Σ₂ ▻ α).

  (* ⊢ A *)
  Definition Valid (A : Ctx nat -> Type) := forall Σ, A Σ.

  (* A → B *)
  Definition Impl (A B : Ctx nat -> Type) : Ctx nat -> Type :=
    fun Σ => (A Σ) -> (B Σ).

  (* □ A *)
  Definition Box A (Σ : Ctx nat) :=
    forall Σ', Accessibility Σ Σ' -> A Σ'.

  Lemma empty_is_initial : forall Σ, Accessibility ctx.nil Σ.
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

  Class Persistent (A : Ctx nat -> Type) : Type :=
  { persist : Valid (Impl A (Box A)) }.

  Local Notation "<{ A ~ w }>" := (persist _ A _ w).

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
  - destruct p. apply cons. apply pair. apply s.
    apply persist in t. apply t. apply H.
    apply F. apply E. apply H.
  Show Proof. (* Something <>< *)
  Defined.

  Definition trans {Σ₁ Σ₂ Σ₃} (w12 : Accessibility Σ₁ Σ₂) (w23 : Accessibility Σ₂ Σ₃) : Accessibility Σ₁ Σ₃.
  Proof. induction w23. apply w12. apply fresh. apply IHw23. Defined.

  Local Notation "w1 .> w2" := (trans w1 w2) (at level 80).

  Definition T {A} := fun (Σ : Ctx nat) (a : Box A Σ) => a Σ (refl Σ).

  Definition _4 {A} : Valid (Impl (Box A) (Box (Box A))).
  Proof. cbv in *. intros.  apply X. eapply trans. apply H. apply H0. Defined.

  Print Scopes.

  (*
  Fixpoint bind [A B] {Σ} (m : Cstr A Σ) (f : Box (Impl A (Cstr B)) Σ) {struct m} : Cstr B Σ.
  refine (
    match m with
    | C_eqc _ _ t1 t2 C1 => _
    | C_val _ _ v => _
    | C_fls _ _ => C_fls _ _ (* we just fail *)
    | C_exi _ _ i C => _
    end).
  Proof.
    - apply C_eqc. apply t1. apply t2. eapply bind.
      + apply C1.
      + apply f.
    - apply T in f. unfold Impl in f. apply f. apply v.
    - eapply C_exi. eapply bind.
      + apply C.
      + apply _4 in f. cbv in *. intros. apply (f _ (fresh _ _ _ (refl Σ)) _ H X).
  Show Proof.
  Abort.
  *)

  Fixpoint bind [A B] {Σ} (m : Cstr A Σ) (f : Box (Impl A (Cstr B)) Σ) : Cstr B Σ :=
    match m with
    | C_eqc _ _ t1 t2 C1 => C_eqc B Σ t1 t2 (bind C1 f)
    | C_val _ _ v => (T Σ f) v (* removing the box *)
    | C_fls _ _ => C_fls B Σ
    | C_exi _ _ i C =>
        C_exi B Σ i
          (bind (* (Σ ▻ i) *) C
              (fun Σ' (ω : Accessibility (Σ ▻ i) Σ') (V : A Σ') =>
                 (_4 Σ f) (Σ ▻ i) (fresh Σ i Σ (refl Σ)) Σ' ω V))
    end.

  Local Notation "[ ω ] x <- ma ;; mb" :=
    (bind ma (fun _ ω x => mb))
      (at level 80, x at next level,
        ma at next level, mb at level 200,
        right associativity).

  Definition Unit (Σ : Ctx nat) := unit.

  Definition assert {Σ} t1 t2 := C_eqc Unit Σ t1 t2 (C_val Unit Σ tt).

  Definition exists_Ty : forall Σ, Cstr Ty Σ :=
    fun Σ => let i := ctx.length Σ in
             C_exi Ty Σ i (C_val _ _ (Ty_hole _ i ctx.in_zero)).

  (* Conveniently indexes a given ty with a world Σ *)
  Fixpoint world_index (t : ty) (Σ : Ctx nat) : Ty Σ :=
    match t with
    | ty_bool => Ty_bool Σ
    | ty_func do co => Ty_func Σ (world_index do Σ) (world_index co Σ)
    end.

  Fixpoint infer (e : expr) {Σ : Ctx nat} (Γ : Env Σ) : Cstr Ty Σ :=
    match e with
    | v_true => C_val Ty Σ (Ty_bool Σ)
    | v_false => C_val Ty Σ (Ty_bool Σ)
    | e_if cnd coq alt =>
        [ ω₁ ] t_cnd <- infer cnd Γ ;;
        [ ω₂ ] _     <- assert t_cnd (Ty_bool _) ;;
        [ ω₃ ] t_coq <- infer coq <{ Γ ~ ω₁ .> ω₂ }> ;;
        [ ω₄ ] t_alt <- infer alt <{ Γ ~ ω₁ .> ω₂ .> ω₃ }> ;;
        [ ω₅ ] _     <- assert <{ t_coq ~ ω₄ }>  <{ t_alt ~ (refl _) }> ;;
           C_val Ty _ <{ t_coq ~ ω₄ .> ω₅ }>
    | e_var var =>
        match (value var Γ) with
        | Some t_var => C_val Ty _ t_var
        | None => C_fls Ty Σ
        end
    | e_app f a =>
        [ w1 ] t_co <- exists_Ty Σ ;;
        [ w2 ] t_do <- infer a <{ Γ ~ w1 }> ;;
        [ w3 ] t_fn <- infer f <{ Γ ~ w1 .> w2 }> ;;
        [ w4 ] _    <- assert t_fn <{ (Ty_func _ t_do <{ t_co ~ w2 }> ) ~ w3 }> ;;
           C_val Ty _ <{ t_co ~ w2 .> w3 .> w4 }>
    | e_abst var t_var e =>
        let t_var' := (world_index t_var Σ) in (* t_var lives in ty, not in (Ty w) *)
        [ w1 ] t_e <- infer e ((var, t_var') :: Γ) ;;
          C_val Ty _ (Ty_func _ <{ t_var' ~ w1 }> t_e)
    | e_absu var e =>
        [ w1 ] t_var <- exists_Ty Σ ;;
        [ w2 ] t_e <- infer e ((var, t_var) :: <{ Γ ~ w1 }>) ;;
          C_val Ty _ (Ty_func _ <{ t_var ~ w2 }> t_e)
    end.

  Section RunTI.

    (* To run the type inferencer, we must submit a generated
       constraint to the unifier. In turn, this requires
       converting the constraint into prenex normal form.
       We could do this while generating the constraints,
       but instead we choose to do it afterwards. *)

    Definition Prenex A Σ : Type :=
      option { Σ' : Ctx nat & Accessibility Σ Σ' * list (Ty Σ' * Ty Σ') * A Σ' }%type.

    Fixpoint pnf [A] {Σ} (c : Cstr A Σ) {struct c} : Prenex A Σ :=
      match c with
      | C_val _ _ V       =>
          Some (existT _ _ (refl Σ, nil, V))
      | C_fls _ _         =>
          None
      | C_eqc _ _ T1 T2 K =>
          match pnf K with
          | None => None
          | Some (existT _ Σ' (a, b, c)) =>
              Some (existT _ _ (a, (<{ T1 ~ a }>, <{ T2 ~ a }>) :: b, c))
          end
      | C_exi _ _ i K     =>
          match pnf K with
          | None => None
          | Some (existT _ Σ' (a, b, c)) =>
              Some (existT _ _ ((trans (fresh _ i _ (refl Σ)) a), b, c))
          end
      end.

    Fixpoint ground {Σ} : Unification.Assignment Σ :=
      match Σ with
      | ctx.nil => env.nil
      | Γ ▻ b   => env.snoc ground b ty_bool
      end.

    Definition solve_constraints {AT AV Σ}
      (Aassign : forall Σ, Unification.Assignment Σ -> AT Σ -> AV) :
      Prenex AT Σ -> option AV.
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
      apply pnf.
      apply (infer e []%list).
    Defined.

  End RunTI.

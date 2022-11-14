Require Import List.
Import ListNotations.
From Em Require Import
     Context Environment.
Import ctx.notations.
From Em Require Import
     STLC.
From Em Require
  Unification.

(* Adapted from Katamaran: Symbolic/Worlds.v *)

Inductive Accessibility (Σ₁ : Ctx nat) : Ctx nat -> Type :=
  | refl    : Accessibility Σ₁ Σ₁
  | fresh α : forall Σ₂, Accessibility (Σ₁ ▻ α) Σ₂ ->
                          Accessibility Σ₁ Σ₂.

(* ⊢ A *)
Definition Valid (A : Ctx nat -> Type) := forall Σ, A Σ.

(* A → B *)
Definition Impl (A B : Ctx nat -> Type) : Ctx nat -> Type :=
  fun Σ => (A Σ) -> (B Σ).

(* □ A *)
Definition Box A (Σ : Ctx nat) :=
  forall Σ', Accessibility Σ Σ' -> A Σ'.

(* Lemma empty_is_initial : forall Σ, Accessibility ctx.nil Σ. *)
(* Proof. intros. induction Σ. apply refl. apply fresh. apply IHΣ. Defined. *)

(* _[_] *)
Definition transient : forall (Σ Σ' : Ctx nat) (i : nat),
    Accessibility Σ Σ' ->
    i ∈ Σ -> i ∈ Σ'.
Proof. intros. induction H. apply H0. apply IHAccessibility. apply ctx.in_succ.  apply H0. Defined.

Eval cbv [transient Accessibility_rec Accessibility_rect] in @transient.

Class Persistent (A : Ctx nat -> Type) : Type :=
  persist : Valid (Impl A (Box A)).

Local Notation "<{ A ~ w }>" := (persist _ A _ w).

#[refine] Instance Persistent_Ty : Persistent Ty :=
  fix F {Σ} (t : Ty Σ) {Σ'} (r : Accessibility Σ Σ') : Ty Σ' :=
    match t with
    | Ty_bool _ => Ty_bool Σ'
    | Ty_func _ t0 t1 => Ty_func Σ' (F t0 r) (F t1 r)
    | Ty_hole _ i i0 => Ty_hole Σ' i (transient Σ Σ' i r i0)
    end.
Defined.

#[refine] Instance Persistent_Env : Persistent Env :=
  fix F {Σ} (l : list (String.string * Ty Σ)) {Σ'} (ω : Accessibility Σ Σ') :
           list (String.string * Ty Σ') :=
    match l with
    | []%list => []%list
    | (a0, b) :: l => (a0, <{ b ~ ω}>) :: F l ω
    end.
Defined.


(* Definition trans {Σ₁ Σ₂ Σ₃} (w12 : Accessibility Σ₁ Σ₂) (w23 : Accessibility Σ₂ Σ₃) : Accessibility Σ₁ Σ₃. *)
(* Proof. induction w12. apply w23.  apply (fresh Σ₁ α). apply IHw12. apply w23. Defined. *)

(* Eval cbv [trans Accessibility_rec Accessibility_rect] in @trans. *)

Fixpoint trans {w1 w2 w3} (w12 : Accessibility w1 w2) : Accessibility w2 w3 -> Accessibility w1 w3 :=
  match w12 with
  | refl _ => fun w13 : Accessibility w1 w3 => w13
  | fresh _ α w ω =>
      fun ω' : Accessibility w w3  => fresh w1 α w3 (trans ω ω')
  end.

Local Notation "w1 .> w2" := (trans w1 w2) (at level 80).

Lemma trans_refl : forall (w1 w2 : Ctx nat) w12,
  (@trans w1 w2 w2 w12 (refl w2)) = w12.
Proof. intros. induction w12. auto. cbn. now rewrite IHw12. Qed.

(* Move to PersistLaws, induction V *)
Lemma persist_assoc : forall w1 w2 w3 r12 r23 V,
    persist w2 (persist w1 V w2 r12) w3 r23 = persist w1 V w3 (trans r12 r23).
Proof. intros. induction V as [|[]]; cbn; repeat f_equal; auto. Admitted.

Definition T {A} := fun (Σ : Ctx nat) (a : Box A Σ) => a Σ (refl Σ).

Definition _4 {A} : Valid (Impl (Box A) (Box (Box A))).
Proof. cbv in *. intros.  apply X. eapply trans. apply H. apply H0. Defined.

Print Scopes.

(*
Fixpoint bind [A B] {Σ} (m : FreeM A Σ) (f : Box (Impl A (FreeM B)) Σ) {struct m} : FreeM B Σ.
refine (
  match m with
  | Bind_AssertEq_Free _ _ t1 t2 C1 => _
  | Ret_Free _ _ v => _
  | Fail_Free _ _ => Fail_Free _ _ (* we just fail *)
  | Bind_Exists_Free _ _ i C => _
  end).
Proof.
  - apply T in f. unfold Impl in f. apply f. apply v.
  - apply Bind_AssertEq_Free. apply t1. apply t2. eapply bind.
    + apply C1.
    + apply f.
  - eapply Bind_Exists_Free. eapply bind.
    + apply C.
    + apply _4 in f. cbv in *. intros. apply (f _ (fresh _ _ _ (refl _) ) _ H X).
Show Proof.
Abort.
*)

Fixpoint bind [A B] {Σ} (m : FreeM A Σ) (f : Box (Impl A (FreeM B)) Σ) : FreeM B Σ :=
  match m with
  | Bind_AssertEq_Free _ _ t1 t2 C1 => Bind_AssertEq_Free B Σ t1 t2 (bind C1 f)
  | Ret_Free _ _ v => (T Σ f) v (* removing the box *)
  | Fail_Free _ _ => Fail_Free B Σ
  | Bind_Exists_Free _ _ i C =>
      Bind_Exists_Free B Σ i
        (bind (* (Σ ▻ i) *) C
            (fun Σ' (ω : Accessibility (Σ ▻ i) Σ') (V : A Σ') =>
               (_4 Σ f) (Σ ▻ i) (fresh Σ i (Σ ▻ i) (refl (Σ ▻ i))) Σ' ω V))
  end.

Local Notation "[ ω ] x <- ma ;; mb" :=
  (bind ma (fun _ ω x => mb))
    (at level 80, x at next level,
      ma at next level, mb at level 200,
      right associativity).

Definition Unit (Σ : Ctx nat) := unit.

Definition assert {Σ} t1 t2 := Bind_AssertEq_Free Unit Σ t1 t2 (Ret_Free Unit Σ tt).

Definition exists_Ty : forall Σ, FreeM Ty Σ :=
  fun Σ => let i := ctx.length Σ in
           Bind_Exists_Free Ty Σ i (Ret_Free _ _ (Ty_hole _ i ctx.in_zero)).

(* Conveniently indexes a given ty with a world Σ *)
(* call it lift *)
Fixpoint lift (t : ty) (Σ : Ctx nat) : Ty Σ :=
  match t with
  | ty_bool => Ty_bool Σ
  | ty_func do co => Ty_func Σ (lift do Σ) (lift co Σ)
  end.

Fixpoint infer (e : expr) {Σ : Ctx nat} (Γ : Env Σ) : FreeM Ty Σ :=
  match e with
  | v_true => Ret_Free Ty Σ (Ty_bool Σ)
  | v_false => Ret_Free Ty Σ (Ty_bool Σ)
  | e_if cnd coq alt =>
      [ ω₁ ] t_cnd <- infer cnd Γ ;;
      [ ω₂ ] _     <- assert t_cnd (Ty_bool _) ;;
      [ ω₃ ] t_coq <- infer coq <{ Γ ~ ω₁ .> ω₂ }> ;;
      [ ω₄ ] t_alt <- infer alt <{ Γ ~ ω₁ .> ω₂ .> ω₃ }> ;;
      [ ω₅ ] _     <- assert <{ t_coq ~ ω₄ }>  <{ t_alt ~ (refl _) }> ;;
         Ret_Free Ty _ <{ t_coq ~ ω₄ .> ω₅ }>
  | e_var var =>
      match (value var Γ) with
      | Some t_var => Ret_Free Ty _ t_var
      | None => Fail_Free Ty Σ
      end
  | e_app f a =>
      [ ω1 ] t_co <- exists_Ty Σ ;;
      [ ω2 ] t_do <- infer a <{ Γ ~ ω1 }> ;;
      [ ω3 ] t_fn <- infer f <{ Γ ~ ω1 .> ω2 }> ;;
      [ ω4 ] _    <- assert t_fn <{ (Ty_func _ t_do <{ t_co ~ ω2 }> ) ~ ω3 }> ;;
         Ret_Free Ty _ <{ t_co ~ ω2 .> ω3 .> ω4 }>
  | e_abst var t_var e =>
      let t_var' := (lift t_var Σ) in (* t_var lives in ty, not in (Ty w) *)
      [ ω1 ] t_e <- infer e ((var, t_var') :: Γ) ;;
        Ret_Free Ty _ (Ty_func _ <{ t_var' ~ ω1 }> t_e)
  | e_absu var e =>
      [ ω1 ] t_var <- exists_Ty Σ ;;
      [ ω2 ] t_e <- infer e ((var, t_var) :: <{ Γ ~ ω1 }>) ;;
        Ret_Free Ty _ (Ty_func _ <{ t_var ~ ω2 }> t_e)
  end.

Section RunTI.

  (* To run the type inferencer, we must submit a generated
     constraint to the unifier. In turn, this requires
     converting the constraint into prenex normal form.
     We could do this while generating the constraints,
     but instead we choose to do it afterwards. *)

  Definition Prenex A Σ : Type :=
    option { Σ' : Ctx nat & Accessibility Σ Σ' * list (Ty Σ' * Ty Σ') * A Σ' }%type.

  Fixpoint pnf [A] {Σ} (c : FreeM A Σ) {struct c} : Prenex A Σ :=
    match c with
    | Ret_Free _ _ V =>
        Some (existT _ _ (refl Σ, nil, V))
    | Fail_Free _ _  =>
        None
    | Bind_AssertEq_Free _ _ T1 T2 K =>
        match pnf K with
        | None => None
        | Some (existT _ Σ' (a, b, c)) =>
            Some (existT _ _ (a, (<{ T1 ~ a }>, <{ T2 ~ a }>) :: b, c))
        end
    | Bind_Exists_Free _ _ i K =>
        match pnf K with
        | None => None
        | Some (existT _ Σ' (a, b, c)) =>
            Some (existT _ _ (fresh Σ i (Σ ▻ i) (refl (Σ ▻ i)) .> a, b, c))
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

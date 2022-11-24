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

Fixpoint transient  (Σ Σ' : Ctx nat) (i : nat) (r : Accessibility Σ Σ') :
    i ∈ Σ -> i ∈ Σ'.
Proof. destruct r. auto. intro. eapply transient. apply r. constructor. apply H. Defined.

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

Definition T {A} := fun (Σ : Ctx nat) (a : Box A Σ) => a Σ (refl Σ).

Definition _4 {A} : Valid (Impl (Box A) (Box (Box A))).
Proof. cbv in *. intros.  apply X. eapply trans. apply H. apply H0. Defined.

Fixpoint bind [A B] {Σ} (m : FreeM A Σ) (f : Box (Impl A (FreeM B)) Σ)
  : FreeM B Σ :=
  match m with
  | Ret_Free _ _ v => (T Σ f) v (* removing the box *)
  | Fail_Free _ _ => Fail_Free B Σ
  | Bind_AssertEq_Free _ _ t1 t2 C1 =>
      Bind_AssertEq_Free B Σ t1 t2 (bind C1 f)
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

Definition assert {Σ} t1 t2 :=
  Bind_AssertEq_Free Unit Σ t1 t2 (Ret_Free Unit Σ tt).

Definition exists_Ty : forall Σ, FreeM Ty Σ :=
  fun Σ => let i := ctx.length Σ in
           Bind_Exists_Free Ty Σ i (Ret_Free _ _ (Ty_hole _ i ctx.in_zero)).

(* Indexes a given ty by a world Σ *)
Fixpoint lift (t : ty) (Σ : Ctx nat) : Ty Σ :=
  match t with
  | ty_bool => Ty_bool Σ
  | ty_func do co => Ty_func Σ (lift do Σ) (lift co Σ)
  end.

Fixpoint generate (e : expr) {Σ : Ctx nat} (Γ : Env Σ) : FreeM Ty Σ :=
  match e with
  | v_true => Ret_Free Ty Σ (Ty_bool Σ)
  | v_false => Ret_Free Ty Σ (Ty_bool Σ)
  | e_if cnd coq alt =>
      [ ω₁ ] t_cnd <- generate cnd Γ ;;
      [ ω₂ ] _     <- assert t_cnd (Ty_bool _) ;;
      [ ω₃ ] t_coq <- generate coq <{ Γ ~ ω₁ .> ω₂ }> ;;
      [ ω₄ ] t_alt <- generate alt <{ Γ ~ ω₁ .> ω₂ .> ω₃ }> ;;
      [ ω₅ ] _     <- assert <{ t_coq ~ ω₄ }>  <{ t_alt ~ (refl _) }> ;;
         Ret_Free Ty _ <{ t_coq ~ ω₄ .> ω₅ }>
  | e_var var =>
      match (value var Γ) with
      | Some t_var => Ret_Free Ty _ t_var
      | None => Fail_Free Ty Σ
      end
  | e_app f a =>
      [ ω1 ] t_co <- exists_Ty Σ ;;
      [ ω2 ] t_do <- generate a <{ Γ ~ ω1 }> ;;
      [ ω3 ] t_fn <- generate f <{ Γ ~ ω1 .> ω2 }> ;;
      [ ω4 ] _    <- assert t_fn <{ (Ty_func _ t_do <{ t_co ~ ω2 }> ) ~ ω3 }> ;;
         Ret_Free Ty _ <{ t_co ~ ω2 .> ω3 .> ω4 }>
  | e_abst var t_var e =>
      let t_var' := (lift t_var Σ) in (* t_var lives in ty, not in (Ty w) *)
      [ ω1 ] t_e <- generate e ((var, t_var') :: Γ) ;;
        Ret_Free Ty _ (Ty_func _ <{ t_var' ~ ω1 }> t_e)
  | e_absu var e =>
      [ ω1 ] t_var <- exists_Ty Σ ;;
      [ ω2 ] t_e <- generate e ((var, t_var) :: <{ Γ ~ ω1 }>) ;;
        Ret_Free Ty _ (Ty_func _ <{ t_var ~ ω2 }> t_e)
  end.

Section RunTI.

  (* infer_ng defines inference without grounding
     of remaining unification variables. *)
  Definition infer_ng (e : expr) : SolvedM Ty [] :=
    Unification.Variant1.solve_ng (@generate e ctx.nil []%list).

  Fixpoint ground (w: Ctx nat) (ass : Unification.Assignment w)
                  (s: SolvedM Ty w) : option ty.
  Proof. destruct s.
    - (* value  *) apply Some. apply (Unification.applyassign t ass).
    - (* fail   *) apply None.
    - (* exists *) apply (ground (w ▻ i)).
      + constructor. apply ass. constructor 1. (* ground remaining to Bool *)
      + apply s.
  Defined.

  Definition runTI (e : expr) : option ty :=
    ground ctx.nil env.nil (infer_ng e).

End RunTI.

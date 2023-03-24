From Equations.Type Require
     Classes.
Require Import Relation_Definitions String.
From Em Require Import
     Context Environment Prelude.
Import ctx.
Import ctx.notations.

Notation World := (Ctx nat).

Polymorphic Definition TYPE : Type := World -> Type.
(* The type of accessibility relations between worlds. Because we work with
   multiple different definitions of accessibility, we generalize many
   definitions over the accessibility relation. *)
Definition ACC : Type := World -> TYPE.

Class Refl (R : ACC) : Type :=
  refl : forall w, R w w.
Class Trans (R : ACC) : Type :=
  trans : forall w1 w2 w3, R w1 w2 -> R w2 w3 -> R w1 w3.
Class Step (R : ACC) : Type :=
  step : forall w α, R w (w ▻ α).
#[global] Arguments refl {R _ w}.
#[global] Arguments step {R _ w α}.
#[global] Arguments trans {R _ w1 w2 w3} _ _.

Class PreOrder R {reflR : Refl R} {transR : Trans R} : Prop :=
  { trans_refl_l {w1 w2} {r : R w1 w2} :
      trans refl r = r;
    trans_refl_r {w1 w2} {r : R w1 w2} :
      trans r refl = r;
    trans_assoc {w0 w1 w2 w3} (r1 : R w0 w1) (r2 : R w1 w2) (r3 : R w2 w3) :
      trans (trans r1 r2) r3 = trans r1 (trans r2 r3);
  }.

Module alloc.

  Inductive Alloc (Σ₁ : World) : TYPE :=
    | refl    : Alloc Σ₁ Σ₁
    | fresh α : forall Σ₂, Alloc (Σ₁ ▻ α) Σ₂ ->
                              Alloc Σ₁ Σ₂.

  #[export] Instance refl_accessibility : Refl Alloc :=
    fun w => refl _.
  #[export] Instance trans_accessibility : Trans Alloc :=
    fix trans {w1 w2 w3} (r12 : Alloc w1 w2) : Alloc w2 w3 -> Alloc w1 w3 :=
    match r12 with
    | refl _         => fun r23 => r23
    | fresh _ α w2 r => fun r23 => fresh _ α w3 (trans r r23)
    end.

  #[export] Instance step_accessibility : Step Alloc :=
    fun w α => fresh w α (w ▻ α) (refl (w ▻ α)).

  #[export] Instance preorder_accessibility : PreOrder Alloc.
  Proof.
    constructor.
    - easy.
    - intros ? ? r; induction r; cbn; [|rewrite IHr]; easy.
    - induction r1; cbn; congruence.
  Qed.

  Lemma snoc_r {w1 w2} (r : Alloc w1 w2) :
    forall α, Alloc w1 (w2 ▻ α).
  Proof.
    induction r; cbn; intros β.
    - econstructor 2; constructor 1.
    - econstructor 2. apply IHr.
  Qed.

  Lemma nil_l {w} : Alloc ctx.nil w.
  Proof. induction w; [constructor|now apply snoc_r]. Defined.

End alloc.

(* Everything is now qualified, except the stuff in paren on the line below *)
Export alloc (Alloc).
Export (hints) alloc.

Definition Valid (A : TYPE) : Type :=
  forall w, A w.
Polymorphic Definition Impl (A B : TYPE) : TYPE :=
  fun w => A w -> B w.
Definition Forall {I : Type} (A : I -> TYPE) : TYPE :=
  fun w => forall i : I, A i w.

Declare Scope indexed_scope.
Bind    Scope indexed_scope with TYPE.

Notation "⊢ A" := (Valid A) (at level 100).
Notation "A -> B" := (Impl A B) : indexed_scope.
Notation "'∀' x .. y , P " :=
  (Forall (fun x => .. (Forall (fun y => P)) ..))
    (at level 99, x binder, y binder, right associativity) : indexed_scope.

Definition Const (A : Type) : TYPE := fun _ => A.
Definition PROP : TYPE := fun _ => Prop.
Definition Unit : TYPE := fun _ => unit.
Definition Option (A : TYPE) : TYPE := fun w => option (A w).
Definition List (A : TYPE) : TYPE := fun w => list (A w).
Definition Prod (A B : TYPE) : TYPE := fun w => prod (A w) (B w).
Definition Sum (A B : TYPE) : TYPE := fun w => sum (A w) (B w).

Definition Box (R : ACC) (A : TYPE) : TYPE :=
  fun w0 => forall w1, R w0 w1 -> A w1.

(* Notation "◻A" := BoxR A *)

Class Pure (M : TYPE -> TYPE) : Type :=
  pure : forall A, ⊢ A -> M A.
#[global] Arguments pure {M _ A} [w].
Class Bind (R : ACC) (M : TYPE -> TYPE) : Type :=
  bind : forall A B, ⊢ M A -> Box R (A -> M B) -> M B.
#[global] Arguments bind {R M _ A B} [w].

Module MonadNotations.
  Notation "[ r ] x <- ma ;; mb" :=
    (bind ma (fun _ r x => mb))
      (at level 80, x at next level,
        ma at next level, mb at level 200,
        right associativity).
End MonadNotations.

Module Diamond.
  Import SigTNotations.

  Definition Diamond (R : ACC) (A : TYPE) : TYPE :=
    fun w0 => {w1 & R w0 w1 * A w1}%type.
  Definition DiamondT (R : ACC) (M : TYPE -> TYPE) : TYPE -> TYPE :=
    fun A => M (Diamond R A).

  #[export] Instance pure {R} {reflR : Refl R} : Pure (Diamond R) :=
    fun A w a => (w;(refl,a)).
  #[export] Instance bind {R} {transR : Trans R} : Bind R (Diamond R) :=
    fun A B w0 m f =>
      let '(w1;(r01,a1)) := m in
      let '(w2;(r12,b2)) := f w1 r01 a1 in
      (w2; (trans r01 r12, b2)).

End Diamond.
Export Diamond (Diamond, DiamondT).

Definition Schematic (A : TYPE) : Type :=
  { w : World & A w }.

Notation "w1 .> w2" := (trans (R := Alloc) w1 w2) (at level 80, only parsing).
Infix "⊙" := trans (at level 60, right associativity).

(* TODO: switch to superscript *)
(* \^s \^+ *)

Notation "□⁺ A" := (Box Alloc A) (at level 9, format "□⁺ A", right associativity)
    : indexed_scope.
Notation "◇⁺ A" := (Diamond Alloc A) (at level 9, format "◇⁺ A", right associativity)
    : indexed_scope.

Class Persistent (R : ACC) (A : TYPE) : Type :=
  persist : ⊢ A -> Box R A.

Class PersistLaws A `{Persistent Alloc A} : Type :=
  { refl_persist w (V : A w) :
        persist w V w refl = V
  ; assoc_persist w1 w2 w3 r12 r23 (V : A w1) :
        persist w2 (persist w1 V w2 r12) w3 r23
      = persist w1 V w3 (trans r12 r23) }.

(* Instance Persistent_Prod : forall A B R, *)
(*     Persistent R A -> Persistent R B -> Persistent R (Prod A B). *)
(* Proof. firstorder. Qed. *)

Definition T {R} {reflR : Refl R} {A} : ⊢ Box R A -> A :=
  fun w a => a w refl.
#[global] Arguments T {R _ A} [_] _ : simpl never.

Definition _4 {R} {transR : Trans R} {A} : ⊢ Box R A -> Box R (Box R A) :=
  fun w0 a w1 r1 w2 r2 => a w2 (trans r1 r2).
#[global] Arguments _4 {R _ A} [_] _ [_] _ [_] _ : simpl never.

Definition K {R A B} :
  ⊢ Box R (A -> B) -> (Box R A -> Box R B) :=
  fun w0 f a w1 ω01 =>
    f w1 ω01 (a w1 ω01).

#[export] Instance Persistent_In {x} :
  Persistent Alloc (ctx.In x) :=
  fix transient {w} (xIn : x ∈ w) {w'} (r : Alloc w w') {struct r} :=
    match r with
    | alloc.refl _        => xIn
    | alloc.fresh _ α _ r => transient (in_succ xIn) r
    end.

#[export] Instance PersistLaws_In {x} : PersistLaws (ctx.In x).
Proof. constructor; [easy|induction r12; cbn; auto]. Qed.

#[export] Instance persistent_const {R A} : Persistent R (Const A) :=
  fun _ a _ _ => a.

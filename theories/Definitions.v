From Coq Require Import
     Classes.CRelationClasses.
From Equations.Type Require
     Classes.
Require Import Relation_Definitions String.
From Em Require Import
     Context Environment Prelude.
Import ctx.
Import ctx.notations.

Notation World := (Ctx nat).
Definition TYPE : Type := World -> Type.
Definition Valid (A : TYPE) : Type :=
  forall w, A w.
Definition Impl (A B : TYPE) : TYPE :=
  fun w => A w -> B w.
Definition Forall {I : Type} (A : I -> TYPE) : TYPE :=
  fun w => forall i : I, A i w.

Declare Scope indexed_scope.
Bind    Scope indexed_scope with TYPE.

Notation "⊢ A" := (Valid A) (at level 100).
Notation "A -> B" := (Impl A B) : indexed_scope.

Definition Const (A : Type) (w : World) : Type := A.
Definition Unit : TYPE := fun _ => unit.
Definition Option (A : TYPE) : TYPE := fun w => option (A w).
Definition List (A : TYPE) : TYPE := fun w => list (A w).
Definition Prod (A B : TYPE) : TYPE := fun w => prod (A w) (B w).
Definition Sum (A B : TYPE) : TYPE := fun w => sum (A w) (B w).

Definition BoxR (R : Relation.relation World) (A : TYPE) : TYPE :=
  fun w0 => forall w1, R w0 w1 -> A w1.

(* Notation "◻A" := BoxR A *)

Definition DiamondR (R : Relation.relation World) (A : TYPE) : TYPE :=
  fun w0 => {w1 & R w0 w1 * A w1}%type.

Notation "[< R >] A" := (BoxR R A) (at level 9, format "[< R >] A", right associativity).

Module acc.

  Inductive Accessibility (Σ₁ : World) : TYPE :=
    | refl    : Accessibility Σ₁ Σ₁
    | fresh α : forall Σ₂, Accessibility (Σ₁ ▻ α) Σ₂ ->
                              Accessibility Σ₁ Σ₂.

  Fixpoint trans {w1 w2 w3} (w12 : Accessibility w1 w2) : Accessibility w2 w3 -> Accessibility w1 w3 :=
    match w12 with
    | refl _ => fun w13 : Accessibility w1 w3 => w13
    | fresh _ α w ω =>
        fun ω' : Accessibility w w3  => fresh w1 α w3 (trans ω ω')
    end.

  Lemma trans_refl : forall (w1 w2 : World) w12,
      (@trans w1 w2 w2 w12 (acc.refl w2)) = w12.
  Proof. intros. induction w12. auto. cbn. now rewrite IHw12. Qed.

End acc.

Notation "w1 .> w2" := (acc.trans w1 w2) (at level 80).

(* Everything is now qualified, except the stuff in paren on the line below *)
Export acc (Accessibility).

(* TODO: switch to superscript *)
(* \^s \^+ *)

Notation "□⁺ A" := (BoxR Accessibility A) (at level 9, format "□⁺ A", right associativity)
    : indexed_scope.

Class Persistent (R : Relation.relation World) (A : TYPE) : Type :=
  persist : ⊢ A -> BoxR R A.

Instance Persistent_Prod : forall A B R,
    Persistent R A -> Persistent R B -> Persistent R (Prod A B).
Proof. firstorder. Qed.

Definition T {A} : ⊢ □⁺A -> A := fun w a => a w (acc.refl w).

Definition _4 {A} : ⊢ □⁺A -> □⁺□⁺A.
Proof. cbv in *. intros.  apply X. eapply acc.trans; eauto. Defined.

Fixpoint transient  (Σ Σ' : World) (i : nat) (r : Accessibility Σ Σ') :
    i ∈ Σ -> i ∈ Σ'.
Proof.
  destruct r. auto. intro. eapply transient. apply r. constructor. apply H.
Defined.

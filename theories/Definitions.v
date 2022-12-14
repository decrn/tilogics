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

(* pure  :: a -> f a *)
(* apply :: f (a -> b) -> f a -> f b *)


(* η   : Valid (Impl Unit (f unit)) *)
(* <*> : f a -> f b -> f (a * b) *)

Declare Scope indexed_scope.
Bind Scope indexed_scope with TYPE.

Notation "⊢ A" := (Valid A) (at level 100).
Notation "A -> B" := (Impl A B) : indexed_scope.

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

End acc.

(* Everything is now qualified, except the stuff in paren on the line below *)
Export acc (Accessibility).

(* □ A *)
Definition Box (A : TYPE) : TYPE :=
  fun w => forall w', Accessibility w w' -> A w'.

(* TODO: switch to superscript *)
(* \^s \^+ *)

Notation "◻₊ A" := (Box A) (at level 9, format "◻₊ A", right associativity)
    : indexed_scope.

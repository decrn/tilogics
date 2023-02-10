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

Definition BoxR (R : Relation.relation World) (A : TYPE) : TYPE :=
  fun w0 => forall w1, R w0 w1 -> A w1.

(* Notation "◻A" := BoxR A *)

Definition DiamondR (R : Relation.relation World) (A : TYPE) : TYPE :=
  fun w0 => {w1 & R w0 w1 * A w1}%type.

Notation "[< R >] A" := (BoxR R A) (at level 9, format "[< R >] A", right associativity).
Notation "<[ R ]> A" := (DiamondR R A) (at level 9, format "<[ R ]> A", right associativity).

Definition Schematic (A : TYPE) : Type :=
  { w : World & A w }.

Module acc.

  Inductive Accessibility (Σ₁ : World) : TYPE :=
    | refl    : Accessibility Σ₁ Σ₁
    | fresh α : forall Σ₂, Accessibility (Σ₁ ▻ α) Σ₂ ->
                              Accessibility Σ₁ Σ₂.

  Definition step {w α} : Accessibility w (w ▻ α) :=
    fresh w α (w ▻ α) (refl (w ▻ α)).

  Fixpoint trans {w1 w2 w3} (w12 : Accessibility w1 w2) : Accessibility w2 w3 -> Accessibility w1 w3 :=
    match w12 with
    | refl _ => fun w13 : Accessibility w1 w3 => w13
    | fresh _ α w ω =>
        fun ω' : Accessibility w w3  => fresh w1 α w3 (trans ω ω')
    end.

  Lemma trans_refl : forall (w1 w2 : World) w12,
      (@trans w1 w2 w2 w12 (acc.refl w2)) = w12.
  Proof. intros. induction w12. auto. cbn. now rewrite IHw12. Qed.

  Lemma snoc_r {w1 w2} (r : Accessibility w1 w2) :
    forall α, Accessibility w1 (w2 ▻ α).
  Proof.
    induction r; cbn; intros β.
    - econstructor 2; constructor 1.
    - econstructor 2. apply IHr.
  Qed.

  Lemma nil_l {w} : Accessibility ctx.nil w.
  Proof. induction w; [constructor|now apply snoc_r]. Qed.

End acc.

Notation "w1 .> w2" := (acc.trans w1 w2) (at level 80).

(* Everything is now qualified, except the stuff in paren on the line below *)
Export acc (Accessibility).

(* TODO: switch to superscript *)
(* \^s \^+ *)

Notation "□⁺ A" := (BoxR Accessibility A) (at level 9, format "□⁺ A", right associativity)
    : indexed_scope.
Notation "◇⁺ A" := (DiamondR Accessibility A) (at level 9, format "◇⁺ A", right associativity)
    : indexed_scope.

Class Persistent (R : Relation.relation World) (A : TYPE) : Type :=
  persist : ⊢ A -> BoxR R A.

Class PersistLaws A `{Persistent Accessibility A} : Type :=
  { refl_persist w (V : A w) :
        persist w V w (acc.refl w) = V
  ; assoc_persist w1 w2 w3 r12 r23 (V : A w1) :
        persist w2 (persist w1 V w2 r12) w3 r23
      = persist w1 V w3 (acc.trans r12 r23) }.

(* Instance Persistent_Prod : forall A B R, *)
(*     Persistent R A -> Persistent R B -> Persistent R (Prod A B). *)
(* Proof. firstorder. Qed. *)

Definition T {A} : ⊢ □⁺A -> A := fun w a => a w (acc.refl w).

Definition _4 {A} : ⊢ □⁺A -> □⁺□⁺A.
Proof. cbv in *. intros.  apply X. eapply acc.trans; eauto. Defined.

#[export] Instance Persistent_In {x} :
  Persistent Accessibility (ctx.In x) :=
  fix transient {w} (xIn : x ∈ w) {w'} (r : Accessibility w w') {struct r} :=
    match r with
    | acc.refl _        => xIn
    | acc.fresh _ α _ r => transient (in_succ xIn) r
    end.

#[export] Instance PersistLaws_In {x} : PersistLaws (ctx.In x).
Proof. constructor; [easy|induction r12; cbn; auto]. Qed.

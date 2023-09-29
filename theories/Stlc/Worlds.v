(******************************************************************************)
(* Copyright (c) 2023 Denis Carnier, Steven Keuchel                           *)
(* All rights reserved.                                                       *)
(*                                                                            *)
(* Redistribution and use in source and binary forms, with or without         *)
(* modification, are permitted provided that the following conditions are     *)
(* met:                                                                       *)
(*                                                                            *)
(* 1. Redistributions of source code must retain the above copyright notice,  *)
(*    this list of conditions and the following disclaimer.                   *)
(*                                                                            *)
(* 2. Redistributions in binary form must reproduce the above copyright       *)
(*    notice, this list of conditions and the following disclaimer in the     *)
(*    documentation and/or other materials provided with the distribution.    *)
(*                                                                            *)
(* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS        *)
(* "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED  *)
(* TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR *)
(* PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR          *)
(* CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,      *)
(* EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,        *)
(* PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR         *)
(* PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF     *)
(* LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING       *)
(* NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS         *)
(* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.               *)
(******************************************************************************)

From Coq Require Import
  Strings.String.
From Equations Require Import
  Equations.
From stdpp Require
  gmap.
From Em Require Import
  Context Prelude.


Import ctx.notations.

#[local] Set Implicit Arguments.
#[local] Set Transparent Obligations.

Notation World := (Ctx nat).
(* Polymorphic *) Definition TYPE : Type := World -> Type.

Module ṫy.

  Inductive Ṫy (w : World) : Type :=
  | var {α} (αIn : α ∈ w)
  | bool
  | func (t1 t2 : Ṫy w).
  #[global] Arguments var {w α}.
  #[global] Arguments bool {w}.
  #[global] Arguments func {w} _ _.

  Derive NoConfusion Subterm for Ṫy.

  #[local] Set Equations With UIP.
  #[export] Instance In_eqdec {w} : EqDec (sigT (fun x : unit => ctx.In x w)).
  Proof.
    intros [x xIn] [y yIn].
    induction xIn; cbn; destruct (ctx.view yIn) as [|y yIn].
    - left. reflexivity.
    - right. abstract discriminate.
    - right. abstract discriminate.
    - destruct (IHxIn yIn); clear IHxIn; [left|right].
      + abstract (now dependent elimination e).
      + abstract (intros e; apply n; clear n;
                  now dependent elimination e).
  Defined.

  #[export] Instance eqdec {w} : EqDec (Ṫy w).
  Proof.
    change_no_check (forall x y : Ṫy w, dec_eq x y).
    induction x; destruct y as [β βIn| |]; cbn;
      try (right; abstract discriminate).
    - destruct (eq_dec (existT α αIn) (existT β βIn)).
      + left. abstract now dependent elimination e.
      + right. abstract (intros H; apply n; clear n; inversion H; auto).
    - left. auto.
    - apply f_equal2_dec; auto.
      now intros H%noConfusion_inv.
  Defined.

  Lemma no_cycle {w} (t : Ṫy w) : ~ Ṫy_subterm t t.
  Proof.
    induction (well_founded_Ṫy_subterm t) as [? _ IH].
    intros Hx. apply (IH _ Hx Hx).
  Qed.

End ṫy.
Export ṫy (Ṫy).
Export (hints) ṫy.

Definition Ėnv (w : World) :=
  stdpp.gmap.gmap string (Ṫy w).

(* The type of accessibility relations between worlds. Because we work with
   multiple different definitions of accessibility, we generalize many
   definitions over the accessibility relation. *)
Structure ACC : Type :=
  MkAcc
    { acc :> World -> TYPE;
      #[canonical=no] lk {w0 w1} (θ : acc w0 w1) α (αIn : α ∈ w0) : Ṫy w1;
    }.
#[global] Arguments acc Θ (_ _)%ctx_scope : rename, simpl never.
#[global] Arguments lk {Θ} [w0 w1] !θ [α] αIn : rename.

Class Refl (Θ : ACC) : Type :=
  refl w : Θ w w.
Class Trans (Θ : ACC) : Type :=
  trans w0 w1 w2 : Θ w0 w1 -> Θ w1 w2 -> Θ w0 w2.
#[global] Arguments refl {Θ _ w}.
#[global] Arguments trans {Θ _ w0 w1 w2} _ _.

Class ReflTrans Θ {reflΘ : Refl Θ} {transΘ : Trans Θ} : Prop :=
  { trans_refl_l {w1 w2} {r : Θ w1 w2} :
      trans refl r = r;
    trans_refl_r {w1 w2} {r : Θ w1 w2} :
      trans r refl = r;
    trans_assoc {w0 w1 w2 w3} (r1 : Θ w0 w1) (r2 : Θ w1 w2) (r3 : Θ w2 w3) :
      trans (trans r1 r2) r3 = trans r1 (trans r2 r3);
  }.
#[global] Arguments ReflTrans Θ {_ _}.

Class Step (Θ : ACC) : Type :=
  step w α : Θ w (w ▻ α).
#[global] Arguments step {Θ _ w α}.

Class Thin (Θ : ACC) : Type :=
  thin w α {αIn : α ∈ w} : Θ (w - α) w.
#[global] Arguments thin {Θ _ w} α {αIn}.

Class Thick (Θ : ACC) : Type :=
  thick w α {αIn : α ∈ w} (t : Ṫy (w - α)) : Θ w (w - α).
#[global] Arguments thick {Θ _ w} α {αIn} t.

Definition Valid (A : TYPE) : Type :=
  forall w, A w.
Polymorphic Definition Impl (A B : TYPE) : TYPE :=
  fun w => A w -> B w.
Definition Forall {I : Type} (A : I -> TYPE) : TYPE :=
  fun w => forall i : I, A i w.

Declare Scope indexed_scope.
Bind    Scope indexed_scope with TYPE.
Delimit Scope indexed_scope with W.

Definition Const (A : Type) : TYPE := fun _ => A.
Definition PROP : TYPE := fun _ => Prop.
Definition Unit : TYPE := fun _ => unit.
Definition Option (A : TYPE) : TYPE := fun w => option (A w).
Definition List (A : TYPE) : TYPE := fun w => list (A w).
Definition Prod (A B : TYPE) : TYPE := fun w => prod (A w) (B w).
Definition Sum (A B : TYPE) : TYPE := fun w => sum (A w) (B w).

Definition Box (Θ : ACC) (A : TYPE) : TYPE :=
  fun w0 => forall w1, Θ w0 w1 -> A w1.

#[local] Notation "⊢ʷ A" :=
  (Valid A)
    (at level 200, right associativity).
#[local] Notation "A -> B" := (Impl A B) : indexed_scope.


Class Pure (M : TYPE -> TYPE) : Type :=
  pure : forall A, ⊢ʷ A -> M A.
#[global] Arguments pure {M _ A} [w].
Class Bind (Θ : ACC) (M : TYPE -> TYPE) : Type :=
  bind : forall A B, ⊢ʷ M A -> Box Θ (A -> M B) -> M B.
#[global] Arguments bind {Θ M _ A B} [w].

#[export] Instance pure_option : Pure Option :=
  fun A w a => Some a.
#[export] Instance bind_option {Θ} {reflΘ : Refl Θ} : Bind Θ Option :=
  fun A B w m f => option.bind m (fun a => f w refl a).

Module Diamond.
  Import SigTNotations.

  Definition Diamond (Θ : ACC) (A : TYPE) : TYPE :=
    fun w0 => {w1 & Θ w0 w1 * A w1}%type.
  Definition DiamondT (Θ : ACC) (M : TYPE -> TYPE) : TYPE -> TYPE :=
    fun A => M (Diamond Θ A).

  #[export] Instance pure_diamond {Θ} {reflΘ : Refl Θ} : Pure (Diamond Θ) :=
    fun A w a => (w;(refl,a)).
  #[export] Instance bind_diamond {Θ} {transΘ : Trans Θ} : Bind Θ (Diamond Θ) :=
    fun A B w0 m f =>
      let '(w1;(r01,a1)) := m in
      let '(w2;(r12,b2)) := f w1 r01 a1 in
      (w2; (trans r01 r12, b2)).

  #[export] Instance pure_diamondt {Θ} {reflΘ : Refl Θ}
    {M} {pureM : Pure M} : Pure (DiamondT Θ M) :=
    fun A w a => pure (M := M) (pure (M := Diamond Θ) a).

  #[export] Instance bind_diamondt {Θ} {transΘ : Trans Θ} :
    Bind Θ (DiamondT Θ Option) :=
    fun A B w m f =>
      option.bind m
        (fun '(existT w1 (θ1,a1)) =>
           option.bind (f w1 θ1 a1)
             (fun '(existT w2 (θ2,b2)) =>
                Some (w2; (trans θ1 θ2, b2)))).

End Diamond.
Export Diamond (Diamond, DiamondT).


Module World.
  Module notations.
    Notation "⊢ʷ A" :=
      (Valid A)
        (at level 200, right associativity).
    Notation "A -> B" := (Impl A B) : indexed_scope.
    Notation "A * B" := (Prod A B) : indexed_scope.
    Notation "'∀' x .. y , P " :=
      (Forall (fun x => .. (Forall (fun y => P%W)) ..))
        (at level 200, x binder, y binder, right associativity) : indexed_scope.

    Infix "⊙" := trans (at level 60, right associativity).

    (* TODO: switch to superscript *)
    (* \^s \^+ *)

    (* Notation "□ A" := (Box _ A) (at level 9, format "□ A", right associativity). *)

    (* Notation "◻A" := BoxR A *)
  End notations.
End World.

Module MonadNotations.
  Notation "[ r ] x <- ma ;; mb" :=
    (bind ma (fun _ r x => mb))
      (at level 80, x at next level,
        ma at next level, mb at level 200,
        right associativity).

  Notation "[ r ] ' x <- ma ;; mb" :=
    (bind ma (fun _ r x => mb))
      (at level 80, x pattern,
        ma at next level, mb at level 200,
        right associativity).
End MonadNotations.

Definition Schematic (A : TYPE) : Type :=
  { w : World & A w }.

    (* Notation "w1 .> w2" := (trans (Θ := Alloc) w1 w2) (at level 80, only parsing). *)

    (* Notation "□⁺ A" := (Box Alloc A) (at level 9, format "□⁺ A", right associativity) *)
    (*     : indexed_scope. *)
    (* Notation "◇⁺ A" := (Diamond Alloc A) (at level 9, format "◇⁺ A", right associativity) *)
    (*     : indexed_scope. *)

Definition T {Θ} {reflΘ : Refl Θ} {A} : ⊢ʷ Box Θ A -> A :=
  fun w a => a w refl.
#[global] Arguments T {Θ _ A} [_] _ : simpl never.

Definition _4 {Θ} {transΘ : Trans Θ} {A} : ⊢ʷ Box Θ A -> Box Θ (Box Θ A) :=
  fun w0 a w1 r1 w2 r2 => a w2 (trans r1 r2).
#[global] Arguments _4 {Θ _ A} [_] _ [_] _ [_] _ : simpl never.

Definition K {Θ A B} :
  ⊢ʷ Box Θ (A -> B) -> (Box Θ A -> Box Θ B) :=
  fun w0 f a w1 ω01 =>
    f w1 ω01 (a w1 ω01).

Definition thickIn [w x] (xIn : x ∈ w) (s : Ṫy (w - x)) :
  forall y, y ∈ w -> Ṫy (w - x) :=
  fun y yIn =>
    match ctx.occurs_check_view xIn yIn with
    | ctx.Same _     => s
    | ctx.Diff _ yIn => ṫy.var yIn
    end.
#[global] Arguments thickIn [w x] xIn s [y] yIn.

(******************************************************************************)
(* Copyright (c) 2022 Steven Keuchel                                          *)
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
  Classes.Morphisms
  Classes.RelationClasses
  Relations.Relation_Definitions.
From Em Require Import
  Context
  Definitions
  STLC.

Set Implicit Arguments.

#[local] Arguments Ty_hole {Σ i} xIn.
#[local] Arguments Ty_bool {Σ}.
#[local] Arguments Ty_func {Σ}.

Module Pred.

  Declare Scope pred_scope.
  Delimit Scope pred_scope with P.

  Definition Pred (w : World) : Type :=
    Assignment w -> Prop.
  Bind Scope pred_scope with Pred.

  Section Connectives.

    Context {w : World}.

    Definition PValid {w} (P : Pred w) : Prop :=
      forall ι, P ι.
    Definition PUnsatisfiable {w} (P : Pred w) : Prop :=
      forall ι, ~ P ι.

    Definition BiEntails : relation (Pred w) :=
      fun P Q => forall ι, P ι <-> Q ι.
    Definition Entails : relation (Pred w) :=
      fun P Q => forall ι, P ι -> Q ι.

    #[export] Instance equivalence_bientails : Equivalence BiEntails.
    Proof.
      constructor; unfold Reflexive, Symmetric, Transitive, BiEntails;
        [ reflexivity | now symmetry | now etransitivity ].
    Qed.
    #[export] Instance preorder_entails : RelationClasses.PreOrder Entails.
    Proof. constructor; unfold Reflexive, Transitive, Entails; auto. Qed.

    #[export] Instance subrelation_bientails_entails :
      subrelation BiEntails Entails.
    Proof. intros x y xy ι. apply xy. Qed.

    #[export] Instance subrelation_bientails_flip_entails :
      subrelation BiEntails (Basics.flip Entails).
    Proof. intros x y xy ι. apply xy. Qed.

    (* #[export] Instance proper_bientails : *)
    (*   Proper (BiEntails ==> BiEntails ==> iff) BiEntails. *)
    (* Proof. intuition. Qed. *)
    #[export] Instance proper_entails_bientails :
      Proper (BiEntails ==> BiEntails ==> iff) Entails.
    Proof. unfold Proper, respectful, BiEntails, Entails. intuition. Qed.
    #[export] Instance proper_entails_entails :
      Proper (Basics.flip Entails ==> Entails ==> Basics.impl) Entails.
    Proof. unfold Proper, respectful, Basics.impl, Entails. intuition. Qed.

    Definition PTrue : Pred w :=
      fun _ => True.
    Definition PIff (P Q : Pred w) : Pred w :=
      fun ι => P ι <-> Q ι.
    Definition PImpl (P Q : Pred w) : Pred w :=
      fun ι => (P ι -> Q ι)%type.
    Definition PAnd (P Q : Pred w) : Pred w :=
      fun ι => (P ι /\ Q ι)%type.

    #[export] Instance proper_pvalid_bientails : Proper (BiEntails ==> iff) PValid.
    Proof. firstorder. Qed.
    #[export] Instance proper_pvalid_entails : Proper (Entails ==> Basics.impl) PValid.
    Proof. firstorder. Qed.
    #[export] Instance proper_piff : Proper (BiEntails ==> BiEntails ==> BiEntails) PIff.
    Proof. firstorder. Qed.
    #[export] Instance proper_pimpl : Proper (BiEntails ==> BiEntails ==> BiEntails) PImpl.
    Proof. firstorder. Qed.
    #[export] Instance proper_pand : Proper (BiEntails ==> BiEntails ==> BiEntails) PAnd.
    Proof. firstorder. Qed.

  End Connectives.

  (* #[export] Instance proper_iff_impl {w} : *)
  (*   Proper (BiEntails ==> BiEntails ==> Basics.flip Basics.impl) (@BiEntails w). *)
  (* Proof. firstorder. Qed. *)

  Notation "⊩ P" := (PValid P) (at level 95).
  (* Notation "⊩ P" := (forall ι, P%P ι) (at level 95). *)

  #[global] Arguments BiEntails {w} (_ _)%P.
  Notation "P ⊣⊢ Q" := (BiEntails P Q) (at level 95).
  Notation "⊤" := PTrue : pred_scope.
  Notation "P ⇔ Q" := (PIff P Q) (at level 94) : pred_scope.
  Notation "P ⇒ Q" := (PImpl P Q) (at level 94, right associativity) : pred_scope.
  Notation "P ∧ Q" := (PAnd P Q) (at level 80, right associativity) : pred_scope.

  Lemma pimpl_and_adjoint {w} (P Q R : Pred w) :
    (Entails (P ∧ Q)%P R) <-> (Entails P (Q ⇒ R)%P).
  Proof. unfold Entails, PAnd, PImpl. intuition. Qed.

  Lemma split_bientails {w} (P Q : Pred w) :
    Entails P Q -> Entails Q P -> BiEntails P Q.
  Proof. intros PQ QP ι. split; [apply PQ|apply QP]. Qed.

  Lemma pand_comm {w} (P Q : Pred w) : P ∧ Q ⊣⊢ Q ∧ P.
  Proof. unfold BiEntails, PAnd. intuition. Qed.
  Lemma pand_true_l {w} (P : Pred w) : ⊤ ∧ P ⊣⊢ P.
  Proof. now unfold BiEntails, PAnd, PTrue. Qed.
  Lemma pand_true_r {w} (P : Pred w) : P ∧ ⊤ ⊣⊢ P.
  Proof. now unfold BiEntails, PAnd, PTrue. Qed.
  Lemma pimpl_true_l {w} (P : Pred w) : ⊤ ⇒ P ⊣⊢ P.
  Proof. unfold BiEntails, PImpl, PTrue. intuition. Qed.
  Lemma pimpl_true_r {w} (P : Pred w) : P ⇒ ⊤ ⊣⊢ ⊤.
  Proof. unfold BiEntails, PImpl, PTrue. intuition. Qed.

  Section Ext.

    Context {R : ACC} {instR : forall w, Inst (R w) (Assignment w)}.

    Definition Ext  : ⊢ Pred -> Box R Pred :=
      fun w0 p w1 r ι => p (inst r ι).
    #[global] Arguments Ext [w] _%P [w1].

    #[export] Instance proper_ext_bientails {w : World} :
      Proper (BiEntails ==> forall_relation (fun _ => eq ==> BiEntails)) (@Ext w).
    Proof. intros p q pq w1 ? ? ? ι; subst; apply pq. Qed.
    #[export] Instance proper_ext_entails {w : World} :
      Proper (Entails ==> forall_relation (fun _ => eq ==> Entails)) (@Ext w).
    Proof. intros p q pq w1 ? ? ? ι; subst; apply pq. Qed.

    Lemma ext_refl {reflR : Refl R} {instReflR : InstRefl R} {w} (P : Pred w) :
      BiEntails (Ext P refl) P.
    Proof. unfold BiEntails, Ext. intros ι. now rewrite inst_refl. Qed.

    Lemma ext_trans {transR : Trans R} {w0 w1 w2} (r1 : R w0 w1) (r2 : R w1 w2)
      (P : Pred w0) :
      BiEntails (Ext P (trans r1 r2)) (Ext (Ext P r1) r2).
    Proof. unfold BiEntails, Ext. intros ι. now rewrite inst_trans. Qed.

    Lemma ext_and {w0 w1} (ζ01 : R w0 w1) (P Q : Pred w0) :
      Ext P ζ01 ∧ Ext Q ζ01 ⊣⊢ Ext (P ∧ Q) ζ01 .
    Proof. unfold BiEntails, Ext, PAnd. intuition. Qed.

    Lemma ext_impl {w0 w1} (ζ01 : R w0 w1) (P Q : Pred w0) :
      Ext P ζ01 ⇒ Ext Q ζ01 ⊣⊢ Ext (P ⇒ Q) ζ01 .
    Proof. unfold BiEntails, Ext, PAnd. intuition. Qed.

  End Ext.
  #[global] Instance params_ext : Params (@Ext) 6 := {}.

  Section Eq.
    Definition PEq : ⊢ Ty -> Ty -> Pred :=
      fun w t1 t2 ι => inst t1 ι = inst t2 ι.

    Lemma peq_refl {w} (t : Ty w) :
      PEq t t ⊣⊢ ⊤.
    Proof. easy. Qed.

    Lemma peq_symmetry {w} (s t : Ty w) :
      PEq s t ⊣⊢ PEq t s.
    Proof. easy. Qed.

    Lemma peq_persist {R : ACC} {persR : Persistent R Ty}
      (instR : forall w : World, Inst (R w) (Assignment w))
      {w0 w1} (r : R w0 w1) (t1 t2 : Ty w0) :
      PEq (persist _ t1 _ r) (persist _ t2 _ r) ⊣⊢ Ext (PEq t1 t2) r.
    Proof.
      unfold BiEntails, PEq, Ext. intros ι.
      now rewrite !inst_persist_ty.
    Qed.

    Lemma peq_func {w} (s1 s2 t1 t2 : Ty w) :
      PEq (Ty_func s1 s2) (Ty_func t1 t2) ⊣⊢ PEq s1 t1 ∧ PEq s2 t2.
    Proof. unfold PEq, PAnd, BiEntails. cbn. intuition congruence. Qed.

  End Eq.

  Notation "t1 ≃ t2" := (PEq t1 t2) (at level 90) : pred_scope.
  Notation "'Fun' x => b" :=
    (fun w ζ x => b%P w ζ)
      (x binder, at level 100) : pred_scope.

  #[global] Typeclasses Opaque Entails.
  #[global] Typeclasses Opaque BiEntails.

End Pred.
Export Pred (Pred).

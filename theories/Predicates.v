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
  Classes.Morphisms_Prop
  Classes.RelationClasses
  Relations.Relation_Definitions.
From Em Require Import
  Context
  Definitions
  Environment
  Substitution
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

    Definition PFalse : Pred w :=
      fun _ => False.
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
    #[export] Instance proper_pand_bientails : Proper (BiEntails ==> BiEntails ==> BiEntails) PAnd.
    Proof. firstorder. Qed.
    #[export] Instance proper_pand_entails : Proper (Entails ==> Entails ==> Entails) PAnd.
    Proof. firstorder. Qed.

  End Connectives.

  Definition Forall {I : TYPE} : ⊢ (I -> Pred) -> Pred :=
    fun w A ι => forall i : I w, A i ι.
  Definition Exists {I : TYPE} : ⊢ (I -> Pred) -> Pred :=
    fun w A ι => exists i : I w, A i ι.
  #[global] Arguments Forall {I w} A ι.
  #[global] Arguments Exists {I w} A ι.

  Notation "'∀' x ∶ T , Q" :=
      (@Forall T _ (fun x => Q%P))
        (at level 99, x binder, right associativity,
          format "'∀'  x  ∶  T ,  Q")
      : pred_scope.

  (* Notation "'∃' x .. y , Q " := *)
  (*     (Exists (fun x => .. (Exists (fun y => Q%P)) ..)) *)
  (*       (at level 94, x binder, y binder, right associativity) *)
  (*     : pred_scope. *)

  Notation "'∃' x ∶ T , Q" :=
      (@Exists T _ (fun x => Q%P))
        (at level 99, x binder, right associativity,
          format "'∃'  x  ∶  T ,  Q")
      : pred_scope.


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
    BiEntails P Q <-> Entails P Q /\ Entails Q P.
  Proof. unfold Entails, BiEntails. firstorder. Qed.

  Lemma pand_comm {w} (P Q : Pred w) : P ∧ Q ⊣⊢ Q ∧ P.
  Proof. unfold BiEntails, PAnd. intuition. Qed.
  Lemma pand_true_l {w} (P : Pred w) : ⊤ ∧ P ⊣⊢ P.
  Proof. now unfold BiEntails, PAnd, PTrue. Qed.
  Lemma pand_true_r {w} (P : Pred w) : P ∧ ⊤ ⊣⊢ P.
  Proof. now unfold BiEntails, PAnd, PTrue. Qed.
  Lemma pand_false_l {w} (P : Pred w) : PFalse ∧ P ⊣⊢ PFalse.
  Proof. now unfold BiEntails, PAnd, PFalse. Qed.
  Lemma pand_false_r {w} (P : Pred w) : P ∧ PFalse ⊣⊢ PFalse.
  Proof. now unfold BiEntails, PAnd, PFalse. Qed.
  Lemma pimpl_true_l {w} (P : Pred w) : ⊤ ⇒ P ⊣⊢ P.
  Proof. unfold BiEntails, PImpl, PTrue. intuition. Qed.
  Lemma pimpl_true_r {w} (P : Pred w) : P ⇒ ⊤ ⊣⊢ ⊤.
  Proof. unfold BiEntails, PImpl, PTrue. intuition. Qed.
  Lemma entails_true {w} (P : Pred w) : Entails P PTrue.
  Proof. easy. Qed.

  Lemma pPoseProof {w} {P Q R : Pred w} :
    PValid Q -> Entails (P ∧ Q)%P R -> Entails P R.
  Proof. unfold PValid, Entails, PAnd. intuition. Qed.

  Lemma pGeneralize {w} {P Q R : Pred w} :
    PValid Q -> Entails P (Q ⇒ R)%P -> Entails P R.
  Proof. unfold PValid, Entails, PAnd. intuition. Qed.

  Lemma pApply {w} {P Q R : Pred w} :
    Entails P Q -> Entails Q R -> Entails P R.
  Proof. apply transitivity. Qed.

  Lemma pApply_r {w} {P Q R : Pred w} :
    Entails Q R -> Entails P Q -> Entails P R.
  Proof. intros; etransitivity; eauto. Qed.

  Lemma pIntro {w} {P Q : Pred w} :
    Entails P Q -> PValid (P ⇒ Q).
  Proof. now unfold PValid, Entails, PImpl. Qed.

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

  (* A type class for things that can be interpreted as a predicate. *)
  Class InstPred (A : TYPE) :=
    instpred : ⊢ A -> Pred.

  #[export] Instance instpred_option {A} `{ipA : InstPred A} :
    InstPred (Option A) :=
    fun w o => match o with Some p => instpred p | None => PFalse end.
  #[export] Instance instpred_list {A} `{ipA : InstPred A} :
    InstPred (List A) :=
    fun w =>
      fix ip xs {struct xs} :=
      match xs with
      | nil       => PTrue
      | cons y ys => PAnd (instpred y) (ip ys)
      end.

  Notation Expr := (Lifted expr).

  Definition TPB : ⊢ Env -> Const expr -> Ty -> Expr -> Pred :=
    fun w G e t ee ι => inst G ι |-- e ; inst t ι ~> inst ee ι.
  #[global] Arguments TPB [w] G e t ee ι.
  Notation "G |-- E ; T ~> EE" := (TPB G E T EE) : pred_scope.

  Module Acc.
    Import (hints) Sub.
    Section WithAccessibilityRelation.
      Context {R : ACC} {instR : forall w, Inst (R w) (Assignment w)}.

      Definition wp {w0 w1} (r01 : R w0 w1) (Q : Pred w1) : Pred w0 :=
        fun ι0 => exists (ι1 : Assignment w1), inst r01 ι1 = ι0 /\ Q ι1.
      Definition wlp {w0 w1} (r01 : R w0 w1) (Q : Pred w1) : Pred w0 :=
        fun ι0 => forall (ι1 : Assignment w1), inst r01 ι1 = ι0 -> Q ι1.

      #[local] Arguments wp {_ _} _ _ _/.
      #[local] Arguments wlp {_ _} _ _ _/.
      #[local] Arguments PAnd {_} _ _ _/.
      #[local] Arguments PImpl {_} _ _ _/.
      #[local] Arguments Ext {_ _} [w] _ [_] _ _/.
      #[local] Arguments PEq [w] _ _ _/.

      #[export] Instance proper_wp_bientails {w0 w1} (r01 : R w0 w1) :
        Proper (BiEntails ==> BiEntails) (@wp w0 w1 r01).
      Proof.
        intros p q pq ι. cbn. apply ex_iff_morphism.
        intros ι1. apply and_iff_morphism. easy. apply pq.
      Qed.

      #[export] Instance proper_wp_entails {w0 w1} (r01 : R w0 w1) :
        Proper (Entails ==> Entails) (@wp w0 w1 r01).
      Proof.
        intros p q pq ι. cbn. intros (ι0 & Heq & HP).
        exists ι0. split. easy. now apply pq.
      Qed.

      #[export] Instance proper_wlp_bientails {w0 w1} (r01 : R w0 w1) :
        Proper (BiEntails ==> BiEntails) (@wlp w0 w1 r01).
      Proof.
        intros p q pq ι. cbn. apply all_iff_morphism. intros ι1.
        now apply iff_iff_iff_impl_morphism.
      Qed.

      #[export] Instance proper_wlp_entails {w0 w1} (r01 : R w0 w1) :
        Proper (Entails ==> Entails) (@wlp w0 w1 r01).
      Proof. intros P Q HPQ ι HP ι0 Heq. now apply HPQ, HP. Qed.

      Lemma wp_refl {reflR : Refl R} {instReflR : InstRefl R}
        {w} (Q : Pred w) : wp refl Q ⊣⊢ Q.
      Proof.
        split; cbn.
        - intros (ι' & Heq & HQ). rewrite inst_refl in Heq. now subst.
        - intros HQ. exists ι. split. now rewrite inst_refl. easy.
      Qed.

      Lemma wp_trans {transR : Trans R}
        {w0 w1 w2} (r01 : R w0 w1) (r12 : R w1 w2) Q :
        wp (r01 ⊙ r12) Q ⊣⊢ wp r01 (wp r12 Q).
      Proof.
        split; cbn.
        - intros (ι2 & Heq & HQ). rewrite inst_trans in Heq.
          exists (inst r12 ι2). split. easy. now exists ι2.
        - intros (ι1 & Heq1 & ι2 & Heq2 & HQ). exists ι2.
          split; [|easy]. rewrite inst_trans. congruence.
      Qed.

      Lemma wp_false {w0 w1} (r01 : R w0 w1) :
        wp r01 PFalse ⊣⊢ PFalse.
      Proof. firstorder. Qed.

      Lemma and_wp_l {w0 w1} (r01 : R w0 w1) P Q :
        wp r01 P ∧ Q ⊣⊢ wp r01 (P ∧ Ext Q r01).
      Proof.
        split; cbn.
        - intros [(ι1 & <- & HP) HQ]. now exists ι1.
        - intros (ι1 & <- & HP & HQ). split; [|easy]. now exists ι1.
      Qed.

      Lemma and_wp_r {w0 w1} (r01 : R w0 w1) P Q :
        P ∧ wp r01 Q ⊣⊢ wp r01 (Ext P r01 ∧ Q).
      Proof. now rewrite pand_comm, and_wp_l, pand_comm. Qed.

      Lemma wp_thick {thickR : Thick R} {instThickR : InstThick R}
        {w x} (xIn : ctx.In x w) (t : Ty (ctx.remove xIn)) Q :
        Entails ((Ty_hole xIn ≃ thin xIn t) ∧ wlp (thick x t) Q)%P (wp (thick x t) Q).
      Proof.
        intros ι. cbn. intros [Heq HQ].
        exists (env.remove _ ι xIn).
        rewrite inst_thick.
        rewrite Sub.subst_thin in Heq.
        rewrite inst_persist_ty in Heq.
        rewrite Sub.inst_thin in Heq.
        rewrite <- Heq.
        rewrite env.insert_remove.
        split. easy. apply HQ.
        rewrite inst_thick.
        rewrite <- Heq.
        now rewrite env.insert_remove.
      Qed.

      Lemma wlp_refl {reflR : Refl R} {instReflR : InstRefl R}
        {w} (Q : Pred w) : wlp refl Q ⊣⊢ Q.
      Proof.
        split; cbn.
        - intros HQ. apply HQ. now rewrite inst_refl.
        - intros HQ ? <-. now rewrite inst_refl in HQ.
      Qed.

      Lemma wlp_trans {transR : Trans R}
        {w0 w1 w2} (r01 : R w0 w1) (r12 : R w1 w2) Q :
        wlp (r01 ⊙ r12) Q ⊣⊢ wlp r01 (wlp r12 Q).
      Proof.
        split; cbn.
        - intros HQ ι1 Heq1 ι2 Heq2. apply HQ.
          subst. now rewrite inst_trans.
        - intros HQ ι2 Heq. rewrite inst_trans in Heq.
          now apply (HQ (inst r12 ι2)).
      Qed.

      Lemma wlp_true {w0 w1} (r01 : R w0 w1) :
        wlp r01 PTrue ⊣⊢ PTrue.
      Proof. firstorder. Qed.

      Lemma wlp_impl {w0 w1} (r01 : R w0 w1) P Q :
        Entails (wlp r01 (P ⇒ Q)) (wlp r01 P ⇒ wlp r01 Q)%P.
      Proof. intros ι0. cbn. intros HPQ HP ι1 <-. firstorder. Qed.

      Lemma entails_wlp {w0 w1} (r01 : R w0 w1) P Q :
        Entails (Ext P r01) Q -> Entails P (wlp r01 Q).
      Proof. intros HPQ ι0 HP ι1 <-. revert HP. apply HPQ. Qed.

      Lemma pvalid_wlp {w0 w1} (r01 : R w0 w1) Q :
        PValid Q -> PValid (wlp r01 Q).
      Proof. unfold PValid; cbn. firstorder. Qed.

    End WithAccessibilityRelation.
    (* #[global] Opaque wp. *)
    (* #[global] Opaque wlp. *)
  End Acc.

  Lemma pno_cycle {w x} (xIn : ctx.In x w) (t : Ty w) :
    Ty_subterm (Ty_hole xIn) t ->
    Entails (Ty_hole xIn ≃ t)%P PFalse.
  Proof.
    intros Hsub ι Heq.
    apply (inst_subterm ι) in Hsub. cbn in Hsub.
    rewrite <- Heq in Hsub. now apply ty_no_cycle in Hsub.
  Qed.

  (* #[global] Opaque BiEntails Entails PAnd PImpl PEq. *)

End Pred.
Export Pred (Pred).

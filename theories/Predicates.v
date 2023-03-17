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
    #[export] Instance proper_pimpl_bientails : Proper (BiEntails ==> BiEntails ==> BiEntails) PImpl.
    Proof. firstorder. Qed.
    #[export] Instance proper_pimpl_entails : Proper (Entails --> Entails ==> Entails) PImpl.
    Proof. firstorder. Qed.
    #[export] Instance proper_pand_bientails : Proper (BiEntails ==> BiEntails ==> BiEntails) PAnd.
    Proof. firstorder. Qed.
    #[export] Instance proper_pand_entails : Proper (Entails ==> Entails ==> Entails) PAnd.
    Proof. firstorder. Qed.

  End Connectives.
  #[global] Arguments BiEntails {w} (_ _)%P.
  #[global] Arguments Entails {w} (_ _)%P.
  #[global] Arguments PAnd {_} _ _ _/.
  #[global] Arguments PImpl {_} _ _ _/.
  #[global] Arguments PFalse {_} _/.

  Definition Forall {I : TYPE} : ⊢ (I -> Pred) -> Pred :=
    fun w A ι => forall i : I w, A i ι.
  Definition Exists {I : TYPE} : ⊢ (I -> Pred) -> Pred :=
    fun w A ι => exists i : I w, A i ι.
  #[global] Arguments Forall {I w} A ι.
  #[global] Arguments Exists {I w} A ι.

  #[local] Notation "⊩ P" := (PValid P) (at level 95).
  #[local] Notation "P ⊣⊢ Q" := (BiEntails P Q) (at level 95).
  #[local] Notation "⊤" := PTrue : pred_scope.
  #[local] Notation "⊥" := PFalse : pred_scope.
  #[local] Notation "P ⇔ Q" := (PIff P Q) (at level 94) : pred_scope.
  #[local] Notation "P ⇒ Q" := (PImpl P Q) (at level 94, right associativity) : pred_scope.
  #[local] Notation "P ∧ Q" := (PAnd P Q) (at level 80, right associativity) : pred_scope.

  Lemma pimpl_and_adjoint {w} (P Q R : Pred w) :
    Entails (P ∧ Q) R <-> Entails P (Q ⇒ R).
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
  Lemma pimpl_false_l {w} (P : Pred w) : ⊥ ⇒ P ⊣⊢ ⊤.
  Proof. unfold BiEntails, PImpl, PTrue, PFalse. intuition. Qed.
  Lemma entails_false {w} (P : Pred w) : Entails PFalse P.
  Proof. easy. Qed.
  Lemma entails_true {w} (P : Pred w) : Entails P PTrue.
  Proof. easy. Qed.

  Lemma pPoseProof {w} {P Q R : Pred w} :
    PValid Q -> Entails (P ∧ Q) R -> Entails P R.
  Proof. unfold PValid, Entails, PAnd. intuition. Qed.

  Lemma pGeneralize {w} {P Q R : Pred w} :
    PValid Q -> Entails P (Q ⇒ R) -> Entails P R.
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

    Lemma ext_false {w0 w1} (ζ01 : R w0 w1) :
      Ext PFalse ζ01 ⊣⊢ PFalse.
    Proof. unfold BiEntails, Ext, PFalse. reflexivity. Qed.

    Lemma ext_true {w0 w1} (ζ01 : R w0 w1) :
      Ext PTrue ζ01 ⊣⊢ PTrue.
    Proof. unfold BiEntails, Ext, PTrue. reflexivity. Qed.

  End Ext.
  #[global] Arguments Ext {_ _} [w] _ [_] _ _/.
  #[global] Instance params_ext : Params (@Ext) 6 := {}.

  Section Eq.

    Context {T : TYPE} {A : Type} {instTA : Inst T A}.

    Definition PEq : ⊢ T -> T -> Pred :=
      fun w t1 t2 ι => inst t1 ι = inst t2 ι.
    #[local] Infix "=" := PEq : pred_scope.

    Lemma peq_refl {w} (t : T w) :
      PEq t t ⊣⊢ ⊤.
    Proof. easy. Qed.

    Lemma peq_symmetry {w} (s t : T w) :
      PEq s t ⊣⊢ PEq t s.
    Proof. easy. Qed.

    Lemma peq_persist {R : ACC} {persR : Persistent R T}
      (instR : forall w : World, Inst (R w) (Assignment w))
      {w0 w1} (r : R w0 w1) (t1 t2 : T w0) :
      PEq (persist _ t1 _ r) (persist _ t2 _ r) ⊣⊢ Ext (PEq t1 t2) r.
    Proof.
      unfold BiEntails, PEq, Ext. intros ι.
      (* now rewrite !inst_persist. *)
    Admitted.

  End Eq.
  #[global] Arguments PEq {T A _} [w] _ _ _/.
  #[local] Infix "=" := PEq : pred_scope.

  Lemma peq_ty_noconfusion {w} (t1 t2 : Ty w) :
    t1 = t2 ⊣⊢
      match t1 , t2 with
      | Ty_bool         , Ty_bool         => PTrue
      | Ty_func t11 t12 , Ty_func t21 t22 => PEq t11 t21 ∧ PEq t12 t22
      | Ty_hole _       , _               => PEq t1 t2
      | _               , Ty_hole _       => PEq t1 t2
      | _               , _               => PFalse
      end.
  Proof.
    intros ι; unfold PEq, PFalse, PTrue, PAnd; destruct t1, t2;
      cbn; try reflexivity; intuition congruence.
  Qed.

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
        {w x} (xIn : ctx.In x w) (t : Ty (ctx.remove xIn)) (Q : Pred (ctx.remove xIn))  :
        wp (thick x t) Q ⊣⊢ PEq (Ty_hole xIn) (thin xIn t) ∧ Ext Q (Sub.thin xIn).
      Proof.
        intros ι; cbn. rewrite Sub.subst_thin, inst_persist_ty, Sub.inst_thin.
        split.
        - intros (ι1 & Heq & HQ). subst.
          now rewrite inst_thick, env.remove_insert, env.lookup_insert.
        - intros [Heq HQ]. exists (env.remove x ι xIn).
          now rewrite inst_thick, <- Heq, env.insert_remove.
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

      Lemma wlp_thick {thickR : Thick R} {instThickR : InstThick R}
        {w x} (xIn : ctx.In x w) (t : Ty (ctx.remove xIn)) (Q : Pred (ctx.remove xIn))  :
        wlp (thick x t) Q ⊣⊢ PEq (Ty_hole xIn) (thin xIn t) ⇒ Ext Q (Sub.thin xIn).
      Proof.
        intros ι; cbn. rewrite Sub.subst_thin, inst_persist_ty, Sub.inst_thin.
        split; intros HQ.
        - specialize (HQ (env.remove x ι xIn)). intros Heq.
          rewrite inst_thick, <- Heq, env.insert_remove in HQ. auto.
        - intros ι1 Heq. subst.
          rewrite inst_thick, env.remove_insert, env.lookup_insert in HQ.
          now apply HQ.
      Qed.

    End WithAccessibilityRelation.
    (* #[global] Opaque wp. *)
    (* #[global] Opaque wlp. *)
  End Acc.

  Lemma pno_cycle {w x} (xIn : ctx.In x w) (t : Ty w) :
    Ty_subterm (Ty_hole xIn) t ->
    Entails (Ty_hole xIn = t) PFalse.
  Proof.
    intros Hsub ι Heq.
    apply (inst_subterm ι) in Hsub. cbn in Hsub.
    rewrite <- Heq in Hsub. now apply ty_no_cycle in Hsub.
  Qed.

  #[local] Notation Expr := (Sem expr).

  Definition TPB : ⊢ Env -> Const expr -> Ty -> Expr -> Pred :=
    fun w G e t ee ι => inst G ι |-- e ; inst t ι ~> inst ee ι.
  #[global] Arguments TPB [w] G e t ee ι/.

  (* #[global] Opaque BiEntails Entails PAnd PImpl PEq. *)

  Module Import notations.

    Notation "t1 ≃ t2" :=
      (PEq t1 t2) (at level 90) : pred_scope.
    Notation "'Fun' x => b" :=
      (fun w ζ x => b%P w ζ)
        (x binder, at level 100) : pred_scope.
    Notation "⊩ P" := (PValid P) (at level 95).
    Notation "P ⊣⊢ Q" := (BiEntails P Q) (at level 95).
    Notation "⊤" := PTrue : pred_scope.
    Notation "⊥" := PFalse : pred_scope.
    Notation "P ⇔ Q" := (PIff P Q) (at level 94) : pred_scope.
    Notation "P ⇒ Q" := (PImpl P Q) (at level 94, right associativity) : pred_scope.
    Notation "P ∧ Q" := (PAnd P Q) (at level 80, right associativity) : pred_scope.

    Notation "'∀' x ∶ T , Q" :=
      (@Forall T _ (fun x => Q%P))
        (at level 99, x binder, x at next level, T at level 95,
          right associativity,
          format "'∀'  x  ∶  T ,  Q")
      : pred_scope.

    Notation "'∀⁺' x .. y , Q " :=
      (Forall (fun x => .. (Forall (fun y => Q%P)) ..))
        (at level 99, x binder, y binder, right associativity,
        only parsing)
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

    Notation "G |-- E ; T ~> EE" := (TPB G E T EE) : pred_scope.

  End notations.

  (* A predicate-based induction scheme for the typing relation. *)
  Section InductionScheme.

    Context (P : ⊢ Env -> Const expr -> Ty -> Expr -> Pred).
    Context
      {pfalse : forall w, PValid (w := w)
         (∀ G ∶ Env, ∀ t ∶ Ty, ∀ e' ∶ Expr,
             PEq t Ty_bool ⇒
             PEq e' (S.pure v_false) ⇒
             P G v_false t e')%P }
      {ptrue : forall w, PValid (w := w)
         (∀ G ∶ Env, ∀ t ∶ Ty, ∀ e' ∶ Expr,
             PEq t Ty_bool ⇒
             PEq e' (S.pure v_true) ⇒
             P G v_true t e')%P }
      {pif : forall w, PValid (w := w)
         (∀⁺ G e1 e2 e3 e' e1' e2' e3' t,
             (G |-- e1; Ty_bool ~> e1') ⇒
             (G |-- e2; t ~> e2') ⇒
             (G |-- e3; t ~> e3') ⇒
             P G e1 Ty_bool e1' ⇒
             P G e2 t e2' ⇒
             P G e3 t e3' ⇒
             PEq e' (fun ι0 => e_if (e1' ι0) (e2' ι0) (e3' ι0)) ⇒
             P G (e_if e1 e2 e3) t e')%P }
      {pvar : forall w (G : Env w) x t e', PValid
         (PEq (resolve x G) (Some t) ⇒
          PEq e' (fun _ => e_var x) ⇒
          P G (e_var x) t e') }
      {pabsu : forall w (G : Env w) x t1 t2 t e1 e1' e',
        PValid
          ((cons (x, t1) G |-- e1; t2 ~> e1') ⇒
           P (cons (x, t1) G) e1 t2 e1' ⇒
           PEq t (Ty_func t1 t2) ⇒
           PEq e' (fun ι0 => e_abst x (inst t1 ι0) (e1' ι0)) ⇒
           P G (e_absu x e1) t e' )}
      {pabst : forall w (G : Env w) x t1 t2 e1 e1' e' t,
          PValid
            ((cons (x, lift t1 w) G |-- e1; t2 ~> e1') ⇒
             P (cons (x, lift t1 w) G) e1 t2 e1' ⇒
             PEq t (Ty_func (lift t1 w) t2) ⇒
             PEq e' (fun ι0 => e_abst x t1 (e1' ι0)) ⇒
             P G (e_abst x t1 e1) t e')}
      {papp : forall w (G : Env w) e1 t1 e1' e2 t2 e2' e',
          PValid
            ((G |-- e1; Ty_func t2 t1 ~> e1') ⇒
             (G |-- e2; t2 ~> e2') ⇒
             P G e1 (Ty_func t2 t1) e1' ⇒
             P G e2 t2 e2' ⇒
             PEq e' (fun ι0 => e_app (e1' ι0) (e2' ι0)) ⇒
             P G (e_app e1 e2) t1 e')%P }.

    Lemma TPB_ind w G (e : expr) (t : Ty w) (ee : Expr w) :
      Entails (G |-- e; t ~> ee)%P (P G e t ee).
    Proof.
      intros ι T. hnf in T.
      remember (inst G ι) as G'.
      remember (inst t ι) as t'.
      remember (inst ee ι) as ee'.
      revert HeqG' Heqt' Heqee'. revert G t ee. revert w ι.
      induction T; cbn; intros; subst.
      - apply pfalse; cbn; auto.
      - apply ptrue; cbn; auto.
      - specialize (IHT1 w ι G Ty_bool (fun _ => cnd') eq_refl eq_refl eq_refl).
        specialize (IHT2 w ι G t0      (fun _ => coq') eq_refl eq_refl eq_refl).
        specialize (IHT3 w ι G t0      (fun _ => alt') eq_refl eq_refl eq_refl).
        eapply pif; cbn; eauto; eauto.
      - apply pvar; cbn; auto.
        now rewrite resolve_inst in H.
      - specialize (IHT w ι (cons (v, lift vt _) G) (lift t _) (fun _ => e')).
        cbn in IHT. rewrite ?inst_lift in IHT.
        specialize (IHT eq_refl eq_refl eq_refl).
        eapply pabsu; cbn; eauto; rewrite ?inst_lift; eauto.
        change (@inst _ _ (@inst_sem expr) _ ?e ?ι) with (e ι); cbn.
        now rewrite inst_lift.
      - specialize (IHT w ι (cons (v, lift vt _) G) (lift t _) (fun _ => e')).
        cbn in IHT. rewrite ?inst_lift in IHT.
        specialize (IHT eq_refl eq_refl eq_refl).
        eapply pabst; cbn; eauto; rewrite ?inst_lift; eauto.
      - specialize (IHT1 w ι G (Ty_func (lift t2 _) t) (fun _ => e1')). cbn in IHT1.
        rewrite ?inst_lift in IHT1. specialize (IHT1 eq_refl eq_refl eq_refl).
        specialize (IHT2 w ι G (lift t2 _) (fun _ => e2')).
        rewrite ?inst_lift in IHT2. specialize (IHT2 eq_refl eq_refl eq_refl).
        eapply papp; cbn; eauto; rewrite ?inst_lift; eauto.
    Qed.

  End InductionScheme.

End Pred.
Export Pred (Pred).

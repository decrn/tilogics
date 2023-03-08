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
  Program.Tactics
  Relations.Relation_Definitions.
From Equations Require Import
  Equations.
From Em Require Import
  Context
  Definitions
  Environment
  LogicalRelation
  Prelude
  STLC
  Substitution
  Triangular
  Unification.

Import ctx.notations.
Import SigTNotations.

Set Implicit Arguments.

#[local] Arguments Ty_hole {Σ i} xIn.
#[local] Arguments Ty_bool {Σ}.
#[local] Arguments Ty_func {Σ}.
#[local] Open Scope indexed_scope.

Reserved Notation "w1 ⊒ w2" (at level 80).

#[local] Notation "□ A" := (Box Tri A) (at level 9, format "□ A", right associativity).
#[local] Notation "◇ A" := (DiamondT Tri id A) (at level 9, format "◇ A", right associativity).
#[local] Notation "? A" := (Option A) (at level 9, format "? A", right associativity).
#[local] Notation "◆ A" := (DiamondT Tri Option A) (at level 9, format "◆ A", right associativity).
#[local] Notation "A * B" := (Prod A B).
#[local] Notation "s [ ζ ]" :=
  (persist _ s _ ζ)
    (at level 8, left associativity,
      format "s [ ζ ]").

Module AssignmentPredicates.

  Import (hints) Tri.
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

  Definition Ext : ⊢ Pred -> □Pred :=
    fun w0 p w1 r ι => p (inst r ι).
  #[global] Arguments Ext [w] _%P [w1].
  #[global] Instance params_ext : Params (@Ext) 4 := {}.

  #[export] Instance proper_ext_bientails {w : World} :
    Proper (BiEntails ==> forall_relation (fun _ => eq ==> BiEntails)) (@Ext w).
  Proof. intros p q pq w1 ? ? ? ι; subst; apply pq. Qed.
  #[export] Instance proper_ext_entails {w : World} :
    Proper (Entails ==> forall_relation (fun _ => eq ==> Entails)) (@Ext w).
  Proof. intros p q pq w1 ? ? ? ι; subst; apply pq. Qed.

  Lemma ext_refl {w} (P : Pred w) :
    BiEntails (Ext P refl) P.
  Proof. unfold BiEntails, Ext. intros ι. now rewrite inst_refl. Qed.

  Lemma ext_trans {w0 w1 w2} (r1 : Tri w0 w1) (r2 : Tri w1 w2)
    (P : Pred w0) :
    BiEntails (Ext P (trans r1 r2)) (Ext (Ext P r1) r2).
  Proof. unfold BiEntails, Ext. intros ι. now rewrite inst_trans. Qed.

  Notation "⊩ P" := (PValid P) (at level 95).
  (* Notation "⊩ P" := (forall ι, P%P ι) (at level 95). *)

  #[global] Arguments BiEntails {w} (_ _)%P.
  Notation "P ⊣⊢ Q" := (BiEntails P Q) (at level 95).
  Notation "⊤" := PTrue : pred_scope.
  Notation "P ⇔ Q" := (PIff P Q) (at level 94) : pred_scope.
  Notation "P ⇒ Q" := (PImpl P Q) (at level 94, right associativity) : pred_scope.
  Notation "P ∧ Q" := (PAnd P Q) (at level 80, right associativity) : pred_scope.

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

  Definition PEq : ⊢ Ty -> Ty -> Pred :=
    fun w t1 t2 ι => inst t1 ι = inst t2 ι.
  Notation "t1 ≃ t2" := (PEq t1 t2) (at level 90) : pred_scope.

  Lemma peq_refl {w} (t : Ty w) :
    PEq t t ⊣⊢ ⊤.
  Proof. easy. Qed.

  Lemma peq_symmetry {w} (s t : Ty w) :
    PEq s t ⊣⊢ PEq t s.
  Proof. easy. Qed.

  Lemma peq_persist {w0 w1} (r : Tri w0 w1) (t1 t2 : Ty w0) :
    PEq (persist _ t1 _ r) (persist _ t2 _ r) ⊣⊢ Ext (PEq t1 t2) r.
  Proof.
    unfold BiEntails, PEq, Ext. intros ι.
    now rewrite !inst_persist_ty.
  Qed.

  Lemma peq_func {w} (s1 s2 t1 t2 : Ty w) :
    Ty_func s1 s2 ≃ Ty_func t1 t2 ⊣⊢ PEq s1 t1 ∧ PEq s2 t2.
  Proof. unfold PEq, PAnd, BiEntails. cbn. intuition congruence. Qed.

  Lemma pimpl_and_adjoint {w} (P Q R : Pred w) :
    (Entails (P ∧ Q)%P R) <-> (Entails P (Q ⇒ R)%P).
  Proof. unfold Entails, PAnd, PImpl. intuition. Qed.

  Lemma ext_and {w0 w1} (ζ01 : Tri w0 w1) (P Q : Pred w0) :
    Ext P ζ01 ∧ Ext Q ζ01 ⊣⊢ Ext (P ∧ Q) ζ01 .
  Proof. unfold BiEntails, Ext, PAnd. intuition. Qed.

  Lemma ext_impl {w0 w1} (ζ01 : Tri w0 w1) (P Q : Pred w0) :
    Ext P ζ01 ⇒ Ext Q ζ01 ⊣⊢ Ext (P ⇒ Q) ζ01 .
  Proof. unfold BiEntails, Ext, PAnd. intuition. Qed.

  Notation "'Fun' x => b" :=
    (fun w ζ x => b%P w ζ)
      (x binder, at level 100) : pred_scope.

  Definition PTri {w0 w1} (r : Tri w0 w1) : Pred w0 :=
    fun ι0 => exists ι1, ι0 = inst r ι1.

  #[global] Typeclasses Opaque Entails.
  #[global] Typeclasses Opaque BiEntails.

End AssignmentPredicates.

Module ProgramLogic.

  Import (hints) Tri.
  Import AssignmentPredicates.

  Definition WP {A} : ⊢ ◆A -> □(A -> Pred) -> Pred :=
    fun w0 d Q ι0 =>
      option.wp
        (fun '(w1; (ζ01, a)) =>
           exists (ι1 : Assignment w1),
             inst ζ01 ι1 = ι0 /\ Q w1 ζ01 a ι1) d.
  #[global] Arguments WP {A}%indexed_scope [w] _ _%P _.
  #[global] Instance params_wp : Params (@WP) 4 := {}.

  Lemma wp_pure {A w0} (a : A w0) (Q : □(A -> Pred) w0) :
    WP (η a) Q ⊣⊢ T Q a.
  Proof.
    unfold BiEntails, WP, η. intros ι0. rewrite option.wp_match.
    split.
    - intros (ι1 & e & HQ). now subst.
    - intros HQ. exists ι0. auto.
  Qed.

  Lemma wp_bind {A B w0} (d : ◆A w0) (f : □(A -> ◆B) w0) (Q : □(B -> Pred) w0) :
    WP (bind d f) Q ⊣⊢ WP d (fun w1 ζ1 a1 => WP (f w1 ζ1 a1) (_4 Q ζ1)).
  Proof.
    unfold BiEntails, WP, bind, acc. intros ι0.
    rewrite option.wp_bind.
    option.tactics.mixin.
    intros (w1 & ζ01 & a).
    rewrite option.wp_map.
    setoid_rewrite option.wp_match.
    destruct (f w1 ζ01 a) as [(w2 & ζ2 & b2)|]; [|firstorder].
    split.
    - intros (ι2 & e1 & HQ). subst. exists (inst ζ2 ι2).
      split; [rewrite inst_trans|]; firstorder.
    - intros (ι1 & e0 & ι2 & e1 & HQ). subst. exists ι2.
      split; [rewrite inst_trans|]; firstorder.
  Qed.

  Lemma wp_monotonic {A w} (d : ◆A w) (R : Pred w) (P Q : □(A -> Pred) w) :
    (forall w1 (r : w ⊒⁻ w1) (a : A w1), Entails (Ext R r) (P w1 r a ⇒ Q w1 r a)%P) ->
    Entails R (WP d P ⇒ WP d Q)%P.
  Proof.
    unfold Entails, PImpl, WP, Ext; intros pq ι HR.
    apply option.wp_monotonic.
    intros (w1 & ζ01 & a1) (ι1 & e1 & H).
    exists ι1; split; [assumption|].
    revert H; apply pq. now rewrite e1.
  Qed.

  #[export] Instance proper_wp_bientails {A w} :
    Proper
      (pointwise_relation _
         (forall_relation
            (fun _ => pointwise_relation _
                        (pointwise_relation _ BiEntails)) ==> BiEntails))
      (@WP A w).
  Proof.
    intros d p q pq. apply split_bientails;
      rewrite <- pand_true_l at 1;
      apply pimpl_and_adjoint, wp_monotonic;
      intros * ι _; unfold PImpl; apply pq.
  Qed.

  #[export] Instance proper_wp_entails {A w} :
    Proper
      (pointwise_relation _
         (forall_relation
            (fun _ => pointwise_relation _
                        (pointwise_relation _ Entails)) ==> Entails))
      (@WP A w).
  Proof.
    intros d p q pq. rewrite <- pand_true_l at 1.
    apply pimpl_and_adjoint, wp_monotonic.
    intros * ι _. unfold PImpl. apply pq.
  Qed.

  Definition WLP {A} : ⊢ ◆A -> □(A -> Pred) -> Pred :=
    fun w d Q ι0 =>
      option.wlp
        (fun '(w1; (ζ01, a)) =>
           forall ι1 : Assignment w1, inst ζ01 ι1 = ι0 -> Q w1 ζ01 a ι1)
        d.
  #[global] Arguments WLP {A}%indexed_scope [w] _ _%P _.

  Lemma wlp_pure {A w} (a : A w) (Q : □(A -> Pred) w) :
    WLP (η a) Q ⊣⊢ T Q a.
  Proof.
    unfold PIff, WLP, η, T. intros ι.
    rewrite option.wlp_match.
    split; intros; subst; auto.
  Qed.

  Lemma wlp_bind {A B w0} (d : ◆A w0) (f : □(A -> ◆B) w0) (Q : □(B -> Pred) w0) :
    WLP (bind d f) Q ⊣⊢ WLP d (fun _ ζ1 a1 => WLP (f _ ζ1 a1) (_4 Q ζ1)).
  Proof.
    unfold BiEntails, WLP, bind, acc. intros ι0.
    rewrite option.wlp_bind.
    option.tactics.mixin.
    intros (w1 & ζ01 & a).
    rewrite option.wlp_map.
    setoid_rewrite option.wlp_match.
    destruct (f w1 ζ01 a) as [(w2 & ζ2 & b2)|]; [|firstorder].
    split.
    - intros HQ ι1 e1 ι2 e2. subst. apply HQ, inst_trans.
    - intros HQ ι2 e2. subst. apply (HQ (inst ζ2 ι2)).
      now rewrite inst_trans. easy.
  Qed.

  Lemma wlp_monotonic {A w} (d : ◆A w) (R : Pred w) (P Q : □(A -> Pred) w) :
    (forall w1 (r : w ⊒⁻ w1) (a : A w1), Entails (Ext R r) (P w1 r a ⇒ Q w1 r a)%P) ->
    Entails R (WLP d P ⇒ WLP d Q)%P.
  Proof.
    unfold Entails, PImpl, WLP, Ext; intros pq ι HR.
    apply option.wlp_monotonic.
    intros (w1 & ζ01 & a1) H ι1 e1. specialize (H ι1 e1).
    revert H; apply pq. now rewrite e1.
  Qed.

  #[global] Instance params_wlp : Params (@WLP) 4 := {}.
  #[export] Instance proper_wlp_bientails {A w} :
    Proper
      (pointwise_relation _
         (forall_relation
            (fun _ => pointwise_relation _
                        (pointwise_relation _ BiEntails)) ==> BiEntails))
      (@WLP A w).
  Proof.
    intros d p q pq. apply split_bientails;
      rewrite <- pand_true_l at 1;
      apply pimpl_and_adjoint, wlp_monotonic;
      intros * ι _; unfold PImpl; apply pq.
  Qed.

  #[export] Instance proper_wlp_entails {A w} :
    Proper
      (pointwise_relation _
         (forall_relation
            (fun _ => pointwise_relation _
                        (pointwise_relation _ Entails)) ==> Entails))
      (@WLP A w).
  Proof.
    intros d p q pq. rewrite <- pand_true_l at 1.
    apply pimpl_and_adjoint, wlp_monotonic.
    intros * ι _. unfold PImpl. apply pq.
  Qed.

  Lemma wlp_tell1 {w x} (xIn : x ∈ w) (t : Ty (w - x)) (Q : □(Unit -> Pred) w) :
    PValid (WLP (tell1 xIn t) Q) <->
      PValid (Q _ (thick x t) tt).
  Proof.
    unfold PValid, WLP, tell1.
    split.
    - intros H ι. specialize (H (inst (thick (R := Tri) x t) ι)).
      rewrite option.wlp_match in H. apply (H ι eq_refl).
    - intros H ι. rewrite option.wlp_match. intros. apply H.
  Qed.

  Lemma pPoseProof {w} {P Q R : Pred w} :
    PValid Q -> Entails (P ∧ Q)%P R -> Entails P R.
  Proof. unfold PValid, Entails, PAnd. intuition. Qed.

  Lemma pGeneralize {w} {P Q R : Pred w} :
    PValid Q -> Entails P (Q ⇒ R)%P -> Entails P R.
  Proof. unfold PValid, Entails, PAnd. intuition. Qed.

  Lemma pApply {w} {P Q R : Pred w} :
    Entails P Q -> Entails Q R -> Entails P R.
  Proof. apply transitivity. Qed.

End ProgramLogic.

Module Correctness.

  Import (hints) Tri.
  Import AssignmentPredicates ProgramLogic.

  Definition UnifierSound : ⊢ Unifier -> PROP :=
    fun w0 u =>
      forall (t1 t2 : Ty w0),
        ⊩ WLP (u t1 t2) (Fun _ => Ext (t1 ≃ t2)).

  Definition UnifierComplete : ⊢ Unifier -> PROP :=
    fun w0 u =>
      forall (t1 t2 : Ty w0),
        ⊩ t1 ≃ t2 ⇒ WP (u t1 t2) (fun _ _ _ => PTrue).

  Definition BoxUnifierSound : ⊢ BoxUnifier -> PROP :=
    fun w0 bu =>
      forall (t1 t2 : Ty w0) (w1 : World) (ζ01 : w0 ⊒⁻ w1),
        ⊩ WLP (bu t1 t2 w1 ζ01) (Fun _ => Ext (Ext (t1 ≃ t2) ζ01)).

  Definition BoxUnifierComplete : ⊢ BoxUnifier -> PROP :=
    fun w0 bu =>
      forall (t1 t2 : Ty w0) (w1 : World) (ζ01 : w0 ⊒⁻ w1),
        Entails (Ext (t1 ≃ t2) ζ01) (WP (bu t1 t2 w1 ζ01) (fun _ _ _ => PTrue)).

  Section BoxedProofs.

    Import (hints) Sub.

    Context [w] (lmgu : ▷BoxUnifier w).
    Context (lmgu_sound : forall x (xIn : x ∈ w),
                BoxUnifierSound (lmgu xIn)).

    Lemma flex_sound_assignment {x} (xIn : x ∈ w) (t : Ty w) :
      ⊩ WLP (flex t xIn) (Fun _ => Ext (Ty_hole xIn ≃ t)).
    Proof.
      unfold flex. destruct (varview t) as [y yIn|].
      - destruct (ctx.occurs_check_view xIn yIn).
        + rewrite wlp_pure. unfold T. now rewrite ext_refl.
        + rewrite wlp_tell1, <- peq_persist. cbn. unfold thickIn.
          now rewrite ctx.occurs_check_view_refl, ctx.occurs_check_view_thin.
      - destruct (occurs_check_sound t xIn); subst; [|constructor].
        rewrite wlp_tell1, <- peq_persist, persist_thin_thick. cbn.
        unfold thickIn. now rewrite ctx.occurs_check_view_refl.
    Qed.

    Lemma boxflex_sound_assignment {x} (xIn : x ∈ w) (t : Ty w)
      {w1} (ζ01 : w ⊒⁻ w1) :
      ⊩ WLP (boxflex lmgu t xIn ζ01) (Fun _ => Ext (Ext (Ty_hole xIn ≃ t) ζ01)).
    Proof.
      unfold boxflex, Tri.box_intro_split.
      destruct ζ01 as [|w2 y yIn ty]; folddefs.
      - generalize (flex_sound_assignment xIn t).
        apply proper_pvalid_entails.
        apply proper_wlp_entails.
        intros w2 ζ2 _.
        now rewrite ext_refl.
      - generalize (lmgu_sound yIn (Ty_hole xIn)[thick y ty] t[thick y ty] ζ01). clear.
        apply proper_pvalid_entails.
        apply proper_wlp_entails.
        intros w3 ζ3 _.
        now rewrite ext_trans, peq_persist.
    Qed.

    Lemma boxmgu_sound_assignment : BoxUnifierSound (boxmgu lmgu).
    Proof.
      intros t1 t2. pattern (boxmgu lmgu t1 t2).
      apply boxmgu_elim; clear t1 t2.
      - intros. apply boxflex_sound_assignment.
      - intros. generalize (boxflex_sound_assignment xIn t ζ01).
        now apply proper_pvalid_entails, proper_wlp_entails.
      - intros *. now rewrite wlp_pure.
      - constructor.
      - constructor.
      - intros * IH1 IH2 *. rewrite wlp_bind.
        specialize (IH1 _ ζ01). revert IH1.
        apply proper_pvalid_entails, proper_wlp_entails.
        intros w2 ζ12 _. rewrite wlp_bind.
        apply (pGeneralize (IH2 _ (ζ01 ⊙ ζ12))), wlp_monotonic.
        intros ? ? _. rewrite wlp_pure. unfold T, _4.
        rewrite ?trans_refl_r, ?ext_trans, ?ext_impl.
        apply proper_ext_entails; auto.
        apply proper_ext_entails; auto.
        apply proper_ext_entails; auto.
        now rewrite peq_func.
    Qed.

    Context (lmgu_complete : forall x (xIn : x ∈ w),
                BoxUnifierComplete (lmgu xIn)).

    Lemma flex_complete_assignment {x} (xIn : x ∈ w) (t : Ty w) :
      Entails
        (Ty_hole xIn ≃ t)%P
        (WP (flex t xIn) (fun (w0 : World) (_ : w ⊒⁻ w0) (_ : Unit w0) => ⊤%P)).
    Proof.
      unfold flex. destruct (varview t) as [y yIn|].
      - destruct (ctx.occurs_check_view xIn yIn).
        + now rewrite wp_pure.
        + unfold Entails, WP, PEq, tell1; cbn. intros ι Heq.
          rewrite env.lookup_thin in Heq.
          rewrite option.wp_match.
          exists (env.remove _ ι xIn).
          split; [|easy].
          rewrite inst_thick. cbn.
          rewrite <- Heq.
          now rewrite env.insert_remove.
      - unfold Entails, PEq, WP, tell1; cbn; intros ι Heq.
        rewrite option.wp_match. destruct (occurs_check_spec xIn t); subst.
        + exists (env.remove _ ι xIn). split; [|easy].
          rewrite inst_thick.
          rewrite Sub.subst_thin in Heq.
          rewrite inst_persist_ty in Heq.
          rewrite Sub.inst_thin in Heq. rewrite <- Heq.
          now rewrite env.insert_remove.
        + destruct H0; [exact (H _ _ H0)|].
          apply (inst_subterm ι) in H0. cbn in H0. rewrite <- Heq in H0.
          now apply ty_no_cycle in H0.
    Qed.

    Lemma boxflex_complete_assignment {x} (xIn : x ∈ w) (t : Ty w) {w1} (ζ01 : w ⊒⁻ w1) :
      Entails
        (Ext (Ty_hole xIn ≃ t) ζ01)
        (WP (boxflex lmgu t xIn ζ01) (fun (w0 : World) (_ : w1 ⊒⁻ w0) (_ : Unit w0) => ⊤%P)).
    Proof.
      unfold boxflex, Tri.box_intro_split.
      destruct ζ01 as [|w2 y yIn ty].
      - rewrite ext_refl. apply flex_complete_assignment.
      - change (Tri.cons ?x ?t ?r) with (thick x t ⊙ r).
        rewrite ext_trans, <- peq_persist.
        now apply (lmgu_complete yIn).
    Qed.

    Lemma boxmgu_complete_assignment : BoxUnifierComplete (boxmgu lmgu).
    Proof.
      intros t1 t2. pattern (boxmgu lmgu t1 t2).
      apply boxmgu_elim; clear t1 t2.
      - intros. apply boxflex_complete_assignment.
      - intros. rewrite peq_symmetry. apply boxflex_complete_assignment.
      - intros *. now rewrite wp_pure.
      - cbn; discriminate.
      - cbn; discriminate.
      - intros * IH1 IH2 *.
        rewrite wp_bind, peq_func.
        rewrite <- ext_and.
        apply pimpl_and_adjoint.
        apply (pApply (IH1 w1 ζ01)). clear IH1.
        apply pimpl_and_adjoint.
        rewrite pand_comm.
        apply pimpl_and_adjoint.
        apply wp_monotonic. intros.
        rewrite pimpl_true_l.
        rewrite wp_bind.
        rewrite <- ext_trans.
        apply (pApply (IH2 _ _)).
        apply proper_wp_entails. intros ? ? _.
        rewrite wp_pure. unfold _4, T.
        reflexivity.
    Qed.

  End BoxedProofs.

End Correctness.

Module Generalized.

  Import (hints) Sub Tri.
  Import AssignmentPredicates ProgramLogic LR.

  Definition RPred : LR.RELATION Pred :=
    fun w0 w1 r P Q => forall ι, P (inst r ι) <-> Q ι.

  Lemma wlp_tell' {w x} (xIn : x ∈ w) (t : Ty (w - x)) (Q : □(Unit -> Pred) w)
    (RQ : RProper (RBox (RImpl RUnit RPred)) Q) :
    WLP (tell1 xIn t) Q ⊣⊢ (t[Sub.thin xIn] ≃ Ty_hole xIn ⇒ T Q tt).
  Proof.
    unfold BiEntails, WLP, PEq, PImpl, tell1, T. intros ι.
    rewrite option.wlp_match. cbn. split.
    - intros HQ Heq.
      rewrite inst_persist_ty, Sub.inst_thin in Heq.
      specialize (HQ (env.remove _ ι xIn)).
      rewrite Heq, env.insert_remove in HQ.
      specialize (HQ eq_refl). revert HQ.
      hnf in RQ.
      unfold RImpl, RUnit, RPred in RQ.
      specialize (RQ _ _ refl (thick x t) (thick x t) eq_refl tt tt I).
      specialize (RQ (env.remove x ι xIn)).
      rewrite inst_thick, Heq, env.insert_remove in RQ.
      apply RQ.
    - intros HQ ι1 Heq. subst.
      rewrite inst_persist_ty in HQ.
      rewrite Sub.inst_thin in HQ.
      rewrite env.remove_insert in HQ.
      rewrite env.lookup_insert in HQ.
      specialize (HQ eq_refl). revert HQ.
      hnf in RQ.
      unfold RImpl, RUnit, RPred in RQ.
      specialize (RQ _ _ refl (thick x t) (thick x t) eq_refl tt tt I).
      specialize (RQ ι1).
      rewrite inst_thick in RQ.
      apply RQ.
  Qed.

  Lemma flex_sound_assignment' {w x} (xIn : x ∈ w) (t : Ty w)
    (Q : □(Unit -> Pred) w) (RQ : RProper (RBox (RImpl RUnit RPred)) Q) :
    WLP (flex t xIn) Q ⊣⊢ (t ≃ Ty_hole xIn) ⇒ T Q tt.
  Proof.
    unfold flex. destruct (varview t) as [y yIn|].
    - destruct (ctx.occurs_check_view xIn yIn).
      + now rewrite wlp_pure, peq_refl, pimpl_true_l.
      + rewrite wlp_tell'; auto. cbn.
        now rewrite Sub.lk_thin.
    - unfold PValid, WLP, PEq, PImpl. intros ι. rewrite option.wlp_match.
      destruct (occurs_check_spec xIn t); cbn; subst.
      + split.
        * intros HQ Heq. specialize (HQ (env.remove _ ι xIn)).
          rewrite Sub.subst_thin, inst_persist_ty, Sub.inst_thin in Heq.
          rewrite Heq in HQ. rewrite env.insert_remove in HQ.
          specialize (HQ eq_refl). revert HQ. unfold T.
          specialize (RQ _ _ refl (thick x a) (thick x a) eq_refl tt tt I).
          specialize (RQ (env.remove x ι xIn)).
          rewrite inst_thick, Heq, env.insert_remove in RQ.
          apply RQ.
        * intros Heq ι1 <-.
          rewrite Sub.subst_thin, inst_persist_ty, Sub.inst_thin in Heq.
          rewrite env.remove_insert, env.lookup_insert in Heq.
          specialize (Heq eq_refl). revert Heq. unfold T.
          specialize (RQ _ _ refl (thick x a) (thick x a) eq_refl tt tt I).
          specialize (RQ ι1). rewrite inst_thick in RQ.
          apply RQ.
      + destruct H0.
        * destruct (H _ _ H0).
        * split; auto. intros _ Heq. exfalso.
          apply (inst_subterm ι) in H0. rewrite Heq in H0.
          now apply ty_no_cycle in H0.
  Qed.

End Generalized.

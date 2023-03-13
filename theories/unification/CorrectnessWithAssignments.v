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
  Predicates
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

Module ProgramLogic.

  Import (hints) Tri.
  Import Pred.

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

  Lemma pApply_r {w} {P Q R : Pred w} :
    Entails Q R -> Entails P Q -> Entails P R.
  Proof. intros; etransitivity; eauto. Qed.

  Lemma pIntro {w} {P Q : Pred w} :
    Entails P Q -> PValid (P ⇒ Q).
  Proof. now unfold PValid, Entails, PImpl. Qed.

End ProgramLogic.

Module Correctness.

  Import (hints) Tri.
  Import Pred ProgramLogic.

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
      destruct ζ01 as [|w2 y yIn ty]; folddefs.
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

  Lemma bmgu_sound w : @BoxUnifierSound w (@bmgu w).
  Proof.
    pattern (@bmgu w). revert w. apply Löb_elim.
    intros w IH. now apply boxmgu_sound_assignment.
  Qed.

  Lemma bmgu_complete {w} : @BoxUnifierComplete w (@bmgu w).
  Proof.
    pattern (@bmgu w). revert w. apply Löb_elim.
    intros w IH. now apply boxmgu_complete_assignment.
  Qed.

  Definition mgu_sound w : UnifierSound (@mgu w).
  Proof.
    unfold UnifierSound, mgu. intros t1 t2.
    generalize (bmgu_sound t1 t2 refl).
    apply proper_pvalid_entails, proper_wlp_entails.
    intros w' r _. now rewrite ext_refl.
  Qed.

  Definition mgu_complete w : UnifierComplete (@mgu w).
  Proof.
    unfold UnifierComplete, mgu. intros t1 t2. apply pIntro.
    apply (pApply_r (@bmgu_complete _ t1 t2 _ refl)).
    now rewrite ext_refl.
  Qed.

  Import Pred.

  #[local] Instance instpred_prod_ty : InstPred (Prod Ty Ty) :=
    fun w '(t1,t2) => PEq t1 t2.

  Definition BoxSolveListSound : ⊢ BoxSolveList -> PROP :=
    fun w0 bsl =>
      forall (C : List (Prod Ty Ty) w0) (w1 : World) (ζ01 : w0 ⊒⁻ w1),
        ⊩ WLP (bsl C w1 ζ01) (Fun _ => Ext (Ext (instpred C) ζ01)).

  Definition SolveListSound : ⊢ SolveList -> PROP :=
    fun w0 sl =>
      forall (C : List (Prod Ty Ty) w0),
        ⊩ WLP (sl C) (Fun _ => Ext (instpred C)).

  Definition BoxSolveListComplete : ⊢ BoxSolveList -> PROP :=
    fun w0 bsl =>
      forall (C : List (Prod Ty Ty) w0) (w1 : World) (ζ01 : w0 ⊒⁻ w1),
        Entails (Ext (instpred C) ζ01) (WP (bsl C w1 ζ01) (fun _ _ _ => PTrue)).

  Definition SolveListComplete : ⊢ SolveList -> PROP :=
    fun w0 sl =>
      forall (C : List (Prod Ty Ty) w0),
        Entails (instpred C) (WP (sl C) (fun _ _ _ => PTrue)).

  Lemma boxsolvelist_sound {w} : BoxSolveListSound (boxsolvelist (w := w)).
  Proof.
    intros C. induction C as [|[t1 t2]]; cbn; intros.
    - rewrite wlp_pure. unfold T. now rewrite ext_refl.
    - rewrite wlp_bind. generalize (bmgu_sound t1 t2 ζ01).
      apply proper_pvalid_entails, proper_wlp_entails.
      intros w2 r2 _. apply (pGeneralize (IHC _ (ζ01 ⊙⁻ r2))).
      apply wlp_monotonic. unfold _4. intros w3 r3 _.
      rewrite ?trans_refl_r, ?ext_trans, ?ext_impl.
      apply proper_ext_entails; auto.
      apply proper_ext_entails; auto.
      apply proper_ext_entails; auto.
      now apply pimpl_and_adjoint.
  Qed.

  Lemma solvelist_sound {w} : SolveListSound (solvelist (w := w)).
  Proof.
    unfold SolveListSound, solvelist. intros C.
    generalize (boxsolvelist_sound C refl).
    apply proper_pvalid_entails, proper_wlp_entails.
    intros w' r _. now rewrite ext_refl.
  Qed.

  Lemma boxsolvelist_complete {w} : BoxSolveListComplete (boxsolvelist (w := w)).
  Proof.
    intros C. induction C as [|[t1 t2]]; cbn; intros.
    - rewrite wp_pure. unfold T. easy.
    - rewrite wp_bind. rewrite <- ext_and.
      apply pimpl_and_adjoint.
      apply (pApply (@bmgu_complete _ t1 t2 _ ζ01)).
      apply pimpl_and_adjoint.
      rewrite pand_comm.
      apply pimpl_and_adjoint.
      apply wp_monotonic. intros.
      rewrite pimpl_true_l, <- ext_trans.
      apply IHC.
  Qed.

  Lemma solvelist_complete {w} : SolveListComplete (solvelist (w := w)).
  Proof.
    unfold SolveListComplete, solvelist. intros C.
    apply (pApply_r (@boxsolvelist_complete _ C _ refl)).
    now rewrite ext_refl.
  Qed.

  Definition wp_prenex {A} : ⊢ ?◇⁺(List (Ty * Ty) * A) -> □⁺(A -> Pred) -> Pred :=
    fun w o Q =>
      fun ι =>
      option.wp (fun '(w'; (r, (C, a))) =>
          exists ι', inst r ι' = ι /\ instpred C ι' /\ Q w' r a ι') o.

  Lemma prenex_correct {A w} (m : FreeM A w) (Q : □⁺(A -> Pred) w) :
    forall ι,
      wp_prenex (prenex m) Q ι <-> STLC.WP m Q ι.
  Proof.
    unfold wp_prenex.
    induction m; intros ι; cbn.
    - rewrite option.wp_match. unfold T. firstorder. now subst.
    - rewrite option.wp_match. reflexivity.
    - rewrite <- IHm. clear IHm.
      rewrite option.wp_bind. do 2 rewrite option.wp_match.
      destruct (prenex m) as [(w' & r & C & a)|]; [|easy].
      rewrite option.wp_match. cbn. unfold PAnd, PEq.
      firstorder; subst.
      + now rewrite <- ?inst_persist_ty.
      + exists x. now rewrite ?inst_persist_ty.
    - setoid_rewrite <- IHm. clear IHm.
      rewrite option.wp_bind. repeat setoid_rewrite option.wp_match.
      destruct (prenex m) as [(w' & r & C & a)|]; [|firstorder].
      rewrite option.wp_match. cbn. unfold PAnd, PEq, _4.
      split.
      + intros (ι' & Heq & HC & HQ). subst. remember (inst r ι') as ι.
        destruct (Environment.env.view ι).
        exists v. exists ι'. rewrite Heqι. auto.
      + intros (t & ι' & Heq & HC & HQ).
        exists ι'. rewrite Heq. cbn. auto.
  Qed.

  Definition wp_optiondiamond {A} : ⊢ ?◇⁺ A -> □⁺(A -> Pred) -> Pred.
  Proof.
    intros w m Q ι.
    refine (option.wp _ m).
    intros (w1 & r1 & a1).
    refine (exists ι1, inst r1 ι1 = ι /\ Q _ r1 a1 ι1).
  Defined.

  Lemma solvefree_equiv {A} {pA : Persistent Tri.Tri A}
    (m : FreeM A ctx.nil) (Q : □⁺(A -> Pred) [ctx]) :
    wp_optiondiamond (solvefree m) Q ⊣⊢ STLC.WP m Q.
  Proof.
    intros ι. unfold wp_optiondiamond, solvefree.
    rewrite option.wp_bind, <- prenex_correct.
    unfold wp_prenex. apply option.wp_proper.
    intros (w1 & r1 & C & a).
    rewrite option.wp_bind.
    pose proof (solvelist_complete C) as Hcompl.
    pose proof (solvelist_sound C) as Hsound.
    rewrite option.wp_match.
    destruct solvelist as [(w2 & r2 & [])|].
    - rewrite option.wp_match. split.
      + intros (ι2 & Heq & HQ); subst.
        exists (inst r2 ι2). specialize (Hsound (inst r2 ι2)).
        unfold WLP, Ext in Hsound. rewrite option.wlp_match in Hsound.
        specialize (Hsound ι2 eq_refl). repeat split.
        * destruct (env.view (inst r1 (inst r2 ι2))).
          destruct (env.view (inst alloc.nil_l ι2)).
          reflexivity.
        * assumption.
        * clear - HQ. admit.
      + intros (ι1 & Heq1 & HC & HQ).
        specialize (Hcompl ι1 HC). unfold WP in Hcompl.
        rewrite option.wp_match in Hcompl. destruct Hcompl as (ι2 & Heq2 & _).
        exists ι2. split. subst.
        * destruct (env.view (inst r1 (inst r2 ι2))).
          destruct (env.view (inst alloc.nil_l ι2)).
          reflexivity.
        * clear - HQ. admit.
    - split; [easy|]. intros (ι1 & Heq1 & HC & HQ).
      specialize (Hcompl ι1 HC). unfold WP in Hcompl.
      now rewrite option.wp_match in Hcompl.
  Admitted.

End Correctness.

Module Generalized.

  Import (hints) Sub Tri.
  Import Pred ProgramLogic LR.

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

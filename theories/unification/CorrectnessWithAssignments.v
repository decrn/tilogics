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
  Import Pred.notations.

  Definition WP {A} : ⊢ ◆A -> □(A -> Pred) -> Pred :=
    fun w0 d Q =>
      match d with
      | Some (w1; (r01, a)) => Acc.wp r01 (Q w1 r01 a)
      | None                => PFalse
      end.

  #[global] Arguments WP {A}%indexed_scope [w] _ _%P _.
  #[global] Instance params_wp : Params (@WP) 4 := {}.

  #[export] Instance proper_wp_bientails {A w} :
    Proper
      (pointwise_relation _
         (forall_relation
            (fun _ => pointwise_relation _
                        (pointwise_relation _ BiEntails)) ==> BiEntails))
      (@WP A w).
  Proof.
    intros d p q pq. destruct d as [(w1 & r01 & a)|]; cbn; [|easy].
    apply Acc.proper_wp_bientails. apply pq.
  Qed.

  #[export] Instance proper_wp_entails {A w} :
    Proper
      (pointwise_relation _
         (forall_relation
            (fun _ => pointwise_relation _
                        (pointwise_relation _ Entails)) ==> Entails))
      (@WP A w).
  Proof.
    intros d p q pq. destruct d as [(w1 & r01 & a)|]; cbn; [|easy].
    apply Acc.proper_wp_entails. apply pq.
  Qed.

  Lemma wp_monotonic' {A w} (d : ◆A w) (R : Pred w) (P Q : □(A -> Pred) w) :
    (forall w1 (r : w ⊒⁻ w1) (a : A w1),
        Entails (Ext R r) (P w1 r a ⇒ Q w1 r a)%P) ->
    Entails R (WP d P ⇒ WP d Q)%P.
  Proof.
    intros pq. destruct d as [(w1 & r01 & a)|]; cbn.
    - specialize (pq w1 r01 a).
      apply pimpl_and_adjoint.
      rewrite Acc.and_wp_r.
      apply Acc.proper_wp_entails.
      apply pimpl_and_adjoint.
      apply pq.
    - apply pimpl_and_adjoint.
      now rewrite pand_false_r.
  Qed.

  Lemma wp_pure {A w0} (a : A w0) (Q : □(A -> Pred) w0) :
    WP (η a) Q ⊣⊢ T Q a.
  Proof. unfold WP, η. now rewrite Acc.wp_refl. Qed.

  Lemma wp_bind {A B w0} (d : ◆A w0) (f : □(A -> ◆B) w0) (Q : □(B -> Pred) w0) :
    WP (bind d f) Q ⊣⊢ WP d (fun w1 ζ1 a1 => WP (f w1 ζ1 a1) (_4 Q ζ1)).
  Proof.
    destruct d as [(w1 & r01 & a)|]; cbn; [|reflexivity].
    destruct (f w1 r01 a) as [(w2 & r12 & b2)|]; cbn;
      now rewrite ?Acc.wp_trans, ?Acc.wp_false.
  Qed.

  Definition WLP {A} : ⊢ ◆A -> □(A -> Pred) -> Pred :=
    fun w0 d Q =>
      match d with
      | Some (w1; (r01, a)) => Pred.Acc.wlp r01 (Q w1 r01 a)
      | None                => PTrue
      end.
  #[global] Arguments WLP {A}%indexed_scope [w] _ _%P _.
  #[global] Instance params_wlp : Params (@WLP) 4 := {}.

  #[export] Instance proper_wlp_bientails {A w} :
    Proper
      (pointwise_relation _
         (forall_relation
            (fun _ => pointwise_relation _
                        (pointwise_relation _ BiEntails)) ==> BiEntails))
      (@WLP A w).
  Proof.
    intros d p q pq. destruct d as [(w1 & r01 & a)|]; cbn; [|easy].
    apply Acc.proper_wlp_bientails. apply pq.
  Qed.

  #[export] Instance proper_wlp_entails {A w} :
    Proper
      (pointwise_relation _
         (forall_relation
            (fun _ => pointwise_relation _
                        (pointwise_relation _ Entails)) ==> Entails))
      (@WLP A w).
  Proof.
    intros d p q pq. destruct d as [(w1 & r01 & a)|]; cbn; [|easy].
    apply Acc.proper_wlp_entails. apply pq.
  Qed.

  Lemma wlp_monotonic' {A w} (d : ◆A w) (R : Pred w) (P Q : □(A -> Pred) w) :
    (forall w1 (r : w ⊒⁻ w1) (a : A w1),
        Entails (Ext R r) (P w1 r a ⇒ Q w1 r a)%P) ->
    Entails R (WLP d P ⇒ WLP d Q)%P.
  Proof.
    intros pq. destruct d as [(w1 & r01 & a)|]; cbn.
    - specialize (pq w1 r01 a). rewrite <- Acc.wlp_impl.
      now apply Acc.entails_wlp.
    - rewrite pimpl_true_r. apply entails_true.
  Qed.

  Lemma wlp_pure {A w} (a : A w) (Q : □(A -> Pred) w) :
    WLP (η a) Q ⊣⊢ T Q a.
  Proof. unfold WLP, η. now rewrite Acc.wlp_refl. Qed.

  Lemma wlp_bind {A B w0} (d : ◆A w0) (f : □(A -> ◆B) w0) (Q : □(B -> Pred) w0) :
    WLP (bind d f) Q ⊣⊢ WLP d (fun w1 ζ1 a1 => WLP (f w1 ζ1 a1) (_4 Q ζ1)).
  Proof.
    destruct d as [(w1 & r01 & a)|]; cbn; [|reflexivity].
    destruct (f w1 r01 a) as [(w2 & r12 & b2)|]; cbn;
      now rewrite ?Acc.wlp_trans, ?Acc.wlp_true.
  Qed.

  Lemma wlp_tell1 {w x} (xIn : x ∈ w) (t : Ty (w - x)) (Q : □(Unit -> Pred) w) :
    WLP (tell1 xIn t) Q ⊣⊢ Acc.wlp (thick x t) (Q _ (thick x t) tt).
  Proof. reflexivity. Qed.

End ProgramLogic.

Module Correctness.

  Import (hints) Tri.
  Import Pred Pred.notations ProgramLogic.

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

    Import (hints) Pred.Acc Sub.

    Context [w] (lmgu : ▷BoxUnifier w).

    Section Soundness.
      Context (lmgu_sound : forall x (xIn : x ∈ w),
                  BoxUnifierSound (lmgu xIn)).

      Lemma flex_sound_assignment {x} (xIn : x ∈ w) (t : Ty w) :
        ⊩ WLP (flex t xIn) (Fun _ => Ext (Ty_hole xIn ≃ t)).
      Proof.
        unfold flex. destruct (varview t) as [y yIn|].
        - destruct (ctx.occurs_check_view xIn yIn).
          + rewrite wlp_pure. unfold T. now rewrite ext_refl.
          + rewrite wlp_tell1. apply Acc.pvalid_wlp.
            rewrite <- peq_persist. cbn. unfold thickIn.
            rewrite ctx.occurs_check_view_refl, ctx.occurs_check_view_thin.
            easy.
        - destruct (occurs_check_spec xIn t); subst; [|constructor].
          rewrite wlp_tell1, <- peq_persist, persist_thin_thick.
          apply Acc.pvalid_wlp. cbn. unfold thickIn.
          rewrite ctx.occurs_check_view_refl. easy.
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
          apply proper_pvalid_entails, proper_wlp_entails.
          intros w2 r12 _. now rewrite peq_symmetry.
        - intros *. now rewrite wlp_pure.
        - constructor.
        - constructor.
        - intros * IH1 IH2 *. rewrite wlp_bind.
          specialize (IH1 _ ζ01). revert IH1.
          apply proper_pvalid_entails, proper_wlp_entails.
          intros w2 ζ12 _. rewrite wlp_bind.
          apply (pGeneralize (IH2 _ (ζ01 ⊙ ζ12))), wlp_monotonic'.
          intros ? ? _. rewrite wlp_pure. unfold T, _4.
          rewrite ?trans_refl_r, ?ext_trans, ?ext_impl.
          apply proper_ext_entails; auto.
          apply proper_ext_entails; auto.
          apply proper_ext_entails; auto.
          rewrite (peq_ty_noconfusion (Ty_func s1 s2)).
          now apply pimpl_and_adjoint.
      Qed.

    End Soundness.

    Section Completeness.
      Context (lmgu_complete : forall x (xIn : x ∈ w),
                  BoxUnifierComplete (lmgu xIn)).

      Lemma flex_complete_assignment {x} (xIn : x ∈ w) (t : Ty w) :
        Entails
          (Ty_hole xIn ≃ t)%P
          (WP (flex t xIn) (fun (w0 : World) (_ : w ⊒⁻ w0) (_ : Unit w0) => ⊤%P)).
      Proof.
        unfold flex. destruct (varview t) as [y yIn|].
        - destruct (ctx.occurs_check_view xIn yIn).
          + rewrite wp_pure. unfold T. apply entails_true.
          + unfold WP, tell1. now rewrite Acc.wp_thick, ext_true, pand_true_r.
        - destruct (occurs_check_spec xIn t) as [|[HOC|HOC]]; cbn.
          + subst. now rewrite Acc.wp_thick, ext_true, pand_true_r.
          + destruct (H _ _ HOC).
          + now apply pno_cycle in HOC.
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
        - intros *. rewrite wp_pure. apply entails_true.
        - intros. now rewrite peq_ty_noconfusion, ext_false.
        - intros. now rewrite peq_ty_noconfusion, ext_false.
        - intros * IH1 IH2 *.
          rewrite wp_bind, peq_ty_noconfusion.
          rewrite <- ext_and.
          apply pimpl_and_adjoint.
          apply (pApply (IH1 w1 ζ01)). clear IH1.
          apply pimpl_and_adjoint.
          rewrite pand_comm.
          apply pimpl_and_adjoint.
          apply wp_monotonic'. intros.
          rewrite pimpl_true_l.
          rewrite wp_bind.
          rewrite <- ext_trans.
          apply (pApply (IH2 _ _)).
          apply proper_wp_entails. intros ? ? _.
          rewrite wp_pure. unfold _4, T.
          reflexivity.
      Qed.

    End Completeness.

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
    - rewrite Acc.wlp_refl. easy.
    - rewrite wlp_bind. generalize (bmgu_sound t1 t2 ζ01).
      apply proper_pvalid_entails, proper_wlp_entails.
      intros w2 r2 _. apply (pGeneralize (IHC _ (ζ01 ⊙⁻ r2))).
      apply wlp_monotonic'. unfold _4. intros w3 r3 _.
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
    - rewrite Acc.wp_refl. easy.
    - rewrite wp_bind. rewrite <- ext_and.
      apply pimpl_and_adjoint.
      apply (pApply (@bmgu_complete _ t1 t2 _ ζ01)).
      apply pimpl_and_adjoint.
      rewrite pand_comm.
      apply pimpl_and_adjoint.
      apply wp_monotonic'. intros.
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
      match o with
      | Some (w'; (r, (C, a))) => Acc.wp r (instpred C ∧ Q _ r a)
      | None => PFalse
      end.

  Lemma prenex_correct {A w} (m : FreeM A w) (Q : □⁺(A -> Pred) w) :
    wp_prenex (prenex m) Q ⊣⊢ STLC.WP m Q.
  Proof.
    unfold wp_prenex.
    induction m; cbn.
    - rewrite Acc.wp_refl. rewrite pand_true_l. reflexivity.
    - reflexivity.
    - destruct (prenex m) as [(w' & r & C & a)|]; cbn.
      + change (Acc.wp r (((t[r] ≃ t0[r]) ∧ instpred C) ∧ Q w' r a)
          ⊣⊢ PEq t t0 ∧ STLC.WP m Q).
        rewrite <- IHm.
        rewrite Acc.and_wp_r.
        apply Acc.proper_wp_bientails.
        rewrite <- peq_persist.
        unfold BiEntails, PAnd.
        intros ι; cbn; intuition.
      + change (PFalse ⊣⊢ (PEq t t0 ∧ STLC.WP m Q)).
        rewrite <- IHm. now rewrite pand_false_r.
    - unfold BiEntails, PAnd, PEq, _4, Acc.wp in *.
      intros ι. destruct (prenex m) as [(w' & r & C & a)|]; cbn.
      + split.
        * intros (ι' & Heq & HC & HQ). subst. cbn.
          remember (inst r ι') as ι. destruct (env.view ι).
          exists v. apply IHm. exists ι'. rewrite Heqι.
          split. easy. split; auto.
        * intros (t & Hwp). apply IHm in Hwp.
          destruct Hwp as (ι' & Heq & HC & HQ).
          exists ι'. cbn. rewrite Heq. cbn. auto.
      + split; [easy|]. intros (t & Hwp). now apply IHm in Hwp.
  Qed.

  Definition wp_optiondiamond {A} : ⊢ ?◇⁺ A -> □⁺(A -> Pred) -> Pred :=
    fun w m Q =>
      match m with
      | Some (w1; (r01, a)) => Acc.wp r01 (Q w1 r01 a)
      | None => PFalse
      end.

  Lemma solvefree_equiv {A} {pA : Persistent Tri.Tri A}
    (m : FreeM A ctx.nil) (Q : □⁺(A -> Pred) [ctx]) :
    wp_optiondiamond (solvefree m) Q ⊣⊢ STLC.WP m Q.
  Proof.
    rewrite <- prenex_correct. unfold solvefree.
    unfold wp_prenex, wp_optiondiamond.
    destruct (prenex m) as [(w1 & r1 & C & a)|]; cbn; [|easy].
    pose proof (solvelist_complete C) as Hcompl.
    pose proof (solvelist_sound C) as Hsound.
    destruct solvelist as [(w2 & r2 & [])|]; cbn in *.
    - apply split_bientails. split.
      + intros ι0 (ι2 & Heq & HQ); subst. exists (inst r2 ι2).
        specialize (Hsound (inst r2 ι2) ι2 eq_refl). hnf in Hsound.
        unfold PAnd. repeat split.
        * destruct (env.view (inst r1 (inst r2 ι2))).
          destruct (env.view (inst alloc.nil_l ι2)).
          reflexivity.
        * assumption.
        * clear - HQ. admit.
      + intros ι0 (ι1 & Heq1 & HC & HQ).
        specialize (Hcompl ι1 HC). destruct Hcompl as (ι2 & Heq2 & _).
        exists ι2. split. subst.
        * destruct (env.view (inst r1 (inst r2 ι2))).
          destruct (env.view (inst alloc.nil_l ι2)).
          reflexivity.
        * clear - HQ. admit.
    - apply split_bientails. split. firstorder.
      intros ι (ι1 & Heq & HC & HQ). apply (Hcompl ι1 HC).
  Admitted.

End Correctness.

Module Generalized.

  Import (hints) Sub Tri.
  Import Pred Pred.notations ProgramLogic LR.

  Lemma wp_tell {w x} (xIn : x ∈ w) (t : Ty (w - x)) (Q : □(Unit -> Pred) w)
    (RQ : RProper (RBox (RImpl RUnit (RPred Tri))) Q) :
    WP (tell1 xIn t) Q ⊣⊢ (Ty_hole xIn ≃ thin xIn t) ∧ T Q tt.
  Proof.
    unfold WP, tell1. rewrite Acc.wp_thick. intros ι. cbn.
    rewrite Sub.subst_thin, inst_persist_ty, Sub.inst_thin.
    apply and_iff_compat_l'. intros Heq.
    specialize (RQ ι w (w - x) refl (thick x t) (thick x t) (env.remove _ ι xIn)).
    cbv [RProper PValid RBox Forall Const PImpl Acc.wlp PEq
      RImpl RUnit PTrue RPred PIff Ext] in RQ.
    cbn in RQ. rewrite <- Heq, env.insert_remove in RQ.
    now specialize (RQ eq_refl eq_refl tt tt I).
  Qed.

  Lemma flex_correct {w x} (xIn : x ∈ w) (t : Ty w)
    (Q : □(Unit -> Pred) w) (RQ : RProper (RBox (RImpl RUnit (RPred Tri))) Q) :
    WP (flex t xIn) Q ⊣⊢ (Ty_hole xIn ≃ t) ∧ T Q tt.
  Proof.
    unfold flex. destruct (varview t) as [y yIn|].
    - destruct (ctx.occurs_check_view xIn yIn).
      + now rewrite wp_pure, peq_refl, pand_true_l.
      + now rewrite wp_tell.
    - destruct (occurs_check_spec xIn t) as [|[HOC|HOC]]; cbn - [tell1].
      + rewrite wp_tell; now subst.
      + destruct (H _ _ HOC).
      + apply pno_cycle in HOC. apply split_bientails. split; [apply entails_false|].
        now rewrite HOC, pand_false_l.
  Qed.

End Generalized.

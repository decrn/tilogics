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

  Import World.notations.
  Import (hints) Tri.
  Import Pred.
  Import Pred.notations.

  Definition WP {A} : ⊢ʷ ◆A -> □(A -> Pred) -> Pred :=
    fun w0 d Q =>
      match d with
      | Some (w1; (r01, a)) => Acc.wp r01 (Q w1 r01 a)
      | None                => Falseₚ
      end.

  #[global] Arguments WP {A}%indexed_scope [w] _ _%P _.
  #[global] Instance params_wp : Params (@WP) 4 := {}.

  #[export] Instance proper_wp_bientails {A w} :
    Proper
      (pointwise_relation _
         (forall_relation
            (fun _ => pointwise_relation _
                        (pointwise_relation _ bientails)) ==> bientails))
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
                        (pointwise_relation _ entails)) ==> entails))
      (@WP A w).
  Proof.
    intros d p q pq. destruct d as [(w1 & r01 & a)|]; cbn; [|easy].
    apply Acc.proper_wp_entails. apply pq.
  Qed.

  Lemma wp_monotonic' {A w} (d : ◆A w) (R : Pred w) (P Q : □(A -> Pred) w) :
    (forall w1 (r : w ⊒⁻ w1) (a : A w1),
        Ext R r ⊢ₚ P w1 r a ->ₚ Q w1 r a) ->
    R ⊢ₚ WP d P ->ₚ WP d Q.
  Proof.
    intros pq. destruct d as [(w1 & r01 & a)|]; cbn.
    - specialize (pq w1 r01 a).
      apply impl_and_adjoint.
      rewrite Acc.and_wp_r.
      apply Acc.proper_wp_entails.
      apply impl_and_adjoint.
      apply pq.
    - apply impl_and_adjoint.
      now rewrite and_false_r.
  Qed.

  Lemma wp_pure {A w0} (a : A w0) (Q : □(A -> Pred) w0) :
    WP (pure a) Q ⊣⊢ₚ T Q a.
  Proof. unfold WP, pure. cbn. now rewrite Acc.wp_refl. Qed.

  Lemma wp_bind {A B w0} (d : ◆A w0) (f : □(A -> ◆B) w0) (Q : □(B -> Pred) w0) :
    WP (bind d f) Q ⊣⊢ₚ WP d (fun w1 ζ1 a1 => WP (f w1 ζ1 a1) (_4 Q ζ1)).
  Proof.
    destruct d as [(w1 & r01 & a)|]; cbn; [|reflexivity].
    destruct (f w1 r01 a) as [(w2 & r12 & b2)|]; cbn;
      now rewrite ?Acc.wp_trans, ?Acc.wp_false.
  Qed.

  Definition WLP {A} : ⊢ʷ ◆A -> □(A -> Pred) -> Pred :=
    fun w0 d Q =>
      match d with
      | Some (w1; (r01, a)) => Pred.Acc.wlp r01 (Q w1 r01 a)
      | None                => Trueₚ
      end.
  #[global] Arguments WLP {A}%indexed_scope [w] _ _%P _.
  #[global] Instance params_wlp : Params (@WLP) 4 := {}.

  #[export] Instance proper_wlp_bientails {A w} :
    Proper
      (pointwise_relation _
         (forall_relation
            (fun _ => pointwise_relation _
                        (pointwise_relation _ bientails)) ==> bientails))
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
                        (pointwise_relation _ entails)) ==> entails))
      (@WLP A w).
  Proof.
    intros d p q pq. destruct d as [(w1 & r01 & a)|]; cbn; [|easy].
    apply Acc.proper_wlp_entails. apply pq.
  Qed.

  Lemma wlp_monotonic' {A w} (d : ◆A w) (R : Pred w) (P Q : □(A -> Pred) w) :
    (forall w1 (r : w ⊒⁻ w1) (a : A w1),
        entails (Ext R r) (P w1 r a ->ₚ Q w1 r a)%P) ->
    entails R (WLP d P ->ₚ WLP d Q)%P.
  Proof.
    intros pq. destruct d as [(w1 & r01 & a)|]; cbn.
    - specialize (pq w1 r01 a). rewrite <- Acc.wlp_impl.
      now apply Acc.entails_wlp.
    - rewrite impl_true_r. apply true_r.
  Qed.

  Lemma wlp_pure {A w} (a : A w) (Q : □(A -> Pred) w) :
    WLP (pure a) Q ⊣⊢ₚ T Q a.
  Proof. unfold WLP, pure. cbn. now rewrite Acc.wlp_refl. Qed.

  Lemma wlp_bind {A B w0} (d : ◆A w0) (f : □(A -> ◆B) w0) (Q : □(B -> Pred) w0) :
    WLP (bind d f) Q ⊣⊢ₚ WLP d (fun w1 ζ1 a1 => WLP (f w1 ζ1 a1) (_4 Q ζ1)).
  Proof.
    destruct d as [(w1 & r01 & a)|]; cbn; [|reflexivity].
    destruct (f w1 r01 a) as [(w2 & r12 & b2)|]; cbn;
      now rewrite ?Acc.wlp_trans, ?Acc.wlp_true.
  Qed.

  Lemma wlp_tell1 {w x} (xIn : x ∈ w) (t : Ty (w - x)) (Q : □(Unit -> Pred) w) :
    WLP (tell1 xIn t) Q ⊣⊢ₚ Acc.wlp (thick x t) (Q _ (thick x t) tt).
  Proof. reflexivity. Qed.

End ProgramLogic.

Module Correctness.

  Import World.notations.
  Import (hints) Pred.Acc Tri.
  Import Pred Pred.notations ProgramLogic.

  Definition interpM : ⊢ʷ M Unit -> Pred :=
    fun w m => WP m (fun _ _ _ => Trueₚ).

  Definition interpC : ⊢ʷ C -> Pred.
  Proof.
    intros w m.
    unfold C in m.
    refine (WP (m w refl) (fun _ _ _ => Trueₚ)).
  Defined.

  (* Lemma ctrue_correct {w : World} : BiEntails (w := w) (interp ctrue) PTrue. *)
  (* Proof. unfold interp, ctrue. now rewrite wp_pure. Qed. *)

  (* Lemma cfalse_correct {w : World} : BiEntails (w := w) (interp cfalse) PFalse. *)
  (* Proof. unfold interp, cfalse. easy. Qed. *)

  Opaque bind.
  Import LR.

  Definition ProperRC {w} (c : C w) : Prop :=
    forall w' (r : Tri w w'),
      Acc.wp r (WP (c w' r) (fun _ _ _ => Trueₚ)) ⊣⊢ₚ
      Acc.wp r Trueₚ /\ₚ WP (c w refl) (fun _ _ _ => Trueₚ).

  Lemma proper_ctrue {w0} : @ProperRC w0 ctrue.
  Proof.
    unfold ProperRC, ctrue; intros w1 r01. cbn.
    now rewrite ?Acc.wp_refl, and_true_r.
  Qed.

  Lemma proper_cfalse {w0} : @ProperRC w0 cfalse.
  Proof.
    unfold ProperRC, cfalse; intros w1 r01. cbn.
    now rewrite Acc.wp_false, and_false_r.
  Qed.

  Lemma proper_cand {w0} (c1 c2 : C w0) :
    ProperRC c1 -> ProperRC c2 -> ProperRC (cand c1 c2).
  Proof.
    unfold ProperRC, cand; intros p1 p2 w1 r01.
    unfold interpM in *. rewrite ?wp_bind. unfold _4.
    specialize (p1 w1 r01).
    destruct (c1 w0 refl) as [(w2 & r02 & [])|],
        (c1 w1 r01)  as [(w3 & r13 & [])|];
      cbn in *; rewrite ?Acc.wp_false, ?ext_false, ?pand_false_r in *.
    - rewrite <- Acc.wp_trans in *. rewrite p2. rewrite p2. clear p2.
      rewrite p1. constructor. pred_unfold. intuition.
    - rewrite p2. apply split_bientails. split.
      + constructor. intros ? [].
      + rewrite p1. constructor. pred_unfold. intuition.
    - rewrite <- Acc.wp_trans in *.
      now rewrite p2, p1, and_false_r, and_false_l.
    - easy.
  Qed.

  Lemma cand_correct {w} {c1 c2 : C w} {p2 : ProperRC c2} :
    interpC (cand c1 c2) ⊣⊢ₚ interpC c1 /\ₚ interpC c2.
  Proof.
    unfold interpC, cand. rewrite wp_bind.
    destruct (c1 w refl) as [(w1 & r01 & [])|];
      cbn; [|now rewrite and_false_l].
    unfold _4.
    rewrite Acc.and_wp_l, and_true_l, trans_refl_l.
    rewrite (p2 w1 r01).
    now rewrite Acc.and_wp_l, and_true_l.
  Qed.

  Definition UnifierSound : ⊢ʷ Unifier -> PROP :=
    fun w0 u =>
      forall (t1 t2 : Ty w0),
        ⊤ₚ ⊢ₚ WLP (u t1 t2) (Fun _ => Ext (t1 =ₚ t2)).

  Definition UnifierComplete : ⊢ʷ Unifier -> PROP :=
    fun w0 u =>
      forall (t1 t2 : Ty w0),
        t1 =ₚ t2 ⊢ₚ WP (u t1 t2) (fun _ _ _ => ⊤ₚ)%P.

  Definition BoxUnifierSound : ⊢ʷ BoxUnifier -> PROP :=
    fun w0 bu =>
      forall (t1 t2 : Ty w0) (w1 : World) (ζ01 : w0 ⊒⁻ w1),
        ⊤ₚ ⊢ₚ WLP (bu t1 t2 w1 ζ01) (Fun _ => Ext (Ext (t1 =ₚ t2) ζ01)).

  Definition BoxUnifierComplete : ⊢ʷ BoxUnifier -> PROP :=
    fun w0 bu =>
      forall (t1 t2 : Ty w0) (w1 : World) (ζ01 : w0 ⊒⁻ w1),
        entails (Ext (t1 =ₚ t2) ζ01) (WP (bu t1 t2 w1 ζ01) (fun _ _ _ => Trueₚ)).

  Section BoxedProofs.

    Import Tri.notations.
    Import (hints) Pred.Acc Sub.

    Context [w] (lmgu : ▷BoxUnifier w).

    Section Soundness.
      Context (lmgu_sound : forall x (xIn : x ∈ w),
                  BoxUnifierSound (lmgu xIn)).

      Lemma flex_sound_assignment {x} (xIn : x ∈ w) (t : Ty w) :
        ⊤ₚ ⊢ₚ WLP (flex t xIn) (Fun _ => Ext (Ty_hole xIn =ₚ t)).
      Proof.
        unfold flex. destruct (varview t) as [y yIn|].
        - destruct (ctx.occurs_check_view xIn yIn).
          + rewrite wlp_pure. unfold T.
            rewrite ext_refl, eqₚ_refl.
            reflexivity.
          + rewrite wlp_tell1. rewrite <- Acc.entails_wlp.
            rewrite ext_true, ext_eq. cbn. unfold thickIn.
            rewrite ctx.occurs_check_view_refl, ctx.occurs_check_view_thin.
            rewrite eqₚ_refl. reflexivity.
        - destruct (occurs_check_spec xIn t); subst.
          + rewrite wlp_tell1, ext_eq, persist_thin_thick.
            rewrite <- Acc.entails_wlp, ext_true. cbn. unfold thickIn.
            rewrite ctx.occurs_check_view_refl. rewrite eqₚ_refl. reflexivity.
          + constructor. constructor.
      Qed.

      Lemma boxflex_sound_assignment {x} (xIn : x ∈ w) (t : Ty w)
        {w1} (ζ01 : w ⊒⁻ w1) :
        ⊤ₚ ⊢ₚ WLP (boxflex lmgu t xIn ζ01) (Fun _ => Ext (Ext (Ty_hole xIn =ₚ t) ζ01)).
      Proof.
        unfold boxflex, Tri.box_intro_split.
        destruct ζ01 as [|w2 y yIn ty]; folddefs.
        - generalize (flex_sound_assignment xIn t).
          apply proper_entails_entails; [easy|].
          apply proper_wlp_entails.
          intros w2 ζ2 _.
          now rewrite ext_refl.
        - generalize (lmgu_sound yIn (Ty_hole xIn)[thick y ty] t[thick y ty] ζ01). clear.
          apply proper_entails_entails; [easy|].
          apply proper_wlp_entails.
          intros w3 ζ3 _.
          now rewrite ext_trans, ?ext_eq.
      Qed.

      Lemma wp_ctrue {w0 w1} (r01 : w0 ⊒⁻ w1) (Q : □(Unit -> Pred) w1) :
        WP (ctrue r01) Q ⊣⊢ₚ T Q tt.
      Proof. unfold ctrue. now rewrite wp_pure. Qed.

      Lemma wp_cfalse {w0 w1} (r01 : w0 ⊒⁻ w1) (Q : □(Unit -> Pred) w1) :
        WP (cfalse r01) Q ⊣⊢ₚ Falseₚ.
      Proof. reflexivity. Qed.

      Lemma wp_cand {w0 w1} (r01 : w0 ⊒⁻ w1) m1 m2 (Q : □(Unit -> Pred) w1) :
        WP (cand m1 m2 r01) Q ⊣⊢ₚ
        WP (m1 w1 r01) (fun w2 r12 _ => WP (_4 m2 r01 r12) (_4 Q r12)).
      Proof. unfold cand. now rewrite wp_bind. Qed.

      Lemma wlp_ctrue {w0 w1} (r01 : w0 ⊒⁻ w1) (Q : □(Unit -> Pred) w1) :
        WLP (ctrue r01) Q ⊣⊢ₚ T Q tt.
      Proof. unfold ctrue. now rewrite wlp_pure. Qed.

      Lemma wlp_cfalse {w0 w1} (r01 : w0 ⊒⁻ w1) (Q : □(Unit -> Pred) w1) :
        WLP (cfalse r01) Q ⊣⊢ₚ Trueₚ.
      Proof. reflexivity. Qed.

      Lemma wlp_cand {w0 w1} (r01 : w0 ⊒⁻ w1) m1 m2 (Q : □(Unit -> Pred) w1) :
        WLP (cand m1 m2 r01) Q ⊣⊢ₚ
        WLP (m1 w1 r01) (fun w2 r12 _ => WLP (_4 m2 r01 r12) (_4 Q r12)).
      Proof. unfold cand. now rewrite wlp_bind. Qed.

      Lemma boxmgu_sound_assignment : BoxUnifierSound (boxmgu lmgu).
      Proof.
        intros t1 t2. pattern (boxmgu lmgu t1 t2).
        apply boxmgu_elim; clear t1 t2.
        - intros. apply boxflex_sound_assignment.
        - intros. generalize (boxflex_sound_assignment xIn t ζ01).
          apply proper_entails_entails; [easy|].
          apply proper_wlp_entails.
          intros w2 r12 _. now rewrite eqₚ_sym.
        - intros *. now rewrite wlp_ctrue.
        - intros *. now rewrite wlp_cfalse.
        - intros *. now rewrite wlp_cfalse.
        - intros * IH1 IH2 *. rewrite wlp_cand.
          specialize (IH1 _ ζ01). revert IH1.
          apply proper_entails_entails; [easy|].
          apply proper_wlp_entails.
          intros w2 ζ12 _. unfold _4.
          specialize (IH2 _ (ζ01 ⊙ ζ12)).
          rewrite <- and_true_r, IH2. apply impl_and_adjoint.
          apply wlp_monotonic'.
          intros ? ? _.
          rewrite ?trans_refl_r, ?ext_trans, <- ?ext_impl.
          apply proper_ext_entails; auto.
          apply proper_ext_entails; auto.
          apply proper_ext_entails; auto.
          rewrite (peq_ty_noconfusion (Ty_func s1 s2)).
          now apply impl_and_adjoint.
      Qed.

    End Soundness.

    Section Completeness.
      Context (lmgu_complete : forall x (xIn : x ∈ w),
                  BoxUnifierComplete (lmgu xIn)).

      Lemma flex_complete_assignment {x} (xIn : x ∈ w) (t : Ty w) :
        Ty_hole xIn =ₚ t ⊢ₚ WP (flex t xIn) (fun _ _ _ => ⊤ₚ)%P.
      Proof.
        unfold flex. destruct (varview t) as [y yIn|].
        - destruct (ctx.occurs_check_view xIn yIn).
          + rewrite wp_pure. unfold T. apply true_r.
          + unfold WP, tell1. now rewrite Acc.wp_thick, ext_true, and_true_r.
        - destruct (occurs_check_spec xIn t) as [|[HOC|HOC]]; cbn.
          + subst. now rewrite Acc.wp_thick, ext_true, and_true_r.
          + destruct (H _ _ HOC).
          + now apply pno_cycle in HOC.
      Qed.

      Lemma boxflex_complete_assignment {x} (xIn : x ∈ w) (t : Ty w) {w1} (ζ01 : w ⊒⁻ w1) :
        Ext (Ty_hole xIn =ₚ t) ζ01 ⊢ₚ
        WP (boxflex lmgu t xIn ζ01) (fun _ _ _ => ⊤ₚ)%P.
      Proof.
        unfold boxflex, Tri.box_intro_split.
        destruct ζ01 as [|w2 y yIn ty]; folddefs.
        - rewrite ext_refl. apply flex_complete_assignment.
        - change (Tri.cons ?x ?t ?r) with (thick x t ⊙ r).
          rewrite ext_trans, ext_eq.
          now apply (lmgu_complete yIn).
      Qed.

      Lemma boxmgu_complete_assignment : BoxUnifierComplete (boxmgu lmgu).
      Proof.
        intros t1 t2. pattern (boxmgu lmgu t1 t2).
        apply boxmgu_elim; clear t1 t2.
        - intros. apply boxflex_complete_assignment.
        - intros. rewrite eqₚ_sym. apply boxflex_complete_assignment.
        - intros *. rewrite wp_ctrue. apply true_r.
        - intros. now rewrite peq_ty_noconfusion, ext_false.
        - intros. now rewrite peq_ty_noconfusion, ext_false.
        - intros * IH1 IH2 *.
          rewrite wp_cand, peq_ty_noconfusion.
          rewrite ext_and.
          apply impl_and_adjoint.
          apply (pApply (IH1 w1 ζ01)). clear IH1.
          apply impl_and_adjoint.
          rewrite and_comm.
          apply impl_and_adjoint.
          apply wp_monotonic'. intros.
          rewrite impl_true_l. unfold _4.
          rewrite <- ext_trans.
          apply (pApply (IH2 _ _)).
          now apply proper_wp_entails.
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
    specialize (bmgu_sound t1 t2 refl).
    apply proper_entails_entails; [easy|].
    apply proper_wlp_entails.
    intros w' r _. now rewrite ext_refl.
  Qed.

  Definition mgu_complete w : UnifierComplete (@mgu w).
  Proof.
    unfold UnifierComplete, mgu. intros t1 t2.
    specialize (@bmgu_complete _ t1 t2 _ refl).
    now rewrite ext_refl.
  Qed.

  Import Pred.

  #[local] Instance instpred_prod_ty : InstPred (Prod Ty Ty) :=
    fun w '(t1,t2) => eqₚ t1 t2.

  Definition BoxSolveListSound : ⊢ʷ BoxSolveList -> PROP :=
    fun w0 bsl =>
      forall (C : List (Prod Ty Ty) w0) (w1 : World) (ζ01 : w0 ⊒⁻ w1),
        ⊤ₚ ⊢ₚ WLP (bsl C w1 ζ01) (Fun _ => Ext (Ext (instpred C) ζ01)).

  Definition SolveListSound : ⊢ʷ SolveList -> PROP :=
    fun w0 sl =>
      forall (C : List (Prod Ty Ty) w0),
        ⊤ₚ ⊢ₚ WLP (sl C) (Fun _ => Ext (instpred C)).

  Definition BoxSolveListComplete : ⊢ʷ BoxSolveList -> PROP :=
    fun w0 bsl =>
      forall (C : List (Prod Ty Ty) w0) (w1 : World) (ζ01 : w0 ⊒⁻ w1),
        entails (Ext (instpred C) ζ01) (WP (bsl C w1 ζ01) (fun _ _ _ => Trueₚ)).

  Definition SolveListComplete : ⊢ʷ SolveList -> PROP :=
    fun w0 sl =>
      forall (C : List (Prod Ty Ty) w0),
        entails (instpred C) (WP (sl C) (fun _ _ _ => Trueₚ)).

  Lemma boxsolvelist_sound {w} : BoxSolveListSound (boxsolvelist (w := w)).
  Proof.
    intros C. induction C as [|[t1 t2]]; cbn - [ctrue cand]; intros.
    - now rewrite wlp_ctrue.
    - rewrite wlp_cand. generalize (bmgu_sound t1 t2 ζ01).
      apply proper_entails_entails; [easy|].
      apply proper_wlp_entails. intros w2 r2 _.
      rewrite <- and_true_r, (IHC _ (ζ01 ⊙⁻ r2)).
      apply impl_and_adjoint, wlp_monotonic'.
      unfold _4. intros w3 r3 _.
      rewrite ?trans_refl_r, ?ext_trans, <- ?ext_impl.
      apply proper_ext_entails; auto.
      apply proper_ext_entails; auto.
      apply proper_ext_entails; auto.
      now apply impl_and_adjoint.
  Qed.

  Lemma solvelist_sound {w} : SolveListSound (solvelist (w := w)).
  Proof.
    unfold SolveListSound, solvelist. intros C.
    generalize (boxsolvelist_sound C refl).
    apply proper_entails_entails; [easy|].
    apply proper_wlp_entails.
    intros w' r _. now rewrite ext_refl.
  Qed.

  Lemma boxsolvelist_complete {w} : BoxSolveListComplete (boxsolvelist (w := w)).
  Proof.
    intros C. induction C as [|[t1 t2]]; cbn; intros.
    - rewrite Acc.wp_refl. easy.
    - rewrite wp_cand. rewrite ext_and.
      rewrite (@bmgu_complete _ t1 t2 _ ζ01).
      rewrite and_comm. apply impl_and_adjoint.
      apply wp_monotonic'. intros.
      rewrite impl_true_l, <- ext_trans.
      apply IHC.
  Qed.

  Lemma solvelist_complete {w} : SolveListComplete (solvelist (w := w)).
  Proof.
    unfold SolveListComplete, solvelist. intros C.
    apply (pApply_r (@boxsolvelist_complete _ C _ refl)).
    now rewrite ext_refl.
  Qed.

  Definition wp_prenex {A} : ⊢ʷ ?◇⁺(List (Ty * Ty) * A) -> □⁺(A -> Pred) -> Pred :=
    fun w o Q =>
      match o with
      | Some (w'; (r, (C, a))) => Acc.wp r (instpred C /\ₚ Q _ r a)
      | None => Falseₚ
      end.

  Arguments Acc.wp {R _ w0 w1} r01 Q _/.

  Lemma prenex_correct {A w} (m : FreeM A w) (Q : □⁺(A -> Pred) w) :
    wp_prenex (prenex m) Q ⊣⊢ₚ STLC.WP m Q.
  Proof.
    unfold wp_prenex.
    induction m; cbn.
    - rewrite Acc.wp_refl. rewrite and_true_l. reflexivity.
    - reflexivity.
    - destruct (prenex m) as [(w' & r & C & a)|]; cbn.
      + change (Acc.wp r (((t[r] =ₚ t0[r]) /\ₚ instpred C) /\ₚ Q w' r a)
          ⊣⊢ₚ t =ₚ t0 /\ₚ STLC.WP m Q).
        rewrite <- IHm.
        rewrite Acc.and_wp_r.
        apply Acc.proper_wp_bientails.
        now rewrite ext_eq, and_assoc.
      + change (Falseₚ ⊣⊢ₚ (t =ₚ t0 /\ₚ STLC.WP m Q)).
        rewrite <- IHm. now rewrite and_false_r.
    - destruct (prenex m) as [(w' & r & C & a)|]; cbn.
      + change (alloc.fresh _ ?x _ ?r) with (step ⊙ r).
        assert
          (Acc.wp (step ⊙ r) (instpred C /\ₚ Q w' (alloc.fresh Σ i w' r) a)
             ⊣⊢ₚ Acc.wp step (STLC.WP m (_4 Q step)))
          as -> by now rewrite Acc.wp_trans, <- IHm.
        constructor. intros ι; cbn; split.
        * intros (ι' & Heq & HQ). destruct env.view as [ι' t]. subst ι'.
          now exists t.
        * intros (t & Hwp). apply IHm in Hwp. exists (env.snoc ι _ t). cbn.
          split. auto. now apply IHm.
      + constructor. split; [easy|]. intros (t & Hwp). now apply IHm in Hwp.
  Qed.

  Definition wp_optiondiamond {A} : ⊢ʷ ?◇⁺ A -> □⁺(A -> Pred) -> Pred :=
    fun w m Q =>
      match m with
      | Some (w1; (r01, a)) => Acc.wp r01 (Q w1 r01 a)
      | None => Falseₚ
      end.

  Lemma solvefree_equiv {AT A} {instA : Inst AT A}
    {persAllocA : Persistent Alloc AT}
    {persTriA : Persistent Tri.Tri AT}
    (m : FreeM AT ctx.nil) (Q : □⁺(AT -> Pred) [ctx])
    (RQ : ProperPost Q) :
    wp_optiondiamond (solvefree m) Q ⊣⊢ₚ STLC.WP m Q.
  Proof.
    rewrite <- prenex_correct. unfold solvefree.
    unfold wp_prenex, wp_optiondiamond.
    destruct (prenex m) as [(w1 & r1 & C & a)|]; cbn; [|easy].
    pose proof (solvelist_complete C) as Hcompl.
    pose proof (solvelist_sound C) as Hsound.
    destruct solvelist as [(w2 & r2 & [])|]; cbn in *.
    - apply split_bientails. split.
      + destruct Hsound as [Hsound]. constructor.
        intros ι0 (ι2 & Heq & HQ); pred_unfold; subst. exists (inst r2 ι2).
        specialize (Hsound (inst r2 ι2) I ι2 eq_refl). hnf in Hsound.
        unfold andₚ. repeat split.
        * destruct (env.view (inst r1 (inst r2 ι2))).
          destruct (env.view (inst alloc.nil_l ι2)).
          reflexivity.
        * assumption.
        * admit.
          (* epose proof (RQ w1 r1 _ a (inst r2 ι2)) as H1. *)
          (* epose proof (RQ w2 alloc.nil_l _ (persist _ a _ r2) ι2) as H2. *)
          (* cbn in H1, H2. *)
      + destruct Hcompl as [Hcompl]. constructor.
        intros ι0 (ι1 & Heq1 & HC & HQ).
        specialize (Hcompl ι1 HC). destruct Hcompl as (ι2 & Heq2 & _).
        exists ι2. split. subst.
        * destruct (env.view (inst r1 (inst r2 ι2))).
          destruct (env.view (inst alloc.nil_l ι2)).
          reflexivity.
        * clear - HQ. admit.
    - apply split_bientails. split. firstorder.
      destruct Hcompl as [Hcompl]. constructor.
      intros ι (ι1 & Heq & HC & HQ). apply (Hcompl ι1 HC).
  Admitted.

End Correctness.

Module Generalized.

  Import World.notations.
  Import (hints) Sub Tri.
  Import Pred Pred.notations ProgramLogic LR.

  Lemma wp_tell {w x} (xIn : x ∈ w) (t : Ty (w - x)) (Q : □(Unit -> Pred) w)
    (RQ : RProper (RBox (RImpl RUnit (RPred Tri))) Q) :
    WP (tell1 xIn t) Q ⊣⊢ₚ Ty_hole xIn =ₚ thin xIn t /\ₚ T Q tt.
  Proof.
    unfold WP, tell1. rewrite Acc.wp_thick. constructor. intros ι. pred_unfold.
    rewrite Sub.subst_thin, inst_persist, Sub.inst_thin.
    apply and_iff_compat_l'. intros Heq.
    destruct RQ as [RQ].
    specialize (RQ ι I w (w - x) refl (thick x t) (thick x t) (env.remove _ ι xIn)).
    cbv [RProper RBox Forall Const implₚ Acc.wlp eqₚ
      RImpl RUnit Trueₚ RPred iffₚ Ext] in RQ.
    pred_unfold.
    cbn in RQ. rewrite <- Heq, env.insert_remove in RQ.
    now specialize (RQ eq_refl eq_refl tt tt I).
  Qed.

  Lemma flex_correct {w x} (xIn : x ∈ w) (t : Ty w)
    (Q : □(Unit -> Pred) w) (RQ : RProper (RBox (RImpl RUnit (RPred Tri))) Q) :
    WP (flex t xIn) Q ⊣⊢ₚ Ty_hole xIn =ₚ t /\ₚ T Q tt.
  Proof.
    unfold flex. destruct (varview t) as [y yIn|].
    - destruct (ctx.occurs_check_view xIn yIn).
      + now rewrite wp_pure, eqₚ_refl, and_true_l.
      + now rewrite wp_tell.
    - destruct (occurs_check_spec xIn t) as [|[HOC|HOC]]; cbn - [tell1].
      + rewrite wp_tell; now subst.
      + destruct (H _ _ HOC).
      + apply pno_cycle in HOC. apply split_bientails. split; [apply false_l|].
        now rewrite HOC, and_false_l.
  Qed.

End Generalized.

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
From stdpp Require Import
  base gmap.
From Em Require Import
  Context
  Environment
  Prelude
  Stlc.Alloc
  Stlc.Instantiation
  Stlc.Persistence
  Stlc.Predicates
  Stlc.Sem
  Stlc.Spec
  Stlc.Substitution
  Stlc.Symbolic.Free
  Stlc.Unification
  Stlc.Unification.CorrectnessWithAssignments
  Stlc.Worlds.

Import ctx.notations.
Import World.notations.

Set Implicit Arguments.

#[local] Notation "s [ ζ ]" :=
  (persist s ζ)
    (at level 8, left associativity,
      format "s [ ζ ]").

Section Generate.
  Import MonadNotations.
  Import World.notations.

  Definition generate : Exp -> ⊢ʷ Ėnv -> Free (Ṫy * Sem Exp) :=
    fix gen e {w} Γ :=
      match e with
      | exp.var x =>
          match lookup x Γ with
          | Some t => Ret (t , ėxp.var x)
          | None   => Fail
          end
      | exp.true  => Ret (ṫy.bool, ėxp.true)
      | exp.false => Ret (ṫy.bool, ėxp.false)
      | exp.ifte e1 e2 e3 =>
          [ θ1 ] '(t1,e1') <- gen e1 Γ ;;
          [ θ2 ] '(t2,e2') <- gen e2 Γ[θ1] ;;
          [ θ3 ] '(t3,e3') <- gen e3 Γ[θ1⊙θ2] ;;
          [ θ4 ] _         <- assert ṫy.bool t1[θ2⊙θ3] ;;
          [ θ5 ] _         <- assert t2[θ3⊙θ4] t3[θ4] ;;
          Ret (t3[θ4⊙θ5], ėxp.ifte e1'[θ2⊙θ3⊙θ4⊙θ5] e2'[θ3⊙θ4⊙θ5] e3'[θ4⊙θ5])
      | exp.absu x e =>
          [ θ1 ] t1       <- choose ;;
          [ θ2 ] '(t2,e') <- gen e (Γ[θ1] ,, x∷t1) ;;
          Ret (ṫy.func t1[θ2] t2, ėxp.abst x t1[θ2] e')
      | exp.abst x t1 e =>
          [ θ1 ] '(t2,e') <- gen e (Γ ,, x∷lift t1 _) ;;
          Ret (ṫy.func (lift t1 _) t2, ėxp.abst x (lift t1 _) e')
      | exp.app e1 e2 =>
          [ θ1 ] '(tf, e1') <- gen e1 Γ ;;
          [ θ2 ] '(t1, e2') <- gen e2 Γ[θ1] ;;
          [ θ3 ] t2 <- choose ;;
          [ θ4 ] _  <- assert tf[θ2⊙θ3] (ṫy.func t1[θ3] t2) ;;
          Ret (t2[θ4], ėxp.app e1'[θ2⊙θ3⊙θ4] e2'[θ3⊙θ4])
      end.

End Generate.

Section Reconstruct.

  Definition reconstruct_optiondiamond (e : Exp) :
    Option (Diamond alloc.acc_alloc (Ṫy * Sem Exp)) ctx.nil :=
    option.bind (prenex (generate e ∅)) solveoptiondiamond.

  Definition reconstruct_schematic (e : Exp) :
    option (Schematic (Ṫy * Sem Exp)) :=
    optiondiamond2schematic (reconstruct_optiondiamond e).

  Definition reconstruct_grounded (e : Exp) :
    option (Ty * Exp) :=
    option.map
      (fun s : Schematic _ =>
         let (w, te) := s in
         inst te (grounding w))
      (reconstruct_schematic e).

End Reconstruct.

Definition persist_sim_step_alloc_env := Sub.persist_sim_step (Θ := alloc.acc_alloc) (T := Ėnv).
Definition persist_sim_step_alloc_ty := Sub.persist_sim_step (Θ := alloc.acc_alloc) (T := Ṫy).
Definition persist_sim_step_alloc_sem {A} := Sub.persist_sim_step (Θ := alloc.acc_alloc) (T := Sem A).

Ltac wsimpl :=
  repeat
    (rewrite ?persist_refl, ?persist_trans, ?persist_lift,
      ?inst_lift, ?inst_reduce, ?inst_persist,
      ?inst_step_snoc, ?lk_trans, ?trans_refl_l, ?trans_refl_r,
      ?persist_insert, ?lift_insert,

      ?Pred.ext_refl, ?Pred.ext_tpb, ?Pred.ext_and, ?Pred.ext_eq,
      ?Pred.eqₚ_refl, ?Pred.impl_true_l, ?Pred.and_true_r, ?Pred.and_true_l,
      ?Pred.impl_true_r, ?Pred.impl_false_l, ?Pred.ext_impl, ?Pred.impl_and,
      ?Pred.ext_exists, ?Pred.ext_forall, ?Pred.Acc.wlp_true, ?Pred.eq_pair,
      ?Pred.eq_func,

      ?persist_sim_step_alloc_env, ?persist_sim_step_alloc_ty, ?persist_sim_step_alloc_sem,
      ?ėxp.inst_var, ?ėxp.inst_true, ?ėxp.inst_false, ?ėxp.inst_ifte, ?ėxp.inst_absu, ?ėxp.inst_abst, ?ėxp.inst_app,
      ?Sem.inst_pure, ?Sem.inst_fmap, ?Sem.inst_app, ?Sem.persist_pure, ?Sem.persist_fmap, ?Sem.persist_app,

      (* ?ProgramLogic.eqₚ_env_cons, *)
      ?step_reduce,
      (* ?ProgramLogic.equiv_true, *)
      ?lk_reduce_zero,
      ?lk_reduce_succ in *;
     cbn - [lk trans step thick Sub.up1]; auto);
  repeat setoid_rewrite Pred.ext_exists;
  repeat setoid_rewrite Pred.ext_forall;
  repeat
    match goal with
    | |- context[@persist ?A ?I ?Θ ?w0 ?x ?w1 ?θ] =>
        is_var x; generalize (@persist A I Θ w0 x w1 θ); clear x; intros x;
        try (clear w0 θ)
    | |- context[@lk ?Θ (ctx.snoc ?w0 ?α) ?w1 ?θ ?α ctx.in_zero] =>
        is_var θ;
        generalize (@lk Θ (ctx.snoc w0 α) w1 θ α ctx.in_zero);
        clear θ w0; intros ?t
    | |- context[fun w : World => Ṫy w] =>
        change_no_check (fun w : World => Ṫy w) with Ṫy
    | |- context[fun w : Ctx nat => Sem ?X w] =>
        change_no_check (fun w : World => Sem X w) with (Sem X)
    end.

Section Correctness.

  Import Pred Pred.notations.
  Import (hints) Sub.
  Import Pred.proofmode.
  Import iris.proofmode.tactics.
  Open Scope pred_scope.

  Import Pred Pred.notations.
  Import World.notations.
  Import (notations) Sem.

  #[local] Arguments Sem.decode_ty : simpl never.
  #[local] Arguments step : simpl never.
  (* #[local] Arguments Free.choose : simpl never. *)

  Lemma generate_sound e :
    forall (w : World) (G : Ėnv w),
      ⊢ WLP (Θ := alloc.acc_alloc) (generate e G) (fun w1 θ '(t,ee) =>
                                   G[θ] |--ₚ e; t ~> ee).
  Proof.
    induction e; cbn; intros w G; unfold T, _4; wsimpl.
    - destruct lookup eqn:?; wsimpl.
      constructor. intros ι _; pred_unfold.
      constructor. now rewrite lookup_inst Heqo.
    - constructor. intros ι _. pred_unfold. constructor.
    - constructor. intros ι _. pred_unfold. constructor.
    - rewrite wlp_bind. unfold _4. cbn.
      iPoseProof (IHe1 w G) as "-#IH1". iRevert "IH1". clear IHe1.
      (* change (fun w : World => ?A w * ?B w)%type with (Prod A B). *)
      iApply (@wlp_mono alloc.acc_alloc). iIntros (w1 θ1 (t1 & e1')) "!> HT1".

      rewrite wlp_bind. unfold _4.
      iPoseProof (IHe2 w1 G[θ1]) as "-#IH2". iRevert "IH2". clear IHe2.
      iApply (@wlp_mono alloc.acc_alloc). iIntros (w2 θ2 (t2 & e2')) "!> HT2".

      rewrite wlp_bind. unfold _4.
      iPoseProof (IHe3 w2 G[θ1 ⊙ θ2]) as "-#IH3". iRevert "IH3". clear IHe3.
      iApply (@wlp_mono alloc.acc_alloc). iIntros (w3 θ3 (t3 & e3')) "!> HT3". cbn.
      iIntros "Heq1 Heq2". wsimpl.
      iStopProof. constructor. intros ι (HT1 & HT2 & HT3 & Heq1 & Heq2).
      pred_unfold. constructor; auto.

    - iIntros "!>".
      rewrite wlp_bind. unfold _4. cbn - [step].
      iPoseProof (IHe (w ▻ ctx.length w) (G[step] ,, x∷ṫy.var ctx.in_zero))
                    as "-#IH". iRevert "IH". clear IHe.
      iApply (@wlp_mono alloc.acc_alloc). iIntros (w1 θ1 (t1 & e1')).
      iIntros "!> HT". rewrite persist_insert. wsimpl.
      iStopProof. constructor. intros ι HT1. pred_unfold.
      rewrite inst_insert in HT1. now constructor.
    - rewrite wlp_bind. unfold _4. cbn.
      iPoseProof (IHe _ (G ,, x∷lift t w)) as "-#IH". iRevert "IH". clear IHe.
      iApply (@wlp_mono alloc.acc_alloc). iIntros (w1 θ1 (t1 & e1')) "!> HT". cbn.
      rewrite persist_insert. wsimpl.
      iStopProof. constructor. intros ι HT1. pred_unfold. wsimpl.
      rewrite inst_insert inst_lift in HT1. now constructor.
    - rewrite wlp_bind. unfold _4.
      iPoseProof (IHe1 w G) as "-#IH". iRevert "IH". clear IHe1.
      iApply (@wlp_mono alloc.acc_alloc). iIntros (w1 r1 (t12 & e1')) "!> HT1".
      rewrite wlp_bind. unfold _4.
      iPoseProof (IHe2 w1 G[r1]) as "-#IH". iRevert "IH". clear IHe2.
      iApply (@wlp_mono alloc.acc_alloc). iIntros (w2 r2 (t2 & e2')) "!> HT2". cbn.
      unfold _4. rewrite Acc.wlp_step_reduce. iIntros (t1). wsimpl.
      iStopProof. constructor. intros ι (HT1 & HT2). pred_unfold. wsimpl.
      econstructor; eauto.
  Qed.

  Lemma generate_complete_aux {G e t ee} (T : G |-- e ∷ t ~> ee) :
    forall w0 (G0 : Ėnv w0),
      ⊢ lift G _ =ₚ G0 →
      WP (Θ := alloc.acc_alloc) (generate e G0)
          (fun w1 r01 '(t',e') => lift t w1 =ₚ t' /\ₚ Sem.pure ee =ₚ e')%P.
  Proof.
    induction T as [G x t Hres|G|G|G e1 e1' e2 e2' e3 e3' t _ IH1 _ IH2 _ IH3
      |G x t1 t2 e e' _ IH|G x t1 t2 e e' _ IH|G e1 t2 e1' e2 t1 e2' _ IH1 _ IH2];
      intros w0 G0; wsimpl; unfold _4, Worlds.T.

    - constructor. intros ι. pred_unfold.
      intros _ ->.
      rewrite lookup_inst in Hres.
      destruct lookup.
      + injection Hres. cbn. intros <-. cbn. now pred_unfold.
      + discriminate Hres.

    - iIntros "#HeqG".
      rewrite wp_bind. unfold _4.
      iPoseProof (IH1 w0 G0 with "HeqG") as "-#IH". clear IH1. iRevert "IH".
      iApply (@wp_mono alloc.acc_alloc). iIntros (w1 r1 (t1 & e1'')) "!> (#Heq1 & #Heq2)". wsimpl.

      rewrite wp_bind. unfold _4.
      iPoseProof (IH2 w1 G0[r1] with "HeqG") as "-#IH". clear IH2. iRevert "IH".
      iApply (@wp_mono alloc.acc_alloc). iIntros (w2 r2 (t2 & e2'')) "!> (#Heq3 & #Heq4)". wsimpl.

      rewrite wp_bind. unfold _4.
      iPoseProof (IH3 w2 G0 with "HeqG") as "-#IH". clear IH3. iRevert "IH".
      iApply (@wp_mono alloc.acc_alloc). iIntros (w3 r3 (t3 & e3'')) "!> (#Heq5 & #Heq6)". wsimpl.

      iStopProof. constructor. intros ι [_ [(HeqG & Heq1 & Heq2 & Heq3 & Heq4 & Heq5 & Heq6)]].
      pred_unfold. wsimpl. now subst.

    - iIntros "#HeqG". rewrite Acc.wp_step_reduce. iExists (lift t1 _). iIntros "!> #Heq1".
      rewrite wp_bind. unfold _4. wsimpl.
      iPoseProof (IH _ (G0 ,, x∷ṫy.var ctx.in_zero)) as "IH". clear IH. wsimpl.
      rewrite <- eqₚ_insert. wsimpl.
      iPoseProof ("IH" with "HeqG Heq1") as "-#IH'"; iClear "IH". iRevert "IH'".
      iApply (@wp_mono alloc.acc_alloc).
      iIntros (w1 r1 (t2' & e1'')) "!> (#Heq2 & #Heq3)"; wsimpl.
      repeat iSplit; auto.
      iStopProof. constructor. intros ι [_ [(HeqG & Heq1 & Heq2 & Heq3)]].
      pred_unfold. wsimpl. now subst.

    - iIntros "#HeqG".
      rewrite wp_bind. unfold _4.
      iPoseProof (IH _ (G0 ,, x∷lift t1 w0)) as "IH". clear IH. wsimpl.
      rewrite <- eqₚ_insert. wsimpl.
      iPoseProof ("IH" with "HeqG") as "-#IH'"; iClear "IH". iRevert "IH'".
      iApply (@wp_mono alloc.acc_alloc).
      iIntros (w1 r1 (t2' & e'')) "!> (#Heq1 & #Heq2)"; wsimpl.
      iSplit; auto.
      iStopProof. constructor. intros ι [_ [(HeqG & Heq1 & Heq2)]].
      pred_unfold. wsimpl. now subst.

    - iIntros "#HeqG".
      rewrite wp_bind. unfold _4. wsimpl.
      iPoseProof (IH1 _ G0) as "IH"; clear IH1. wsimpl.
      iPoseProof ("IH" with "HeqG") as "-#IH'"; iClear "IH". iRevert "IH'".
      iApply (@wp_mono alloc.acc_alloc).
      iIntros (w1 r1 (tf & e1'')) "!> (#Heq1 & #Heq2)"; wsimpl.

      rewrite wp_bind. unfold _4.
      iPoseProof (IH2 w1 G0 with "HeqG") as "-#IH"; clear IH2. iRevert "IH".
      iApply (@wp_mono alloc.acc_alloc).
      iIntros (w2 r2 (t1' & e2'')) "!> (#Heq3 & #Heq4)"; wsimpl.
      rewrite Acc.wp_step_reduce.
      iExists (lift t2 w2). unfold _4. rewrite lk_refl. wsimpl.

      iStopProof. constructor. intros ι [_ [(HeqG & Heq1 & Heq2 & Heq3 & Heq4)]].
      pred_unfold. wsimpl. now subst.
  Qed.

  Lemma generate_complete (e : Exp) (w0 : World) G0 t0 e0 :
    ⊢ G0 |--ₚ e; t0 ~> e0 -∗
      WP (Θ := alloc.acc_alloc)
        (generate e G0)
        (fun w1 (θ1 : alloc.acc_alloc w0 w1) '(t1,e1) =>
           t0[θ1] =ₚ t1 /\ₚ e0[θ1] =ₚ e1).
  Proof.
    rewrite wand_is_impl.
    constructor. intros ι _ HT.
    destruct (@generate_complete_aux _ _ _ _ HT w0 G0) as [Hcompl].
    specialize (Hcompl ι (MkEmp _)). pred_unfold.
    specialize (Hcompl eq_refl). revert Hcompl.
    apply wp_mono. intros w1 θ1 [t1 e1].
    wsimpl. intros ι1 <-. pred_unfold. wsimpl.
  Qed.

  Theorem generate_correct e :
    forall w (G : Ėnv w) Q (RQ : ProperPost Q),
      WP (Θ := alloc.acc_alloc) (generate e G) Q ⊣⊢ₚ
      ∃ₚ t : Ṫy w, ∃ₚ ee : Sem Exp w, TPB G e t ee /\ₚ T Q (t,ee).
  Proof.
    intros w G Q RQ. unfold T. apply split_bientails. split.
    - iStartProof. rewrite wand_is_impl wp_impl.
      iPoseProof (@generate_sound e w G) as "-#Hsound". iRevert "Hsound".
      iApply (@wlp_mono alloc.acc_alloc). iIntros (w1 θ1 [t e']) "!> HT HQ". wsimpl.
      iStopProof. constructor. intros ι [HT HQ]. pred_unfold.
      exists (lift (inst t ι) _).
      exists (fun _ => inst e' ι). wsimpl. pred_unfold.
      split. apply HT. revert HQ. apply RQ. wsimpl.
    - iStartProof. iIntros "(%t & %ee & HT & HQ)".
      iPoseProof (generate_complete with "HT") as "-#Hcompl".
      iRevert "Hcompl".
      iApply (@wp_mono alloc.acc_alloc).
      iIntros (w1 θ1 [t1 e1]) "!> [Heqt Heqe]".
      iStopProof. constructor. intros ι (HQ & Heqt & Heqe). pred_unfold.
      revert HQ. apply RQ. wsimpl. f_equal; auto.
  Qed.

  Theorem generate_correct' e :
    forall w (G : Ėnv w) Q (RQ : ProperPost Q),
      WLP (Θ := alloc.acc_alloc) (generate e G) Q ⊣⊢ₚ
      ∀ₚ t : Ṫy w, ∀ₚ ee : Sem Exp w, TPB G e t ee ->ₚ T Q (t,ee).
  Proof.
    intros w G Q RQ. unfold T. apply split_bientails. split.
    - constructor. intros ι HWLP t ee HT.
      pose proof (fromEntails (generate_complete_aux HT G) ι (MkEmp _)) as Hcompl.
      pred_unfold. specialize (Hcompl eq_refl). revert Hcompl.
      apply wp_impl. revert HWLP. apply wlp_mono.
      intros w1 θ1 [?t ?e'] ι1 <- HQ []. pred_unfold.
      revert HQ. apply RQ. wsimpl. f_equal; auto.
    - iStartProof. rewrite wand_is_impl. iIntros "HQ".
      iPoseProof (@generate_sound e w G) as "-#Hsound". iRevert "Hsound".
      iApply (@wlp_mono alloc.acc_alloc). iIntros (w1 θ1 [t e']) "!> HT". wsimpl.
      iStopProof. constructor. intros ι [HQ HT]. pred_unfold.
      specialize (HQ (lift (inst t ι) _)).
      specialize (HQ (fun _ => inst e' ι)). pred_unfold.
      specialize (HQ HT).
      revert HQ. apply RQ. wsimpl.
  Qed.

  Import (hints) Triangular.Tri.
  Import (hints) Acc.

  Theorem prenex_generate_correct (e : Exp) (w : World)
    (P : Box alloc.acc_alloc (Ṫy * Sem Exp -> Pred) w) (PP : ProperPost P) :
    wp_prenex (prenex (generate e ∅)) P ⊣⊢ₚ
      ∃ₚ t : Ṫy w, ∃ₚ ee : Sem Exp w, ∅ |--ₚ e; t ~> ee /\ₚ T P (t,ee).
  Proof. now rewrite prenex_correct generate_correct. Qed.

  Theorem prenex_generate_sound (e : Exp) (w0 : World) G0 :
    ⊢ wlp_prenex
      (prenex (generate e G0))
      (fun w1 (θ : alloc.acc_alloc w0 w1) '(t1,e1) =>
         G0[θ] |--ₚ e; t1 ~> e1).
  Proof.
    rewrite prenex_correct' generate_correct'.
    - unfold T. wsimpl.
    - intros w1 θ1 [t0 e0] [t1 e1]. wsimpl. constructor. intros ι1 Heq.
      pred_unfold. destruct Heq as [Heq1 Heq2]. now subst.
  Qed.

  Theorem prenex_generate_complete (e : Exp) (w0 : World) G0 t0 e0 :
    ⊢ G0 |--ₚ e; t0 ~> e0 ->ₚ
      wp_prenex
      (prenex (generate e G0))
      (fun w1 (θ1 : alloc.acc_alloc w0 w1) '(t1,e1) =>
         t0[θ1] =ₚ t1 /\ₚ e0[θ1] =ₚ e1).
  Proof.
    rewrite prenex_correct generate_correct.
    - unfold T. wsimpl. constructor. intros ι0 _ HT0.
      exists t0. exists e0. pred_unfold. auto.
    - intros w1 θ1 [t1 e1] [t2 e2]. wsimpl. constructor. intros ι1 Heq.
      pred_unfold. destruct Heq. now subst.
  Qed.

  Theorem reconstruct_schematic_sound e wunc t e':
    reconstruct_schematic e = Some (existT wunc (t,e')) ->
    forall ι : Assignment wunc, ∅ |-- e ∷ inst t ι ~> inst e' ι.
  Proof.
    unfold reconstruct_schematic, reconstruct_optiondiamond, optiondiamond2schematic.
    pose proof (@prenex_generate_sound e ctx.nil empty) as Hprenex.
    destruct (prenex (generate e ∅)) as [(wall & θ1 & C1 & t1 & e1)|];
      cbn in Hprenex |- *; [|discriminate].
    pose proof (@Correctness.solvelist_sound wall C1) as Hsolve.
    destruct (solvelist C1) as [(wunc' & θ2 & [])|]; cbn in *; [|discriminate].
    intros Heq. depelim Heq.
    apply Acc.entails_wlp in Hprenex.
    apply Acc.entails_wlp in Hsolve.
    intros ι.
    destruct Hsolve as [Hsolve].
    specialize (Hsolve ι I).
    destruct Hprenex as [Hprenex].
    specialize (Hprenex (inst θ2 ι) (MkEmp _) Hsolve).
    pred_unfold.
    now rewrite inst_empty in Hprenex.
  Qed.

  Theorem reconstruct_schematic_complete (e : Exp) (t : Ty) (e' : Exp) :
    ∅ |-- e ∷ t ~> e' ->
    match reconstruct_schematic e with
    | Some (existT w1 (t1,e1)) =>
        exists ι : Assignment w1,
          inst t1 ι = t /\ inst e1 ι = e'
    | None => False
    end.
  Proof.
    intros H. rewrite <- option.wp_match.
    unfold reconstruct_schematic, reconstruct_optiondiamond, optiondiamond2schematic, solveoptiondiamond.
    rewrite option.wp_map option.wp_bind.
    rewrite option.wp_match.
    pose proof (@prenex_generate_complete e ctx.nil empty (lift t _) (lift e' _)) as Hcompl.
    destruct Hcompl as [Hcompl]. pred_unfold.
    specialize (Hcompl env.nil (MkEmp _)).
    rewrite inst_empty !inst_lift in Hcompl.
    specialize (Hcompl H).
    destruct (prenex (generate e ∅)) as [(w1 & θ1 & C1 & t1 & e1)|]; cbn in *; auto.
    destruct Hcompl as (ι1 & _ & HC & Heqt & Heqe). pred_unfold. subst.
    rewrite option.wp_bind.
    pose proof (@Correctness.solvelist_complete w1 C1) as Hsolv.
    destruct Hsolv as [Hsolv]. specialize (Hsolv ι1 HC).
    rewrite option.wp_match.
    destruct (solvelist C1) as [(w2 & θ2 & [])|]; cbn in *; auto.
    destruct Hsolv as (ι2 & Heqι & _). subst.
    rewrite option.wp_match. exists ι2.
    now rewrite !inst_persist.
  Qed.

  Definition tpb_algo (e : Exp) (t : Ty) (ee : Exp) : Prop :=
    match reconstruct_schematic e with
    | Some (existT w (t', ee')) =>
        exists ι : Assignment w, inst t' ι = t /\ inst ee' ι = ee
    | None => False
    end.

  Lemma correctness (e : Exp) (t : Ty) (ee : Exp) :
    tpb empty e t ee <-> tpb_algo e t ee.
  Proof.
    split; intros HT.
    - apply (reconstruct_schematic_complete HT).
    - pose proof (reconstruct_schematic_sound e) as Hsnd. unfold tpb_algo in HT.
      destruct (reconstruct_schematic e) as [(wunc & t' & e')|].
      + destruct HT as (ι & Heq1 & Heq2). subst. apply (Hsnd _ _ _ eq_refl ι).
      + easy.
  Qed.

  Print Assumptions correctness.

End Correctness.

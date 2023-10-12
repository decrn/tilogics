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

From Coq Require Import Strings.String.
From Equations Require Import Equations.
From stdpp Require Import base gmap.
From iris Require Import proofmode.tactics.
From Em Require Import
  Environment
  Prelude
  Stlc.Alloc
  Stlc.Instantiation
  Stlc.MonadInterface
  Stlc.Persistence
  Stlc.Predicates
  Stlc.Sem
  Stlc.Spec
  Stlc.Worlds.

Import Pred Pred.notations Pred.proofmode world.notations.

Set Implicit Arguments.

#[local] Notation "s [ ζ ]" :=
  (persist s ζ)
    (at level 7, left associativity,
      format "s [ ζ ]").

Section Generator.
  Import MonadNotations.

  Context {Θ} {reflΘ : Refl Θ} {stepΘ : Step Θ} {transΘ : Trans Θ}
    {reflTransΘ : ReflTrans Θ} {lkReflΘ : LkRefl Θ} {lkTransΘ : LkTrans Θ}
    {lkStepΘ : LkStep Θ}.
  Context {M} {pureM : Pure M} {bindM : Bind Θ M} {tcM : TypeCheckM M} .

  Definition generate : Exp -> ⊧ Ėnv ⇢ Ṫy ⇢ M Ėxp :=
    fix gen e {w} Γ τ :=
      match e with
      | exp.var x =>
          match lookup x Γ with
          | Some τ' => _ <- assert τ τ' ;;
                       pure (ėxp.var x)
          | None    => fail
          end
      | exp.true  =>
          _ <- assert τ ṫy.bool ;;
          pure ėxp.true
      | exp.false =>
          _ <- assert τ ṫy.bool ;;
          pure ėxp.false
      | exp.ifte e1 e2 e3 =>
          e1' <- gen e1 Γ ṫy.bool ;;
          e2' <- gen e2 Γ[_] τ[_] ;;
          e3' <- gen e3 Γ[_] τ[_] ;;
          pure (ėxp.ifte e1'[_] e2'[_] e3')
      | exp.absu x e =>
          t1  <- pick ;;
          t2  <- pick ;;
          e'  <- gen e (Γ[_] ,, x∷t1[_]) t2 ;;
          _   <- assert (τ[_]) (ṫy.func t1[_] t2[_]) ;;
          pure (ėxp.abst x t1[_] e'[_])
      | exp.abst x t1 e =>
          t2  <- pick ;;
          e'  <- gen e (Γ[_] ,, x∷lift t1) t2 ;;
          _   <- assert (τ[_]) (ṫy.func (lift t1) t2[_]) ;;
          pure (ėxp.abst x (lift t1) e'[_])
      | exp.app e1 e2 =>
          t1  <- pick ;;
          e1' <- gen e1 Γ[_] (ṫy.func t1 τ[_]) ;;
          e2' <- gen e2 Γ[_] t1[_] ;;
          pure (ėxp.app e1'[_] e2')
      end.

  Definition generate' (e : Exp) :
    ⊧ Ėnv ⇢ M (Prod Ṫy Ėxp) :=
    fun w G =>
      τ  <- pick ;;
      e' <- generate e G[_] τ ;;
      pure (τ[_] , e').

  Import Pred.proofmode.
  Import iris.proofmode.tactics.
  Open Scope pred_scope.
  Import Pred Pred.notations.
  (* Import (notations) Sem. *)

  Context {wpM : WeakestPre Θ M} {wlpM : WeakestLiberalPre Θ M}
    {tcLogicM : TypeCheckLogicM Θ M}.

  Definition TPB_algo : ⊧ Ėnv ⇢ Const Exp ⇢ Ṫy ⇢ Ėxp ⇢ Pred :=
    fun w0 G0 e τ0 e0 =>
      WP (generate e G0 τ0) (fun w1 (θ1 : Θ w0 w1) e1 => e0[θ1] =ₚ e1).

  (* Import (hints) Pred.Acc. *)

  Lemma generate_sound_aux e :
    forall (w : World) (G : Ėnv w) (t : Ṫy w),
      ⊢ WLP (generate e G t) (fun w1 θ ee =>
                                   G[θ] |--ₚ e; t[θ] ~> ee).
  Proof.
    induction e; cbn; intros w G τ; unfold _4; predsimpl.
    - destruct lookup eqn:?; predsimpl.
      + rewrite wlp_bind wlp_assert wlp_pure. predsimpl.
        pred_unfold. intros ->. constructor.
        now rewrite lookup_inst Heqo.
      + now rewrite wlp_fail.
    - rewrite wlp_bind wlp_assert wlp_pure. predsimpl.
      pred_unfold. intros ->. constructor.
    - rewrite wlp_bind wlp_assert wlp_pure. predsimpl.
      pred_unfold. intros ->. constructor.
    - rewrite wlp_bind. iPoseProof (IHe1 _ G ṫy.bool) as "-#IH". clear IHe1.
      iApply (wlp_mono with "[] IH"). iIntros (w1 θ1 e1') "!> #HT1".
      rewrite wlp_bind. iPoseProof (IHe2 _ G[_] τ[_]) as "-#IH". clear IHe2.
      iApply (wlp_mono with "[] IH"). iIntros (w2 θ2 e2') "!> #HT2".
      rewrite wlp_bind. iPoseProof (IHe3 _ G[_] τ[_]) as "-#IH". clear IHe3.
      iApply (wlp_mono with "[] IH"). iIntros (w3 θ3 e3') "!> #HT3".
      rewrite wlp_pure. rewrite ?persist_trans; predsimpl.
      iStopProof. pred_unfold. intros (HT1 & HT2 & HT3). now constructor.

    - rewrite wlp_bind wlp_pick. iModIntro.
      rewrite wlp_bind wlp_pick. iModIntro.
      rewrite wlp_bind.

      iPoseProof (IHe _ (G[step ⊙ step] ,, x∷lk step world.in_zero) (ṫy.var world.in_zero)) as "-#IH".
      iApply (wlp_mono with "[] IH"). iIntros (w1 θ1 e1') "!> #HT1".
      rewrite wlp_bind wlp_assert wlp_pure. iIntros "#Heq1". predsimpl.
      rewrite ?lk_trans ?lk_step; predsimpl.
      repeat
        match goal with
        | |- context[@lk ?Θ ?w0 ?w1 ?θ ?α ?αIn] =>
            is_var θ;
            generalize (@lk Θ w0 w1 θ α αIn);
            intros ?t
        end.
      iStopProof. pred_unfold. intros [HT Heq]. subst. now constructor.
    - rewrite wlp_bind wlp_pick. iModIntro.
      rewrite wlp_bind. unfold _4.
      iPoseProof (IHe _ (G[step] ,, x∷lift t) (ṫy.var world.in_zero)) as "-#IH".
      iApply (wlp_mono with "[] IH"). iIntros (w1 θ1 e1') "!> #HT1".
      rewrite wlp_bind wlp_assert wlp_pure. iIntros "#Heq". unfold _4. predsimpl.
      iStopProof. pred_unfold. intros [HT Heq]. subst. now constructor.
    - rewrite wlp_bind wlp_pick. iModIntro.
      rewrite wlp_bind. unfold _4.
      iPoseProof (IHe1 _ G[step] (ṫy.func (ṫy.var world.in_zero) τ[step])) as "-#IH".
      iApply (wlp_mono with "[] IH"). iIntros (w1 θ1 e1') "!> #HT1".
      rewrite wlp_bind.
      iPoseProof (IHe2 w1 G[step ⊙ θ1] (lk θ1 world.in_zero)) as "-#IH".
      iApply (wlp_mono with "[] IH"). iIntros (w2 r2 e2') "!> #HT2".
      rewrite wlp_pure. predsimpl.
      iStopProof. pred_unfold. intros (HT1 & HT2).
      econstructor; eauto.
  Qed.

  Lemma generate_sound (e : Exp) (w0 : World) (G0 : Ėnv w0) t0 e0 :
    TPB_algo G0 e t0 e0 ⊢ₚ G0 |--ₚ e; t0 ~> e0.
  Proof.
    iStartProof. rewrite wand_is_impl. rewrite wp_impl.
    iPoseProof (@generate_sound_aux e _ G0 t0) as "-#Hsound".
    iApply (wlp_mono with "[] Hsound"). iIntros (w1 θ1 e') "!> HT".
    predsimpl. iStopProof. pred_unfold. intros HT Heqe. now subst.
  Qed.

  Lemma generate_complete_aux {G e t ee} (T : G |-- e ∷ t ~> ee) :
    forall w0 (G0 : Ėnv w0) (t0 : Ṫy w0),
      ⊢ lift G =ₚ G0 ->ₚ
        lift t =ₚ t0 ->ₚ
      WP (generate e G0 t0)
          (fun w1 r01 e' => Sem.pure ee =ₚ e')%P.
  Proof.
    induction T as [G x t Hres|G|G|G t e1 e1' e2 e2' e3 e3' _ IH1 _ IH2 _ IH3
      |G x t1 t2 e e' _ IH|G x t1 t2 e e' _ IH|G e1 t2 e1' e2 t1 e2' _ IH1 _ IH2];
      intros w0 G0 t0; predsimpl; unfold _4.

    - destruct (G0 !! x) eqn:?.
      + rewrite wp_bind wp_assert wp_pure. predsimpl. pred_unfold. intros.
        subst. rewrite lookup_inst Heqo in Hres. now injection Hres.
      + rewrite wp_fail. pred_unfold. intros. subst.
        rewrite lookup_inst Heqo in Hres. discriminate Hres.

    - iIntros "#HeqG #Heqt". rewrite wp_bind wp_assert wp_pure. predsimpl.
      iSplit. rewrite (eqₚ_sym t0). auto. now iApply eqₚ_refl.
    - iIntros "#HeqG #Heqt". rewrite wp_bind wp_assert wp_pure. predsimpl.
      iSplit. rewrite (eqₚ_sym t0). auto. now iApply eqₚ_refl.
    - iIntros "#HeqG #Heqt". cbn.
      rewrite wp_bind. unfold _4.
      iPoseProof (eqₚ_intro (lift ty.bool)) as "Heqbool".
      iPoseProof (IH1 _ G0 ṫy.bool with "HeqG Heqbool") as "-#IH". clear IH1.
      iApply (wp_mono' with "IH"). iIntros (w1 θ1 e1'') "!> #Heq1".

      rewrite wp_bind ?persist_eq ?persist_lift.
      iPoseProof (IH2 _ G0[_] t0[_] with "HeqG Heqt") as "-#IH". clear IH2.
      iApply (wp_mono' with "IH"). iIntros (w2 θ2 e2'') "!> #Heq2".

      rewrite wp_bind ?persist_eq ?persist_lift. predsimpl.
      iPoseProof (IH3 _ G0 t0 with "HeqG Heqt") as "-#IH". clear IH3.
      iApply (wp_mono' with "IH"). iIntros (w3 θ3 e3'') "!> #Heq3".

      rewrite wp_pure. iClear "Heqbool". predsimpl.
      iStopProof. pred_unfold. intros ? (HeqG & Heqt & Heq1 & Heq2 & Heq3).
      now subst.

    - iIntros "#HeqG #Heqt".
      rewrite wp_bind wp_pick.
      iApply (Acc.intro_wp_step t1). iIntros "!> #Heq1".
      rewrite wp_bind wp_pick.
      iApply (Acc.intro_wp_step t2). iIntros "!> #Heq2".
      rewrite wp_bind. unfold _4.
      rewrite ?persist_eq ?persist_insert ?persist_lift ?persist_trans.
      cbn. rewrite ?lk_step. predsimpl.
      iPoseProof (IH _ (G0 ,, x∷ṫy.var (world.in_succ world.in_zero)) (ṫy.var world.in_zero)) as "IH".
      clear IH. rewrite lift_insert -eqₚ_insert impl_and.
      iPoseProof ("IH" with "HeqG Heq1 Heq2") as "-#IH'"; iClear "IH".
      iApply (wp_mono' with "IH'"). iIntros (w1 r1 e1'') "!> #Heq3".
      rewrite wp_bind wp_assert wp_pure. unfold _4.
      rewrite ?persist_eq ?lk_trans ?lk_refl ?lk_step ?trans_refl_r.
      cbn. rewrite ?persist_lift ?persist_trans. predsimpl.
      repeat
        match goal with
        | |- context[@lk ?Θ (world.snoc ?w0 ?α) ?w1 ?θ ?α world.in_zero] =>
            generalize (@lk Θ (world.snoc w0 α) w1 θ α world.in_zero);
            intros ?t
        end.
      iStopProof. pred_unfold. intros ι (HeqG & Heqt & Heq1 & Heq2 & Heq3).
      now subst.

    - iIntros "#HeqG #Heqt". cbn.
      rewrite wp_bind wp_pick. iApply (Acc.intro_wp_step t2).
      iIntros "!> #Heq1".
      rewrite wp_bind. rewrite ?persist_eq ?persist_lift. predsimpl.
      iPoseProof (IH _ (G0 ,, x∷lift t1) (ṫy.var world.in_zero)) as "IH".
      rewrite lift_insert -eqₚ_insert impl_and eqₚ_refl impl_true_l.
      iPoseProof ("IH" with "HeqG Heq1") as "-#IH'"; iClear "IH".
      iApply (wp_mono' with "IH'"). iIntros (w1 r1 e'') "!> #Heq2".
      rewrite wp_bind wp_assert wp_pure. unfold _4. predsimpl.
      iStopProof. pred_unfold. intros (HeqG & Heqt & Heq1 & Heq2).
      now subst.

    - iIntros "#HeqG #Heqt". rewrite wp_bind wp_pick.
      iApply (Acc.intro_wp_step t1). iIntros "!> #Heq1".
      rewrite wp_bind. unfold _4. predsimpl.
      iPoseProof (IH1 _ G0[step] (ṫy.func (ṫy.var world.in_zero) t0)) as "IH";
      cbn. rewrite eq_func impl_and.
      iPoseProof ("IH" with "HeqG Heq1 Heqt") as "-#IH'"; iClear "IH".
      iApply (wp_mono' with "IH'"). iIntros (w1 θ1 e1'') "!> #Heq2".
      rewrite wp_bind. unfold _4. cbn. predsimpl.
      iPoseProof (IH2 w1 G0 t with "HeqG Heq1") as "-#IH"; clear IH2.
      iApply (wp_mono' with "IH"). iIntros (w2 θ2 e2'') "!> #Heq3".
      rewrite wp_pure. predsimpl.

      iStopProof. pred_unfold. intros (HeqG & Heqt & Heq1 & Heq2 & Heq3).
      now subst.
  Qed.

  Lemma generate_complete (e : Exp) (w0 : World) (G0 : Ėnv w0) t0 e0 :
    G0 |--ₚ e; t0 ~> e0 ⊢ₚ TPB_algo G0 e t0 e0.
  Proof.
    unfold TPB_algo. pred_unfold. intros ι HT.
    pose proof (generate_complete_aux HT G0 t0) as [Hcompl].
    specialize (Hcompl ι (MkEmp _)). pred_unfold.
    rewrite ?inst_lift in Hcompl. specialize (Hcompl eq_refl eq_refl).
    revert Hcompl. apply wp_mono. intros w1 θ1 e1. predsimpl.
    intros ι1 <-. now pred_unfold.
  Qed.

  Lemma generate_correct {w} (Γ : Ėnv w) (e : Exp) (τ : Ṫy w) (e' : Ėxp w) :
    Γ |--ₚ e; τ ~> e' ⊣⊢ₚ TPB_algo Γ e τ e'.
  Proof. apply split_bientails; auto using generate_complete, generate_sound. Qed.

End Generator.

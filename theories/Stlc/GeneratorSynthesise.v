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
From iris Require Import
  proofmode.tactics.
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

Import world.notations.
Import Pred Pred.notations.
Import Pred.proofmode.

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

  Definition generate : Exp -> ⊧ Ėnv ⇢ M (Ṫy * Ėxp) :=
    fix gen e {w} Γ :=
      match e with
      | exp.var x =>
          match lookup x Γ with
          | Some t => pure (t , ėxp.var x)
          | None   => fail
          end
      | exp.true  => pure (ṫy.bool, ėxp.true)
      | exp.false => pure (ṫy.bool, ėxp.false)
      | exp.ifte e1 e2 e3 =>
          '(t1,e1') <- gen e1 Γ ;;
          '(t2,e2') <- gen e2 Γ[_] ;;
          '(t3,e3') <- gen e3 Γ[_] ;;
          _         <- assert ṫy.bool t1[_] ;;
          _         <- assert t2[_] t3[_] ;;
          pure (t3[_], ėxp.ifte e1'[_] e2'[_] e3'[_])
      | exp.absu x e =>
          t1       <- pick ;;
          '(t2,e') <- gen e (insert (M := Ėnv _) x t1 Γ[_]) ;;
          pure (ṫy.func t1[_] t2, ėxp.abst x t1[_] e')
      | exp.abst x t1 e =>
          '(t2,e') <- gen e (insert (M := Ėnv _) x (lift t1) Γ) ;;
          pure (ṫy.func (lift t1) t2, ėxp.abst x (lift t1) e')
      | exp.app e1 e2 =>
          '(tf, e1') <- gen e1 Γ ;;
          '(t1, e2') <- gen e2 Γ[_] ;;
          t2 <- pick ;;
          _  <- assert tf[_] (ṫy.func t1[_] t2) ;;
          pure (t2[_], ėxp.app e1'[_] e2'[_])
      end.

  Import Pred Pred.notations.
  Import Pred.proofmode.
  Import iris.proofmode.tactics.
  Open Scope pred_scope.

  Context {wpM : WeakestPre Θ M} {wlpM : WeakestLiberalPre Θ M}
    {tcLogicM : TypeCheckLogicM Θ M}.

  Definition TPB_algo : ⊧ Ėnv ⇢ Const Exp ⇢ Ṫy ⇢ Ėxp ⇢ Pred :=
    fun w0 G0 e t0 e0 =>
    WP (generate e G0)
      (fun w1 (θ1 : Θ w0 w1) '(t1,e1) =>
         t0[θ1] =ₚ t1 /\ₚ e0[θ1] =ₚ e1).

  Lemma generate_sound_aux e :
    forall (w : World) (G : Ėnv w),
      ⊢ WLP (generate e G) (fun w1 θ '(t,ee) => G[θ] |--ₚ e; t ~> ee).
  Proof.
    induction e; cbn; intros w G; unfold _4; predsimpl.
    - destruct lookup eqn:?; predsimpl.
      + rewrite wlp_pure. pred_unfold. constructor.
        now rewrite lookup_inst Heqo.
      + rewrite wlp_fail. easy.
    - rewrite wlp_pure. pred_unfold. constructor.
    - rewrite wlp_pure. pred_unfold. constructor.
    - rewrite wlp_bind. iApply (wlp_mono' $! (IHe1 _ G)).
      iIntros (w1 θ1 (t1 & e1')) "!> #HT1".
      rewrite wlp_bind. iApply (wlp_mono' $! (IHe2 _ G[_])).
      iIntros (w2 θ2 (t2 & e2')) "!> #HT2".
      rewrite wlp_bind. iApply (wlp_mono' $! (IHe3 _ G[_])).
      iIntros (w3 θ3 (t3 & e3')) "!> #HT3".
      clear IHe1 IHe2 IHe3.

      do 2 rewrite wlp_bind wlp_assert. rewrite wlp_pure.
      iIntros "#Heq1 #Heq2". predsimpl.
      iStopProof. pred_unfold. intros (HT1 & HT2 & HT3 & Heq1 & Heq2).
      subst; now constructor.

    - rewrite wlp_bind wlp_pick. iIntros "!>".
      rewrite wlp_bind. set (α := world.fresh w).
      iApply (wlp_mono' $! (IHe (w ▻ α) (G[step] ,, x∷ṫy.var world.in_zero))).
      iIntros (w1 θ1 (t1 & e1')) "!> #HT".
      rewrite wlp_pure. predsimpl.
      generalize (lk θ1 world.in_zero). intros ?τ.
      iStopProof. pred_unfold. now constructor.

    - rewrite wlp_bind. iApply (wlp_mono' $! (IHe _ (G ,, x∷lift t))).
      iIntros (w1 θ1 (t1 & e1')) "!> #HT".
      rewrite wlp_pure. predsimpl.
      iStopProof. pred_unfold. now constructor.
    - rewrite wlp_bind. iApply (wlp_mono' $! (IHe1 _ G)).
      iIntros (w1 θ1 (t1 & e1')) "!> #HT1".
      rewrite wlp_bind. iApply (wlp_mono' $! (IHe2 _ G[_])).
      iIntros (w2 θ2 (t11 & e2')) "!> #HT2".
      clear IHe1 IHe2.
      rewrite wlp_bind wlp_pick. iIntros "!>".
      rewrite wlp_bind wlp_assert. iIntros "#Heq1".
      rewrite wlp_pure. predsimpl.
      generalize (@ṫy.var (w2 ▻ world.fresh w2) (world.fresh w2)
                (@world.in_zero (world.fresh w2) w2)).
      intros τ12.
      iStopProof. pred_unfold. intros (HT1 & HT2 & Heq). subst.
      econstructor; eauto.
  Qed.

  Lemma generate_sound (e : Exp) (w0 : World) (G0 : Ėnv w0) t0 e0 :
    TPB_algo G0 e t0 e0 ⊢ₚ G0 |--ₚ e; t0 ~> e0.
  Proof.
    iStartProof. rewrite wand_is_impl. rewrite wp_impl.
    iApply (wlp_mono' $! (@generate_sound_aux e w0 G0)).
    iIntros (w1 θ1 [t e']) "!> HT". predsimpl.
    iStopProof. pred_unfold. intros HT Heq1 Heq2. now subst.
  Qed.

  Lemma generate_complete_aux {G e t ee} (T : G |-- e ∷ t ~> ee) :
    forall w0 (G0 : Ėnv w0),
      ⊢ lift G =ₚ G0 →
      WP (generate e G0)
          (fun w1 θ1 '(t',e') => lift t =ₚ t' /\ₚ Sem.pure ee =ₚ e')%P.
  Proof.
    induction T as [G x t Hres|G|G|G e1 e1' e2 e2' e3 e3' t _ IH1 _ IH2 _ IH3
      |G x t1 t2 e e' _ IH|G x t1 t2 e e' _ IH|G e1 t2 e1' e2 t1 e2' _ IH1 _ IH2];
      intros w0 G0; predsimpl; unfold _4.

    - pred_unfold. intros HEq. subst. rewrite lookup_inst in Hres.
      apply noConfusion_inv in Hres.
      destruct (G0 !! x); pred_unfold; cbn in Hres; [|easy].
      subst. now apply wp_pure; pred_unfold.

    - now rewrite wp_pure.
    - now rewrite wp_pure.

    - iIntros "#HeqG". rewrite wp_bind.
      iPoseProof (IH1 _ G0 with "HeqG") as "-#IH".
      iApply (wp_mono' with "IH").
      iIntros (w1 r1 (t1 & e1'')) "!> (#Heq1 & #Heq2)".

      predsimpl. rewrite wp_bind.
      iPoseProof (IH2 _ G0[_] with "HeqG") as "-#IH".
      iApply (wp_mono' with "IH").
      iIntros (w2 r2 (t2 & e2'')) "!> (#Heq3 & #Heq4)".
      predsimpl. rewrite wp_bind.
      iPoseProof (IH3 _ G0 with "HeqG") as "-#IH".
      iApply (wp_mono' with "IH").
      iIntros (w3 r3 (t3 & e3'')) "!> (#Heq5 & #Heq6)".
      clear IH1 IH2 IH3.
      do 2 rewrite wp_bind wp_assert. rewrite wp_pure. predsimpl.
      iStopProof. pred_unfold. intuition subst; auto.

    - iIntros "#HeqG".
      rewrite wp_bind wp_pick. predsimpl.
      iApply (Acc.intro_wp_step t1). iIntros "!> #Heq1".
      rewrite wp_bind. predsimpl.
      iPoseProof (IH _ (G0 ,, x∷ṫy.var world.in_zero)) as "IH".
      rewrite lift_insert. predsimpl.
      iPoseProof ("IH" with "HeqG Heq1") as "-#IH'"; iClear "IH".
      iApply (wp_mono' with "IH'").
      iIntros (w1 θ1 (t2' & e1'')) "!> (#Heq2 & #Heq3)".
      rewrite wp_pure. predsimpl.
      iStopProof. pred_unfold. intuition subst; auto.

    - iIntros "#HeqG".
      rewrite wp_bind. unfold _4.
      iPoseProof (IH _ (G0 ,, x∷lift t1)) as "IH".
      rewrite lift_insert. predsimpl.
      iPoseProof ("IH" with "HeqG") as "-#IH'"; iClear "IH".
      iApply (wp_mono' with "IH'").
      iIntros (w1 r1 (t2' & e'')) "!> (#Heq1 & #Heq2)".
      rewrite wp_pure. predsimpl.
      iStopProof. pred_unfold. intuition subst; auto.

    - iIntros "#HeqG".
      rewrite wp_bind. unfold _4.
      iPoseProof (IH1 _ G0) as "IH"; clear IH1.
      iPoseProof ("IH" with "HeqG") as "-#IH'"; iClear "IH".
      iApply (wp_mono' with "IH'").
      iIntros (w1 r1 (tf & e1'')) "!> (#Heq1 & #Heq2)"; predsimpl.

      rewrite wp_bind. unfold _4.
      iPoseProof (IH2 w1 G0 with "HeqG") as "-#IH"; clear IH2.
      iApply (wp_mono' with "IH").
      iIntros (w2 r2 (t1' & e2'')) "!> (#Heq3 & #Heq4)".

      rewrite wp_bind wp_pick. unfold _4.
      iApply (Acc.intro_wp_step t2). iIntros "!> #Heq5".
      rewrite wp_bind wp_assert. unfold _4.
      rewrite wp_pure. predsimpl.
      repeat (rewrite ?persist_eq ?persist_lift; predsimpl).

      generalize (@ṫy.var (w2 ▻ world.fresh w2) (world.fresh w2) (@world.in_zero (world.fresh w2) w2)). intros t2'.

      iStopProof. pred_unfold. intuition subst; auto.
  Qed.

  Lemma generate_complete  {w} (Γ : Ėnv w) (e : Exp) (τ : Ṫy w) (e' : Ėxp w) :
    Γ |--ₚ e; τ ~> e' ⊢ₚ TPB_algo Γ e τ e'.
  Proof.
    pred_unfold. intros ι HT.
    destruct (generate_complete_aux HT Γ) as [Hcompl].
    specialize (Hcompl ι (MkEmp _)). pred_unfold.
    rewrite inst_lift in Hcompl.
    specialize (Hcompl eq_refl). revert Hcompl.
    apply wp_mono. intros w1 θ1 [τ1 e1]. cbn.
    pred_unfold. intuition subst; auto.
  Qed.

  Lemma generate_correct {w} (Γ : Ėnv w) (e : Exp) (τ : Ṫy w) (e' : Ėxp w) :
    Γ |--ₚ e; τ ~> e' ⊣⊢ₚ TPB_algo Γ e τ e'.
  Proof. apply split_bientails; auto using generate_complete, generate_sound. Qed.

End Generator.

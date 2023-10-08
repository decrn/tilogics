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
  Stlc.Symbolic.Free
  Stlc.Unification
  Stlc.Worlds.

Import world.notations.
Import World.notations.

Set Implicit Arguments.

#[local] Notation "s [ ζ ]" :=
  (persist s ζ)
    (at level 8, left associativity,
      format "s [ ζ ]").

Section Generate.
  Import MonadNotations.
  Import World.notations.

  Definition generate : Exp -> ⊧ Ėnv ̂→ Ṫy ̂→ Free Ėxp :=
    fix gen e {w} Γ τ :=
      match e with
      | exp.var x =>
          match lookup x Γ with
          | Some τ' =>
              [ θ ] _ <- assert τ τ' ;;
              Ret (ėxp.var x)
          | None   => Fail
          end
      | exp.true  =>
          [ θ ] _ <- assert τ ṫy.bool ;;
          Ret ėxp.true
      | exp.false =>
          [ θ ] _ <- assert τ ṫy.bool ;;
          Ret ėxp.false
      | exp.ifte e1 e2 e3 =>
          [ θ1 ] e1' <- gen e1 Γ ṫy.bool ;;
          [ θ2 ] e2' <- gen e2 Γ[θ1] τ[θ1] ;;
          [ θ3 ] e3' <- gen e3 Γ[θ1⊙θ2] τ[θ1⊙θ2] ;;
          Ret (ėxp.ifte e1'[θ2⊙θ3] e2'[θ3] e3')
      | exp.absu x e =>
          [ θ1 ] t1  <- choose ;;
          [ θ2 ] t2  <- choose ;;
          [ θ3 ] e'  <- gen e (Γ[θ1⊙θ2] ,, x∷t1[θ2]) t2 ;;
          [ θ4 ] _   <- assert (τ[θ1⊙θ2⊙θ3]) (ṫy.func t1[θ2⊙θ3] t2[θ3]) ;;
          Ret (ėxp.abst x t1[θ2⊙θ3⊙θ4] e'[θ4])
      | exp.abst x t1 e =>
          [ θ1 ] t2  <- choose ;;
          [ θ2 ] e'  <- gen e (Γ[θ1] ,, x∷lift t1 _) t2 ;;
          [ θ3 ] _   <- assert (τ[θ1⊙θ2]) (ṫy.func (lift t1 _) t2[θ2]) ;;
          Ret (ėxp.abst x (lift t1 _) e'[θ3])
      | exp.app e1 e2 =>
          [ θ1 ] t1  <- choose ;;
          [ θ2 ] e1' <- gen e1 Γ[θ1] (ṫy.func t1 τ[θ1]) ;;
          [ θ3 ] e2' <- gen e2 Γ[θ1⊙θ2] t1[θ2] ;;
          Ret (ėxp.app e1'[θ3] e2')
      end.

  Definition reconstruct_free (e : Exp) :
    ⊧ Ėnv ̂→ Free (Prod Ṫy Ėxp) :=
    fun w G =>
      [θ1] τ  <- choose ;;
      [θ2] e' <- generate e G[θ1] τ ;;
      Ret (τ[θ2] , e').

  Definition reconstruct_optiondiamond (e : Exp) :
    Option (Diamond alloc.acc_alloc (Ṫy * Sem Exp)) world.nil :=
    option.bind (prenex (reconstruct_free e empty)) solveoptiondiamond.

  Definition reconstruct_grounded (e : Exp) : option (Ty * Exp) :=
    option.map
      (fun '(existT w (_ , te)) => inst te (grounding w))
      (reconstruct_optiondiamond e).

End Generate.

Section Correctness.

  Import Pred Pred.notations.
  Import Pred.proofmode.
  Import iris.proofmode.tactics.
  Open Scope pred_scope.

  Import Pred Pred.notations.
  Import World.notations.
  Import (notations) Sem.

  #[local] Arguments Sem.decode_ty : simpl never.
  #[local] Arguments step : simpl never.
  (* #[local] Arguments Free.choose : simpl never. *)

  Lemma generate_sound_aux e :
    forall (w : World) (G : Ėnv w) (t : Ṫy w),
      ⊢ WLP (Θ := alloc.acc_alloc) (generate e G t) (fun w1 θ ee =>
                                   G[θ] |--ₚ e; t[θ] ~> ee).
  Proof.
    induction e; cbn - [choose]; intros w G τ; unfold T, _4; predsimpl.
    - destruct lookup eqn:?; predsimpl.
      constructor. intros ι _; pred_unfold.
      constructor. now rewrite lookup_inst Heqo.
    - constructor. intros ι _. pred_unfold. constructor.
    - constructor. intros ι _. pred_unfold. constructor.
    - rewrite wlp_bind. unfold _4. cbn.
      iPoseProof (IHe1 w G ṫy.bool) as "-#IH1". iRevert "IH1". clear IHe1.
      iApply (@wlp_mono alloc.acc_alloc). iIntros (w1 θ1 e1') "!> HT1".

      rewrite wlp_bind. unfold _4.
      iPoseProof (IHe2 w1 G[θ1] τ[θ1]) as "-#IH2". iRevert "IH2". clear IHe2.
      iApply (@wlp_mono alloc.acc_alloc). iIntros (w2 θ2 e2') "!> HT2".

      rewrite wlp_bind. unfold _4.
      iPoseProof (IHe3 w2 G[θ1⊙θ2] τ[θ1⊙θ2]) as "-#IH3". iRevert "IH3". clear IHe3.
      iApply (@wlp_mono alloc.acc_alloc). iIntros (w3 θ3 e3') "!> HT3".
      predsimpl.
      iStopProof. constructor. intros ι (HT1 & HT2 & HT3).
      pred_unfold. constructor; auto.

    - iIntros "!> !>". rewrite wlp_bind. unfold _4. cbn.

      iPoseProof (IHe _ (G[step][step] ,, x∷lk step world.in_zero) (ṫy.var world.in_zero)) as "-#IH". iRevert "IH". clear IHe.
      iApply (@wlp_mono alloc.acc_alloc). iIntros (w1 θ1 e1').
      iIntros "!> HT Heq1". predsimpl. rewrite lk_step. cbn.
      repeat
        match goal with
        | |- context[@lk ?Θ ?w0 ?w1 ?θ ?α ?αIn] =>
            is_var θ;
            generalize (@lk Θ w0 w1 θ α αIn);
            intros ?t
        end.
      iStopProof. constructor. intros ι [HT Heq]. pred_unfold.
      rewrite inst_insert in HT. now constructor.
    - iIntros "!>". rewrite wlp_bind. unfold _4. cbn.
      iPoseProof (IHe _ (G[step] ,, x∷lift t (w ▻ world.fresh w)) (ṫy.var world.in_zero)) as "-#IH". iRevert "IH". clear IHe.
      iApply (@wlp_mono alloc.acc_alloc). iIntros (w1 θ1 e1') "!> HT". cbn.
      rewrite persist_insert. predsimpl.
      iStopProof. constructor. intros ι HT1. pred_unfold.
      rewrite inst_insert inst_lift in HT1. now constructor.
    - iIntros "!>". rewrite wlp_bind. unfold _4.
      iPoseProof (IHe1 _ G[step] (ṫy.func (ṫy.var world.in_zero) τ[step])) as "-#IH". iRevert "IH". clear IHe1.
      iApply (@wlp_mono alloc.acc_alloc). iIntros (w1 r1 e1') "!> HT1".
      rewrite wlp_bind. unfold _4.
      iPoseProof (IHe2 w1 G[step ⊙ r1] (lk r1 world.in_zero)) as "-#IH". iRevert "IH". clear IHe2.
      iApply (@wlp_mono alloc.acc_alloc). iIntros (w2 r2 e2') "!> HT2". cbn.
      predsimpl.
      iStopProof. constructor. intros ι (HT1 & HT2). pred_unfold.
      econstructor; eauto.
  Qed.

  Definition TPB_algo : ⊧ Ėnv ̂→ Const Exp ̂→ Ṫy ̂→ Ėxp ̂→ Pred :=
    fun w0 G0 e t0 e0 =>
    WP (Θ := alloc.acc_alloc)
      (reconstruct_free e G0)
      (fun w1 (θ1 : alloc.acc_alloc w0 w1) '(t1,e1) =>
         t0[θ1] =ₚ t1 /\ₚ
         e0[θ1] =ₚ e1).

  Lemma generate_sound (e : Exp) (w0 : World) (G0 : Ėnv w0) t0 e0 :
    TPB_algo G0 e t0 e0 ⊢ₚ G0 |--ₚ e; t0 ~> e0.
  Proof.
    iStartProof. rewrite wand_is_impl. rewrite wp_impl. unfold reconstruct_free.
    rewrite wlp_bind. cbn. unfold _4. iIntros "!>".
    rewrite wlp_bind. cbn. unfold _4. predsimpl.
    iPoseProof (@generate_sound_aux e _ G0[step] (ṫy.var world.in_zero)) as "-#Hsound".
    iRevert "Hsound". iApply (@wlp_mono alloc.acc_alloc). iIntros (w1 θ1 e') "!> HT".
    predsimpl. iStopProof. constructor. intros ι HT Heqt Heqe. now pred_unfold.
  Qed.

  Lemma generate_complete_aux {G e t ee} (T : G |-- e ∷ t ~> ee) :
    forall w0 (G0 : Ėnv w0) (t0 : Ṫy w0),
      ⊢ lift G _ =ₚ G0 ->ₚ
        lift t _ =ₚ t0 ->ₚ
      WP (Θ := alloc.acc_alloc) (generate e G0 t0)
          (fun w1 r01 e' => Sem.pure ee =ₚ e')%P.
  Proof.
    induction T as [G x t Hres|G|G|G t e1 e1' e2 e2' e3 e3' _ IH1 _ IH2 _ IH3
      |G x t1 t2 e e' _ IH|G x t1 t2 e e' _ IH|G e1 t2 e1' e2 t1 e2' _ IH1 _ IH2];
      intros w0 G0 t0; predsimpl; unfold _4, Worlds.T.

    - constructor. intros ι. unfold eqₚ. pred_unfold.
      intros _ -> ->.
      rewrite lookup_inst in Hres.
      destruct lookup.
      + injection Hres. now pred_unfold.
      + discriminate Hres.

    - iIntros "#HeqG #Heqt". cbn. iSplit. rewrite (eqₚ_sym t0). auto.
      now iApply eqₚ_refl.
    - iIntros "#HeqG #Heqt". cbn. iSplit. rewrite (eqₚ_sym t0). auto.
      now iApply eqₚ_refl.
    - iIntros "#HeqG #Heqt". cbn.
      rewrite wp_bind. unfold _4.
      iPoseProof (eqₚ_intro (lift ty.bool w0)) as "Heqbool".
      iPoseProof (IH1 _ G0 ṫy.bool with "HeqG Heqbool") as "-#IH". clear IH1.
      iRevert "IH".
      iApply (@wp_mono alloc.acc_alloc). iIntros (w1 r1 e1'') "!> #Heq1". predsimpl.

      rewrite wp_bind. unfold _4.
      iPoseProof (IH2 _ G0[r1] t0[r1] with "HeqG Heqt") as "-#IH". clear IH2.
      iRevert "IH".
      iApply (@wp_mono alloc.acc_alloc). iIntros (w2 r2 e2'') "!> #Heq2". predsimpl.

      rewrite wp_bind. unfold _4.
      iPoseProof (IH3 _ G0 t0 with "HeqG Heqt") as "-#IH". clear IH3.
      iRevert "IH".
      iApply (@wp_mono alloc.acc_alloc). iIntros (w3 r3 e3'') "!> #Heq3". predsimpl.

      iClear "Heqbool".
      iStopProof. constructor. intros ι [_ [(HeqG & Heqt & Heq1 & Heq2 & Heq3)]].
      now pred_unfold.

    - iIntros "#HeqG #Heqt". cbn.
      rewrite Acc.intro_wp_step.
      iExists (lift t1 _). iIntros "!> #Heq1".
      rewrite Acc.intro_wp_step.
      iExists (lift t2 _). iIntros "!> #Heq2".
      rewrite wp_bind. unfold _4. predsimpl.
      iPoseProof (IH _ (G0 ,, x∷lk step world.in_zero) (ṫy.var world.in_zero)) as "IH".
      clear IH. predsimpl.
      iPoseProof ("IH" with "HeqG Heq1 Heq2") as "-#IH'"; iClear "IH". iRevert "IH'".
      iApply (@wp_mono alloc.acc_alloc).
      iIntros (w1 r1 e1'') "!> #Heq3". predsimpl.
      repeat
        match goal with
        | |- context[@lk ?Θ (world.snoc ?w0 ?α) ?w1 ?θ ?α world.in_zero] =>
            generalize (@lk Θ (world.snoc w0 α) w1 θ α world.in_zero);
            intros ?t
        end.
      predsimpl.
      iStopProof. constructor. intros ι [_ [(HeqG & Heqt & Heq1 & Heq2 & Heq3)]].
      now pred_unfold.

    - iIntros "#HeqG #Heqt". cbn.
      rewrite Acc.intro_wp_step.
      iExists (lift t2 _). iIntros "!> #Heq1". predsimpl.

      rewrite wp_bind. unfold _4.
      iPoseProof (IH _ (G0 ,, x∷lift t1 _) (ṫy.var world.in_zero)) as "IH". clear IH.
      predsimpl.
      iPoseProof ("IH" with "HeqG Heq1") as "-#IH'"; iClear "IH". iRevert "IH'".
      iApply (@wp_mono alloc.acc_alloc).
      iIntros (w1 r1 e'') "!> #Heq2"; predsimpl.
      iStopProof. constructor. intros ι [_ [(HeqG & Heqt & Heq1 & Heq2)]].
      now pred_unfold.

    - iIntros "#HeqG #Heqt". cbn.
      rewrite Acc.intro_wp_step.
      iExists (lift t1 _). iIntros "!> #Heq1". predsimpl.
      rewrite wp_bind. unfold _4. predsimpl.
      iPoseProof (IH1 _ G0[step] (ṫy.func (ṫy.var world.in_zero) t0)) as "IH"; clear IH1.
      predsimpl.
      iPoseProof ("IH" with "HeqG Heq1 Heqt") as "-#IH'"; iClear "IH". iRevert "IH'".
      iApply (@wp_mono alloc.acc_alloc).
      iIntros (w1 r1 e1'') "!> #Heq2"; predsimpl.

      rewrite wp_bind. unfold _4. cbn.
      iPoseProof (IH2 w1 G0 t with "HeqG Heq1") as "-#IH"; clear IH2. iRevert "IH".
      iApply (@wp_mono alloc.acc_alloc).
      iIntros (w2 r2 e2'') "!> #Heq3"; predsimpl.

      iStopProof. constructor. intros ι [_ [(HeqG & Heqt & Heq1 & Heq2 & Heq3)]].
      now pred_unfold.
  Qed.

  Lemma generate_complete (e : Exp) (w0 : World) (G0 : Ėnv w0) t0 e0 :
    G0 |--ₚ e; t0 ~> e0 ⊢ₚ TPB_algo G0 e t0 e0.
  Proof.
    iIntros "HT". unfold TPB_algo, reconstruct_free. rewrite wp_bind. cbn. unfold _4.
    rewrite Acc.intro_wp_step.
    iExists t0. iIntros "!> Heq1". predsimpl.
    rewrite wp_bind. unfold _4. cbn.
    iStopProof. constructor. intros ι [HT Heq]. pred_unfold.
    pose proof (@generate_complete_aux _ _ _ _ HT _ G0 (ṫy.var world.in_zero)) as [Hcompl].
    specialize (Hcompl ι (MkEmp _)). pred_unfold.
    specialize (Hcompl eq_refl Heq). revert Hcompl.
    apply wp_mono. intros w1 θ1 e1. predsimpl.
    intros ι1 <-. now pred_unfold.
  Qed.

  Lemma generate_correct (e : Exp) (w0 : World) (G0 : Ėnv w0) t0 e0 :
    G0 |--ₚ e; t0 ~> e0 ⊣⊢ₚ TPB_algo G0 e t0 e0.
  Proof. apply split_bientails. auto using generate_complete, generate_sound. Qed.

  Import (hints) Triangular.Tri.
  Import (hints) Acc.

  Definition TPB_OD (e : Exp) (t : Ty) (ee : Exp) : Pred world.nil :=
    wp_optiondiamond (reconstruct_optiondiamond e)
      (fun w θ '(t', ee') => t' =ₚ lift t w /\ₚ ee' =ₚ lift ee w).

  Lemma proper_wp_option_bientails {A : TYPE} {w1 w2: World} (m : Option A w1) :
    Proper (pointwise_relation (A w1) bientails ==> bientails) (@wp_option A w1 w2 m).
  Proof.
    intros P Q PQ. unfold pointwise_relation in PQ.
    destruct m; cbn; easy.
  Qed.

  Lemma reconstruct_schematic_correct (e : Exp) t ee :
    ∅ |--ₚ e; lift t _ ~> lift ee _ ⊣⊢ₚ TPB_OD e t ee.
  Proof.
    rewrite generate_correct. unfold TPB_algo, TPB_OD, reconstruct_free.
    rewrite wp_bind. unfold reconstruct_optiondiamond.
    rewrite wp_optiondiamond_bind'.
    unfold reconstruct_free. cbn.
    rewrite wp_option_bind. unfold T, _4. predsimpl.
    rewrite <- prenex_correct.
    destruct prenex as [(w1 & θ1 & C & t' & ee')|]; cbn; [|now rewrite Acc.wp_false].
    unfold wp_prenex, wp_optiondiamond. predsimpl.
    rewrite wp_option_bind.
    rewrite <- solver_correct.
    destruct (solver C) as [(w2 & θ2 & [])|]; cbn.
    - rewrite Acc.and_wp_l. predsimpl. clear.
      rewrite eqₚ_sym.
      generalize (t' =ₚ lift t w2). clear. intros P.
      rewrite eqₚ_sym.
      generalize (P /\ₚ ee' =ₚ lift ee w2). clear. intros P.
      constructor; intros ι.
      destruct (env.view ι). cbn.
      split; intros [ι]; firstorder.
      exists (env.snoc env.nil _ (inst (lk θ1 world.in_zero) (inst θ2 ι))).
      split; auto.
      exists (inst θ2 ι). firstorder.
    - now rewrite and_false_l !Acc.wp_false.
  Qed.

  Definition tpb_algo (e : Exp) (t : Ty) (ee : Exp) : Prop :=
    match reconstruct_optiondiamond e with
    | Some (existT w (_ , (t', ee'))) =>
        exists ι : Assignment w, inst t' ι = t /\ inst ee' ι = ee
    | None => False
    end.

  Lemma correctness (e : Exp) (t : Ty) (ee : Exp) :
    tpb empty e t ee <-> tpb_algo e t ee.
  Proof.
    generalize (reconstruct_schematic_correct e t ee).
    unfold TPB_OD, tpb_algo.
    intros [HE]. specialize (HE env.nil). pred_unfold.
    rewrite inst_empty in HE. rewrite HE. clear HE.
    destruct reconstruct_optiondiamond as [(w & θ & [t' ee'])|]; cbn; auto.
    apply base.exist_proper. intros ι. pred_unfold. intuition.
  Qed.

End Correctness.

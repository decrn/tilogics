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

  Existing Class acc.
  Existing Instance trans.
  Hint Mode acc - + - : typeclass_instances.

  Definition generate : Exp -> ⊧ Ėnv ̂→ Free (Ṫy * Ėxp) :=
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
          [ _ ] '(t1,e1') <- gen e1 Γ ;;
          [ _ ] '(t2,e2') <- gen e2 Γ[_] ;;
          [ _ ] '(t3,e3') <- gen e3 Γ[_] ;;
          [ _ ] _         <- assert ṫy.bool t1[_] ;;
          [ _ ] _         <- assert t2[_] t3[_] ;;
          Ret (t3[_], ėxp.ifte e1'[_] e2'[_] e3'[_])
      | exp.absu x e =>
          [ _ ] t1       <- choose ;;
          [ _ ] '(t2,e') <- gen e (Γ[_] ,, x∷t1) ;;
          Ret (ṫy.func t1[_] t2, ėxp.abst x t1[_] e')
      | exp.abst x t1 e =>
          [ _ ] '(t2,e') <- gen e (Γ ,, x∷lift t1 _) ;;
          Ret (ṫy.func (lift t1 _) t2, ėxp.abst x (lift t1 _) e')
      | exp.app e1 e2 =>
          [ _ ] '(tf, e1') <- gen e1 Γ ;;
          [ _ ] '(t1, e2') <- gen e2 Γ[_] ;;
          [ _ ] t2 <- choose ;;
          [ _ ] _  <- assert tf[_] (ṫy.func t1[_] t2) ;;
          Ret (t2[_], ėxp.app e1'[_] e2'[_])
      end.

End Generate.

Section Reconstruct.

  Definition reconstruct_optiondiamond (e : Exp) :
    Option (Diamond alloc.acc_alloc (Ṫy * Sem Exp)) world.nil :=
    option.bind (prenex (generate e ∅)) solveoptiondiamond.

  Definition reconstruct_grounded (e : Exp) : option (Ty * Exp) :=
    option.map
      (fun '(existT w (_ , te)) => inst te (grounding w))
      (reconstruct_optiondiamond e).

End Reconstruct.

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

  Definition TPB_algo : ⊧ Ėnv ̂→ Const Exp ̂→ Ṫy ̂→ Ėxp ̂→ Pred :=
    fun w0 G0 e t0 e0 =>
    WP (Θ := alloc.acc_alloc)
      (generate e G0)
      (fun w1 (θ1 : alloc.acc_alloc w0 w1) '(t1,e1) =>
         t0[θ1] =ₚ t1 /\ₚ e0[θ1] =ₚ e1).

  Create HintDb psimpl.
  #[local] Hint Rewrite @inst_refl @inst_insert @inst_lift : psimpl.

  Ltac psimplnew :=
    autorewrite with psimpl in *; auto with typeclass_instances.

  Lemma generate_sound_aux e :
    forall (w : World) (G : Ėnv w),
      ⊢ WLP (Θ := alloc.acc_alloc) (generate e G) (fun w1 θ '(t,ee) =>
                                   G[θ] |--ₚ e; t ~> ee).
  Proof.
    induction e; cbn; intros w G; unfold T, _4; predsimpl.
    - destruct lookup eqn:?; predsimpl. pred_unfold.
      constructor. now rewrite lookup_inst Heqo.
    - pred_unfold. constructor.
    - pred_unfold. constructor.
    - rewrite wlp_bind. unfold _4. cbn.
      iPoseProof (IHe1 w G) as "-#IH1". iRevert "IH1". clear IHe1.
      iApply (@wlp_mono alloc.acc_alloc). iIntros (w1 θ1 (t1 & e1')) "!> HT1".

      rewrite wlp_bind. unfold _4.
      iPoseProof (IHe2 w1 G[θ1]) as "-#IH2". iRevert "IH2". clear IHe2.
      iApply (@wlp_mono alloc.acc_alloc). iIntros (w2 θ2 (t2 & e2')) "!> HT2".

      rewrite wlp_bind. unfold _4.
      iPoseProof (IHe3 w2 G[θ1 ⊙ θ2]) as "-#IH3". iRevert "IH3". clear IHe3.
      iApply (@wlp_mono alloc.acc_alloc). iIntros (w3 θ3 (t3 & e3')) "!> HT3". cbn.
      iIntros "Heq1 Heq2". predsimpl. iStopProof. pred_unfold.
      intros (HT1 & HT2 & HT3 & Heq1 & Heq2). pred_unfold. constructor; auto.

    - iIntros "!>". rewrite wlp_bind. unfold _4.
      iPoseProof (IHe (w ▻ world.fresh w) (G[step] ,, x∷ṫy.var world.in_zero))
        as "-#IH". iRevert "IH". clear IHe.
      iApply (@wlp_mono alloc.acc_alloc). iIntros (w1 θ1 (t1 & e1')).
      iIntros "!> HT". predsimpl. iStopProof. pred_unfold. constructor.
      pred_unfold. psimplnew.

    - rewrite wlp_bind. unfold _4.
      iPoseProof (IHe _ (G ,, x∷lift t w)) as "-#IH". iRevert "IH". clear IHe.
      iApply (@wlp_mono alloc.acc_alloc). iIntros (w1 θ1 (t1 & e1')) "!> HT".
      predsimpl. iStopProof. pred_unfold. constructor. psimplnew.
    - rewrite wlp_bind. unfold _4.
      iPoseProof (IHe1 w G) as "-#IH". iRevert "IH". clear IHe1.
      iApply (@wlp_mono alloc.acc_alloc). iIntros (w1 r1 (t12 & e1')) "!> HT1".
      rewrite wlp_bind. unfold _4.
      iPoseProof (IHe2 w1 G[r1]) as "-#IH". iRevert "IH". clear IHe2.
      iApply (@wlp_mono alloc.acc_alloc). iIntros (w2 r2 (t2 & e2')) "!> HT2 !>".
      unfold _4. predsimpl. iStopProof. pred_unfold.
      intros (HT1 & HT2). pred_unfold. econstructor; eauto.
  Qed.

  Lemma generate_sound (e : Exp) (w0 : World) (G0 : Ėnv w0) t0 e0 :
    TPB_algo G0 e t0 e0 ⊢ₚ G0 |--ₚ e; t0 ~> e0.
  Proof.
    iStartProof. rewrite wand_is_impl. rewrite wp_impl.
    iPoseProof (@generate_sound_aux e w0 G0) as "-#Hsound". iRevert "Hsound".
    iApply (@wlp_mono alloc.acc_alloc). iIntros (w1 θ1 [t e']) "!> HT". predsimpl.
    iStopProof. constructor. intros ι HT Heq1 Heq2. now pred_unfold.
  Qed.

  Lemma generate_complete_aux {G e t ee} (T : G |-- e ∷ t ~> ee) :
    forall w0 (G0 : Ėnv w0),
      ⊢ lift G _ =ₚ G0 →
      WP (Θ := alloc.acc_alloc) (generate e G0)
          (fun w1 r01 '(t',e') => lift t w1 =ₚ t' /\ₚ Sem.pure ee =ₚ e')%P.
  Proof.
    induction T as [G x t Hres|G|G|G e1 e1' e2 e2' e3 e3' t _ IH1 _ IH2 _ IH3
      |G x t1 t2 e e' _ IH|G x t1 t2 e e' _ IH|G e1 t2 e1' e2 t1 e2' _ IH1 _ IH2];
      intros w0 G0; predsimpl; unfold _4, Worlds.T.

    - constructor. intros ι. pred_unfold.
      intros _ ->.
      rewrite lookup_inst in Hres.
      destruct lookup.
      + injection Hres. cbn. intros <-. cbn. now pred_unfold.
      + discriminate Hres.

    - iIntros "#HeqG". rewrite wp_bind. unfold _4.
      iPoseProof (IH1 w0 G0 with "HeqG") as "-#IH". clear IH1. iRevert "IH".
      iApply (@wp_mono alloc.acc_alloc). iIntros (w1 r1 (t1 & e1'')) "!> (#Heq1 & #Heq2)".
      predsimpl. rewrite wp_bind. unfold _4.
      iPoseProof (IH2 w1 G0[r1] with "HeqG") as "-#IH". clear IH2. iRevert "IH".
      iApply (@wp_mono alloc.acc_alloc). iIntros (w2 r2 (t2 & e2'')) "!> (#Heq3 & #Heq4)".
      predsimpl. rewrite wp_bind. unfold _4.
      iPoseProof (IH3 w2 G0 with "HeqG") as "-#IH". clear IH3. iRevert "IH".
      iApply (@wp_mono alloc.acc_alloc). iIntros (w3 r3 (t3 & e3'')) "!> (#Heq5 & #Heq6)".
      predsimpl.
      iStopProof. constructor. intros ι [_ [(HeqG & Heq1 & Heq2 & Heq3 & Heq4 & Heq5 & Heq6)]].
      pred_unfold. psimplnew.

    - iIntros "#HeqG". rewrite Acc.intro_wp_step. iExists (lift t1 _). iIntros "!> #Heq1".
      rewrite wp_bind. unfold _4. predsimpl.
      iPoseProof (IH _ (G0 ,, x∷ṫy.var world.in_zero)) as "IH". clear IH. predsimpl.
      iPoseProof ("IH" with "HeqG Heq1") as "-#IH'"; iClear "IH". iRevert "IH'".
      iApply (@wp_mono alloc.acc_alloc).
      iIntros (w1 r1 (t2' & e1'')) "!> (#Heq2 & #Heq3)"; predsimpl.
      repeat iSplit; auto.
      iStopProof. constructor. intros ι [_ [(HeqG & Heq1 & Heq2 & Heq3)]].
      pred_unfold. psimplnew.

    - iIntros "#HeqG".
      rewrite wp_bind. unfold _4.
      iPoseProof (IH _ (G0 ,, x∷lift t1 w0)) as "IH". clear IH. predsimpl.
      iPoseProof ("IH" with "HeqG") as "-#IH'"; iClear "IH". iRevert "IH'".
      iApply (@wp_mono alloc.acc_alloc).
      iIntros (w1 r1 (t2' & e'')) "!> (#Heq1 & #Heq2)"; predsimpl.
      iSplit; auto.
      iStopProof. constructor. intros ι [_ [(HeqG & Heq1 & Heq2)]].
      pred_unfold. psimplnew.

    - iIntros "#HeqG".
      rewrite wp_bind. unfold _4. predsimpl.
      iPoseProof (IH1 _ G0) as "IH"; clear IH1. predsimpl.
      iPoseProof ("IH" with "HeqG") as "-#IH'"; iClear "IH". iRevert "IH'".
      iApply (@wp_mono alloc.acc_alloc).
      iIntros (w1 r1 (tf & e1'')) "!> (#Heq1 & #Heq2)"; predsimpl.

      rewrite wp_bind. unfold _4.
      iPoseProof (IH2 w1 G0 with "HeqG") as "-#IH"; clear IH2. iRevert "IH".
      iApply (@wp_mono alloc.acc_alloc).
      iIntros (w2 r2 (t1' & e2'')) "!> (#Heq3 & #Heq4)"; predsimpl.
      rewrite Acc.intro_wp_step. iExists (lift t2 w2). unfold _4. predsimpl.
      iIntros "!>". predsimpl.

      iStopProof. constructor. intros ι [_ [(HeqG & Heq1 & Heq2 & Heq3 & Heq4)]].
      pred_unfold. psimplnew.
  Qed.

  Lemma generate_complete (e : Exp) (w0 : World) (G0 : Ėnv w0) t0 e0 :
    G0 |--ₚ e; t0 ~> e0 ⊢ₚ TPB_algo G0 e t0 e0.
  Proof.
    constructor. intros ι HT.
    destruct (@generate_complete_aux _ _ _ _ HT w0 G0) as [Hcompl].
    specialize (Hcompl ι (MkEmp _)). pred_unfold.
    specialize (Hcompl eq_refl). revert Hcompl.
    apply wp_mono. intros w1 θ1 [t1 e1]. cbn.
    intros ι1 <-. pred_unfold. psimplnew.
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
    rewrite generate_correct. unfold TPB_algo, TPB_OD.
    rewrite <- prenex_correct.
    unfold reconstruct_optiondiamond.
    rewrite wp_optiondiamond_bind'.
    unfold wp_prenex.
    unfold wp_optiondiamond at 1.
    apply proper_wp_option_bientails.
    intros (w & θ & C & [t' ee']). cbn.
    rewrite wp_optiondiamond_bind'.
    rewrite <- solver_correct.
    unfold wp_optiondiamond.
    destruct (solver C) as [(w2 & θ2 & [])|]; cbn.
    - rewrite Acc.and_wp_l. predsimpl.
      rewrite eqₚ_sym.
      generalize (t' =ₚ lift t w2). clear. intros P.
      rewrite eqₚ_sym.
      generalize (P /\ₚ ee' =ₚ lift ee w2). clear. intros P.
      constructor; intros ι.
      destruct (env.view ι). cbn.
      split; intros [ι]; firstorder.
      exists (inst θ2 ι). firstorder.
    - now rewrite and_false_l Acc.wp_false.
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

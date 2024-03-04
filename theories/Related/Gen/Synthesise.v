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

Require Import Coq.Classes.RelationClasses.
From iris Require Import proofmode.tactics.
From Em Require Import BaseLogic Prefix Spec Related.Monad.Interface.
Require Import Em.Shallow.Gen.Synthesise Em.Gen.Synthesise.

Import Pred Pred.notations Pred.proofmode lr lr.notations.

#[local] Set Implicit Arguments.

Section Relatedness.

  Context `{RTypeCheckLogicM DM SM}.
  Local Set Printing Depth 16.

  Lemma relatedness_of_generators (e : Exp) :
    ℛ⟦REnv ↣ RM (RProd RTy RExp)⟧ (generate e) (synth e).
  Proof with
    iStopProof; pred_unfold; cbv [RSat RInst RExp RTy];
      pred_unfold; now intuition subst.

    induction e; iIntros (w dΓ sΓ) "#rΓ"; cbn.
    - iPoseProof (rlookup x with "rΓ") as "rlk".
      destruct (dΓ !! x), (sΓ !! x); cbn; auto.
      + iApply rpure. iSplit...
      + iApply rfail.
    - iApply rpure. iSplit...
    - iApply rpure. iSplit...
    - iApply rbind. iApply IHe1; easy. cbn.
      iIntros "%w1 %θ1 !>". iIntros ([dτ1 de1] [sτ1 se1]) "[#rτ1 #re1]".
      iApply rbind. iApply IHe2; easy.
      iIntros "%w2 %θ2 !>". iIntros ([dτ2 de2] [sτ2 se2]) "[#rτ2 #re2]".
      iApply rbind. iApply IHe3; now rewrite subst_trans.
      iIntros "%w3 %θ3 !>". iIntros ([dτ3 de3] [sτ3 se3]) "[#rτ3 #re3]".
      iApply rbind. iApply requals...
      iIntros "%w4 %θ4 !> %u1 %u2 _".
      iApply rbind. iApply requals...
      iIntros "%w5 %θ5 !> %u3 %u4 _".
      iApply rpure. iSplit...
    - iApply rbind. iApply rpick.
      iIntros "%w1 %θ1 !> %dτ1 %sτ1 #rτ1".
      iApply rbind. iApply IHe; now iApply rinsert.
      iIntros "%w2 %θ2 !>".
      iIntros ([dτ2 de2] [sτ2 se2]) "[#rτ2 #re2]".
      iApply rpure. iSplit...
    - iApply rbind. iApply IHe. iApply rinsert.
      iApply (rlift (DA := OTy)). easy.
      iIntros "%w1 %θ1 !>".
      iIntros ([dτ1 de1] [sτ1 se1]) "[#rτ1 #re]".
      iApply rpure. iSplit...
    - iApply rbind. iApply IHe1; easy.
      iIntros "%w1 %θ1 !>". iIntros ([dτ1 de1] [sτ1 se1]) "[#rτ1 #re1]".
      iApply rbind. iApply IHe2; easy.
      iIntros "%w2 %θ2 !>". iIntros ([dτ2 de2] [sτ2 se2]) "[#rτ2 #re2]".
      iApply rbind. iApply rpick.
      iIntros "%w3 %θ3 !> %dτ3 %sτ3 #rτ3".
      iApply rbind. iApply requals...
      iIntros "%w4 %θ4 !> %u1 %u2 _".
      iApply rpure. iSplit...
  Qed.

  Lemma relatedness_of_algo_typing :
    ℛ⟦REnv ↣ RConst Exp ↣ RTy ↣ RExp ↣ RPred⟧
      (TPB_algo (M := DM))
      (tpb_algorithmic (M := SM)).
  Proof.
    unfold RValid, TPB_algo, tpb_algorithmic. cbn.
    iIntros (w) "%dΓ %sΓ #rΓ %e %se %re %dτ %sτ #rτ %de1 %se1 #re2". subst se.
    iApply RWP. iApply relatedness_of_generators; auto.
    iIntros "%w1 %θ1 !>". iIntros ([dτ'' de'] [sτ' se']) "[#rτ' #re']".
    iApply rand; iApply req; auto.
  Qed.

  Lemma generate_correct_logrel `{!Shallow.Monad.Interface.TypeCheckLogicM SM}
    {w} (Γ : OEnv w) (e : Exp) (τ : OTy w) (e' : OExp w) :
    Γ |--ₚ e; τ ~> e' ⊣⊢ₚ TPB_algo (Θ := Prefix) (M := DM) Γ e τ e'.
  Proof.
    constructor.
    destruct (@relatedness_of_algo_typing w) as [HRel]. intros ι.
    specialize (HRel ι (MkEmp _)). cbn in HRel. pred_unfold.
    specialize (HRel Γ (inst Γ ι)). destruct HRel as [HRel].
    specialize (HRel eq_refl e e). destruct HRel as [HRel].
    specialize (HRel eq_refl τ (inst τ ι)). destruct HRel as [HRel].
    specialize (HRel eq_refl e' (inst e' ι)). destruct HRel as [HRel].
    specialize (HRel eq_refl).
    symmetry. cbv [RPred RSat] in HRel.
    rewrite HRel. rewrite <- synth_correct; eauto.
  Qed.

End Relatedness.

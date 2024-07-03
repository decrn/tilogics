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
Require Import Em.Shallow.Gen.Bidirectional Em.Gen.Bidirectional.

Import Pred Pred.notations Pred.proofmode lr lr.notations.

#[local] Set Implicit Arguments.

Section Relatedness.

  Context `{RTypeCheckLogicM DM SM}.

  Goal False. Proof.
  Ltac relih :=
    match goal with
    | H: _ /\ _ |- _ => destruct H
    | IH: RValid _ (ocheck ?e) (check ?e) |-
        environments.envs_entails _ (RSat (RM _)
          (ocheck ?e _ _) (check ?e _ _)) =>
        iApply IH
    | IH: RValid _ (osynth ?e) (synth ?e) |-
        environments.envs_entails _ (RSat (RM _)
          (osynth ?e _) (synth ?e _)) =>
        iApply IH
    end.
  Ltac relauto :=
    repeat first [iAssumption|relstep|relih];
    try (iStopProof; pred_unfold; cbv [RSat RInst RExp RTy];
         pred_unfold; now intuition subst).
  Abort.

  Lemma relatedness_of_generators (e : Exp) :
    ℛ⟦REnv ↣ RTy ↣ RM RExp⟧ (ocheck e) (check e) ∧
    ℛ⟦REnv ↣ RM (RProd RTy RExp)⟧ (osynth e) (synth e).
  Proof.
    induction e;
      (split; cbn; iIntros (w dΓ sΓ) "#rΓ";
       [iIntros (dτ sτ) "#rτ"|]; relauto);
    iPoseProof (rlookup x with "rΓ") as "rlk";
      destruct (dΓ !! x), (sΓ !! x); relauto.
  Qed.

  Lemma relatedness_of_algo_typing_synth :
    ℛ⟦REnv ↣ RConst Exp ↣ RTy ↣ RExp ↣ RPred⟧
      (otyping_algo_synth (M := DM))
      (typing_algo_synth (M := SM)).
  Proof.
    unfold RValid, otyping_algo_synth, typing_algo_synth. cbn.
    iIntros (w) "%dΓ %sΓ #rΓ %e %se %re %dτ %sτ #rτ %de1 %se1 #re2". subst se.
    destruct (relatedness_of_generators e) as [_ Hrel].
    iApply RWP. iApply Hrel; auto.
    iIntros "%w1 %θ1 !>". iIntros ([dτ'' de'] [sτ' se']) "[#rτ' #re']".
    iApply rand; iApply req; auto.
  Qed.

  Lemma synth_correct_logrel `{!Shallow.Monad.Interface.TypeCheckLogicM SM}
    {w} (Γ : OEnv w) (e : Exp) (τ : OTy w) (e' : OExp w) :
    otyping_algo_synth (M := DM) Γ e τ e' ⊣⊢ₚ Γ |--ₚ e; τ ~> e'.
  Proof.
    constructor. intros ι. simpl. rewrite correctness_synth.
    now apply relatedness_of_algo_typing_synth.
  Qed.

End Relatedness.

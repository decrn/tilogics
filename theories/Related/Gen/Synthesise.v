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

  (* Show that the deep and shallow constraint generators are logically related.
     Relations in this context are predicate-valued. They are binary and relate
     something that can contain variables, i.e. an [OType], with something that
     does not, i.e. a normal [Type]. We also wrap everything in a record:

       Record Rel (DA : OType) (SA : Type) : Type :=
         { RSat : ∀ w : World, DA w → SA → Pred w }.

     Note we do not define a universe of types first on which we then define a
     deep, shallow and relational semantics by recursion. We could carve out a
     subset that is contains everything that we use in the definition of the
     constraint generator, but there are some technical usability issues related
     to inverting denotations functions.
     Instead, we always quantify over these three pieces of information:
       ∀ (DA : OType) (SA : Type) (RA : Rel DA SA)
   *)
   (* The [Context] command below introduces multiple variables:
       - DM : OType → OType
         A monad that implements our constraint interface using deep embeddings
         (de Bruijn variables + string decorations) for existentials.
       - SM : Type → Type
         A monad that implements the shallow constraint interface which uses
         HOAS for existentials.
       - RM : ∀ (DA : OType) (SA : Type) (RA : Rel DA SA), Rel (DM DA) (SM SA)
         A predicate valued relation for the monads.

      The [RTypeCheckLogicM] type class requires then that all monadic operations
      (pure, bind, fail, equals, pick) and the wp and wlp semantics of DM and SM
      are logically related. *)
  Context `{RTypeCheckLogicM DM SM}.

  Goal False. Proof.
  Ltac relih :=
    match goal with
    | IH: RValid _ (osynth ?e) (synth ?e) |-
        environments.envs_entails _ (RSat (RM _) (osynth ?e _) (synth ?e _)) =>
        iApply IH
    end.
  Ltac relauto :=
    repeat first [iAssumption|relstep|relih];
    try (iStopProof; pred_unfold; cbv [RSat RInst RExp RTy];
         pred_unfold; now intuition subst).
  Abort.

  Lemma relatedness_of_generators (e : Exp) :
    ℛ⟦REnv ↣ RM (RProd RTy RExp)⟧ (osynth e) (synth e).
  Proof.
    induction e; iIntros (w dΓ sΓ) "#rΓ"; cbn; relauto.
    iPoseProof (rlookup x with "rΓ") as "rlk".
    destruct (dΓ !! x), (sΓ !! x); relauto.
  Qed.

  Lemma relatedness_of_algo_typing :
    ℛ⟦REnv ↣ RConst Exp ↣ RTy ↣ RExp ↣ RPred⟧
      (otyping_algo (M := DM))
      (typing_algo (M := SM)).
  Proof.
    unfold RValid, otyping_algo, typing_algo. cbn.
    iIntros (w) "%dΓ %sΓ #rΓ %e %se %re %dτ %sτ #rτ %de1 %se1 #re2". subst se.
    iApply RWP. iApply relatedness_of_generators; auto.
    iIntros "%w1 %θ1 !>". iIntros ([dτ'' de'] [sτ' se']) "[#rτ' #re']".
    iApply rand; iApply req; auto.
  Qed.

  Lemma generate_correct_logrel `{!Shallow.Monad.Interface.TypeCheckLogicM SM}
    {w} (Γ : OEnv w) (e : Exp) (τ : OTy w) (e' : OExp w) :
    otyping_algo (M := DM) Γ e τ e'  ⊣⊢  Γ |--ₚ e; τ ~> e'.
  Proof.
    constructor. intros ι. simpl. rewrite correctness.
    now apply relatedness_of_algo_typing.
  Qed.

End Relatedness.

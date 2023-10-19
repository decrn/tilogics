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

From Em Require Import
  Environment
  Prelude
  Stlc.Alloc
  Stlc.GeneratorSynthesise
  Stlc.Instantiation
  Stlc.Persistence
  Stlc.Predicates
  Stlc.PrenexConversion
  Stlc.MonadFree
  Stlc.Sem
  Stlc.Spec
  Stlc.Unification
  Stlc.Worlds.

Import option.notations.
Import Pred Pred.Acc.

Definition run {A} `{Persistent A} (m : Free A world.nil) :
  option { w & A w } :=
  '(existT w1 (θ1 , (xs , a))) <- (prenex m) ;;
  '(existT w2 (θ2 , _))        <- solve xs ;;
  Some (existT w2 (persist a θ2)).

Definition reconstruct (Γ : Env) (e : Exp) :
  option { w & Ṫy w * Ėxp w }%type :=
  run (generate e (lift Γ)).

Definition reconstruct_grounded (Γ : Env) (e : Exp) : option (Ty * Exp) :=
  '(existT w te) <- reconstruct Γ e ;;
  Some (inst te (grounding w)).

Definition algorithmic_typing (Γ : Env) (e : Exp) (τ : Ty) (e' : Exp) : Prop :=
  match reconstruct Γ e with
  | Some (existT w1 (τ1, e1)) =>
      exists ι : Assignment w1, inst τ1 ι = τ /\ inst e1 ι = e'
  | None => False
  end.

Lemma correctness (Γ : Env) (e : Exp) (τ : Ty) (e' : Exp) :
  algorithmic_typing Γ e τ e' <-> tpb Γ e τ e'.
Proof.
  generalize (generate_correct (w:=world.nil) (lift Γ) e (lift τ) (lift e')).
  unfold TPB_algo, algorithmic_typing, reconstruct, run. rewrite <- prenex_correct.
  destruct prenex as [(w1 & θ1 & C & t1 & e1)|]; cbn.
  - rewrite <- (solve_correct C).
    destruct (solve C) as [(w2 & θ2 & [])|]; predsimpl.
    + rewrite Acc.and_wp_l. predsimpl. unfold Acc.wp; pred_unfold.
      intros HE. specialize (HE env.nil).
      rewrite HE. clear HE.
      split.
      * intros (ι2 & Heq1 & Heq2). exists (inst θ2 ι2).
        split; [now destruct (env.view (inst θ1 (inst θ2 ι2)))|].
        exists ι2. now subst.
      * pred_unfold. intros (ι1 & Heq1 & ι2 & Heq2 & Heq3 & Heq4).
        exists ι2. now subst.
    + pred_unfold. intros HE. now specialize (HE env.nil).
  - pred_unfold. intros HE. now specialize (HE env.nil).
Qed.

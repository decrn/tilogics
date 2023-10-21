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
  extraction.ExtrHaskellBasic
  extraction.ExtrHaskellNatInt
  extraction.ExtrHaskellString
  Lists.List
  Strings.String.
From iris Require Import bi.interface bi.derived_laws proofmode.tactics.
From Em Require Import BaseLogic Gen.Synthesise PrenexConversion Spec Unification
  Prefix
  Environment
  Gen.Synthesise
  Instantiation
  Monad.Free
  Monad.Interface
  Persistence
  Prelude
  Open
  Spec
  Worlds.

Import option.notations.
Import Pred Pred.Acc.
Import ListNotations.

Definition run {A} `{Persistent A} (m : Free A world.nil) :
  option { w & A w } :=
  '(existT w1 (θ1 , (xs , a))) <- (prenex m) ;;
  '(existT w2 (θ2 , _))        <- solve xs ;;
  Some (existT w2 (persist a θ2)).

Definition reconstruct (Γ : Env) (e : Exp) :
  option { w & Ṫy w * Ėxp w }%type :=
  run (generate e (lift Γ)).

Definition infer (e : Exp) :
  option { w & Ṫy w }%type :=
  match reconstruct empty e with
  | Some (existT w (t,e)) => Some (existT w t)
  | None => None
  end.

Definition reconstruct_grounded (Γ : Env) (e : Exp) : option (Ty * Exp) :=
  '(existT w te) <- reconstruct Γ e ;;
  Some (inst te (grounding w)).

Definition reconstruct_closed (e : Exp) : option (Ty * Exp) :=
  '(existT w te) <- reconstruct empty e ;;
  Some (inst te (grounding w)).

Section Examples.
  Definition examples :=
    List.map infer
      [ exp.absu "x" (exp.var "x");
        exp.absu "x" (exp.absu "y" (exp.var "x"))
      ].

  Arguments ṫy.var {w}%world_scope α%string_scope {αIn}.
  Import world.notations.
  Notation "( x , .. , y )" := (snoc .. (snoc nil x) .. y) : world_scope.
End Examples.

(* Extraction Inline world.view. *)
Extraction Language Haskell.
Extraction Inline
  Bool.Bool.iff_reflect
  Environment.env.view
  Init.Datatypes.nat_rec
  Init.Logic.False_rec
  Init.Logic.and_rec
  Init.Logic.and_rect
  Init.Logic.eq_rec_r
  Unification.atrav
  Unification.flex
  Unification.loeb
  Unification.remove_acc_rect
  Unification.varview
  Worlds.Box
  Worlds.Impl
  Worlds.Impl
  Worlds.Valid
  Worlds.lk
  Worlds._4
  Worlds.world.view
  stdpp.base.fmap
  stdpp.gmap.gmap_fmap
  stdpp.option.option_fmap.

Extract Inductive reflect => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extract Inlined Constant Init.Datatypes.fst => "Prelude.fst".
Extract Inlined Constant Init.Datatypes.snd => "Prelude.snd".

Extraction "Infer" examples.

Definition algorithmic_typing (Γ : Env) (e : Exp) (τ : Ty) (e' : Exp) : Prop :=
  match reconstruct Γ e with
  | Some (existT w1 (τ1, e1)) =>
      exists ι : Assignment w1, inst τ1 ι = τ /\ inst e1 ι = e'
  | None => False
  end.

Lemma correctness (Γ : Env) (e : Exp) (τ : Ty) (e' : Exp) :
  algorithmic_typing Γ e τ e' <-> tpb Γ e τ e'.
Proof.
  generalize (generate_correct (M := Free) (w:=world.nil)
                (lift Γ) e (lift τ) (lift e')).
  unfold TPB_algo, algorithmic_typing, reconstruct, run.
  rewrite <- prenex_correct. destruct prenex as [(w1 & θ1 & C & t1 & e1)|]; cbn.
  - rewrite <- (solve_correct C).
    destruct (solve C) as [(w2 & θ2 & [])|]; predsimpl.
    + rewrite Acc.and_wp_l. predsimpl. unfold Acc.wp; pred_unfold.
      intros HG. rewrite (HG env.nil). clear HG. split.
      * intros (ι2 & Heq1 & Heq2). exists (inst θ2 ι2).
        split; [now destruct (env.view (inst θ1 (inst θ2 ι2)))|].
        exists ι2. now subst.
      * intros (ι1 & Heq1 & ι2 & Heq2 & Heq3 & Heq4).
        exists ι2. now subst.
    + pred_unfold. intros HE. now specialize (HE env.nil).
  - pred_unfold. intros HE. now specialize (HE env.nil).
Qed.

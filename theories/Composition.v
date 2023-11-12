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
  Logic.Decidable
  Strings.String.
From iris Require Import bi.interface bi.derived_laws proofmode.tactics.
From Em Require Import BaseLogic Gen.Synthesise PrenexConversion Spec Unification
  Gen.Synthesise
  Monad.Free
  Monad.Solved
  Sub.Parallel
  Open
  Spec.

Import Pred Pred.Sub.
Import ListNotations.
Import (hints) Par.

Section Run.
  Import MonadNotations.
  Definition run {A} `{Persistent A} : ⊧ Free A ⇢ Solved Par A :=
    fun w m =>
      '(cs,a) <- solved_hmap (prenex m) ;;
      _       <- solve cs ;;
      pure (persist a _).
End Run.

Record Result :=
  MkResult
    { unconstrained : World;
      inferred_type : OTy unconstrained;
      inferred_expr : OExp unconstrained;
    }.

Definition ground_type (r : Result) : Ty :=
  let (w,t,_) := r in inst t (grounding w).

Definition ground_expr (r : Result) : Exp :=
  let (w,_,e) := r in inst e (grounding w).

Section Reconstruct.
  Import option.notations.

  Definition reconstruct (Γ : Env) (e : Exp) : option Result :=
    '(existT w (_ , (t,e))) <- run _ (generate (w := world.nil) e (lift Γ)) ;;
    Some (MkResult w t e).

  Definition infer (e : Exp) : option Result :=
    reconstruct empty e.

End Reconstruct.

Extraction Language Haskell.
Extraction Inline
  Bool.Bool.iff_reflect
  Environment.env.view
  Init.Datatypes.nat_rec
  Init.Logic.False_rec
  Init.Logic.and_rec
  Init.Logic.and_rect
  Init.Logic.eq_rec_r
  Init.Specif.sumbool_rec
  Init.Specif.sumbool_rect
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
  stdpp.base.empty
  stdpp.base.insert
  stdpp.base.fmap
  stdpp.base.decide_rel
  stdpp.gmap.gmap_fmap
  stdpp.option.option_fmap.

Extract Inductive reflect => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extract Inlined Constant Init.Datatypes.fst => "Prelude.fst".
Extract Inlined Constant Init.Datatypes.snd => "Prelude.snd".

Extraction "Extract" ground_type ground_expr infer.

Definition algorithmic_typing (Γ : Env) (e : Exp) (τ : Ty) (e' : Exp) : Prop :=
  match reconstruct Γ e with
  | Some (MkResult w1 τ1 e1) =>
      exists ι : Assignment w1, τ = inst τ1 ι /\ e' = inst e1 ι
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
    + rewrite Sub.and_wp_l. predsimpl. unfold Sub.wp; pred_unfold.
      intros HG. rewrite (HG env.nil). clear HG. split.
      * intros (ι2 & Heq1 & Heq2). exists (inst θ2 ι2).
        split; [now destruct (env.view (inst θ1 (inst θ2 ι2)))|].
        exists ι2. now subst.
      * intros (ι1 & Heq1 & ι2 & Heq2 & Heq3 & Heq4).
        exists ι2. now subst.
    + pred_unfold. intros HE. now specialize (HE env.nil).
  - pred_unfold. intros HE. now specialize (HE env.nil).
Qed.

Lemma decidable_type_instantiation (τ : Ty) {w} (oτ : OTy w) :
  decidable (∃ ι : Assignment w, τ = inst oτ ι).
Proof.
  pose proof (mgu_correct (lift τ) oτ) as [H].
  destruct (mgu (lift τ) oτ) as [(w' & θ & [])|]; cbn in H.
  - pose (inst θ (grounding _)) as ι.
    specialize (H ι). rewrite inst_lift in H.
    left. exists ι. apply H. now exists (grounding w').
  - right. intros (ι & Heq). specialize (H ι).
    rewrite inst_lift in H. intuition auto.
Qed.

Lemma decidability Γ e τ :
  decidable (exists e', Γ |-- e ∷ τ ~> e').
Proof.
  pose proof (correctness Γ e τ) as Hcorr.
  unfold algorithmic_typing in Hcorr.
  destruct reconstruct as [[w oτ oe']|].
  - destruct (decidable_type_instantiation τ oτ) as [(ι & Heq)|].
    + left. exists (inst oe' ι). apply Hcorr. now exists ι.
    + right. intros (e' & HT). apply Hcorr in HT.
      destruct HT as (ι & Heq1 & Heq2). apply H. now exists ι.
  - right. intros (e' & HT). now apply Hcorr in HT.
Qed.

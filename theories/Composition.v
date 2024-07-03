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

From Coq Require Import Lists.List Logic.Decidable Strings.String.
From iris Require Import bi.interface bi.derived_laws proofmode.tactics.
From Em Require Import BaseLogic Gen.Synthesise PrenexConversion Spec Unification
  Gen.Synthesise Monad.Free Monad.Solved Sub.Parallel Open Spec.

Import Pred Pred.Sub.
Import ListNotations.
Import (hints) Par.

Section Run.
  Import MonadNotations.

  Definition run_prenex {A} `{Subst A} : ⊧ Prenex A ⇢ Solved Par A :=
    fun w m =>
      '(cs,a) <- solved_hmap m ;;
      _       <- solve cs ;;
      pure (subst a _).

  Definition run_free {A} `{Subst A} : ⊧ Free A ⇢ Solved Par A :=
    fun w m => run_prenex w (prenex m).

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

  Definition reconstruct_free (Γ : Env) (e : Exp) : option Result :=
    '(existT w (_ , (t,e))) <- run_free _ (osynth (w := world.nil) e (lift Γ)) ;;
    Some (MkResult w t e).

  Definition infer_free (e : Exp) : option Result :=
    reconstruct_free empty e.

  Definition reconstruct_prenex (Γ : Env) (e : Exp) : option Result :=
    '(existT w (_ , (t,e))) <- run_prenex _ (osynth (w := world.nil) e (lift Γ)) ;;
    Some (MkResult w t e).

  Definition infer_prenex (e : Exp) : option Result :=
    reconstruct_prenex empty e.

  Definition reconstruct_solved (Γ : Env) (e : Exp) : option Result :=
    '(existT w (_ , (t,e))) <- osynth (w := world.nil) e (lift Γ) ;;
    Some (MkResult w t e).

  Definition infer_solved (e : Exp) : option Result :=
    reconstruct_solved empty e.

End Reconstruct.

(* This is the end-to-end definition of an algorithmic typing relation that
   is based on the end-to-end [reconstruct] function that combines constraint
   generation and solving. *)
Definition typing_algo (Γ : Env) (e : Exp) (τ : Ty) (e' : Exp) : Prop :=
  match reconstruct_free Γ e with
  | Some (MkResult w1 τ1 e1) =>
      ∃ ι : Assignment w1, τ = inst τ1 ι ∧ e' = inst e1 ι
  | None => False
  end.

(* The correctness theorem expresses equivalence of algorithmic and
   declarative typing. *)
Theorem correctness (Γ : Env) (e : Exp) (τ : Ty) (e' : Exp) :
  typing_algo Γ e τ e' ↔ tpb Γ e τ e'.
Proof.
  generalize (ocorrectness (M := Free) (w:=world.nil)
                (lift Γ) e (lift τ) (lift e')).
  unfold otyping_algo, typing_algo, reconstruct_free, run_free.
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

(* Decide whether the open object language type [oτ] can be instantiated to the
   given closed object language type [τ], i.e. if there exists an assignment
   to the variables that can appear in [oτ] that after instantiation makes [oτ]
   equal to [τ]. *)
Lemma decidable_type_instantiation (τ : Ty) {w} (oτ : OTy w) :
  decidable (∃ ι : Assignment w, τ = inst oτ ι).
Proof.
  pose proof (mgu_correct (lift τ) oτ) as [H].
  destruct (mgu (lift τ) oτ) as [(w' & θ & [])|]; cbn in H.
  - (* In this case we get a substitution [θ] that unifies [τ] and [oτ]. After
       applying this substitution there might still be variables in the world
       which are not mentioned in [oτ]. At this point we simply ground the
       remaining ones. The actual instantation [ι] we come up with is the
       composition of the grounding with the unifying substitution. *)
    pose (inst θ (grounding _)) as ι.
    specialize (H ι). rewrite inst_lift in H.
    left. exists ι. apply H. now exists (grounding w').
  - right. intros (ι & Heq). specialize (H ι).
    rewrite inst_lift in H. intuition auto.
Qed.

(* Decide the three place typing relation. *)
Lemma decidability Γ e τ :
  decidable (exists e', Γ |-- e ∷ τ ~> e').
Proof.
  pose proof (correctness Γ e τ) as Hcorr.
  unfold typing_algo in Hcorr.
  destruct reconstruct_free as [[w oτ oe']|].
  - destruct (decidable_type_instantiation τ oτ) as [(ι & Heq)|].
    + left. exists (inst oe' ι). apply Hcorr. now exists ι.
    + right. intros (e' & HT). apply Hcorr in HT.
      destruct HT as (ι & Heq1 & Heq2). apply H. now exists ι.
  - right. intros (e' & HT). now apply Hcorr in HT.
Qed.

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

From iris Require Import proofmode.tactics.
From Em Require Export Monad.Interface Prefix.
From Em Require Import BaseLogic Spec.

Import MonadNotations Pred Pred.Sub Pred.notations Pred.proofmode
  world.notations.

#[local] Set Implicit Arguments.

#[export] Instance pure_prenex : Pure Prenex :=
  fun A w a => Some (existT w (refl, (List.nil, a))).
#[export] Instance bind_prenex : Bind Prefix Prenex :=
  fun A B w (m : Solved Prefix (List (OTy * OTy) * A) w)
      (f : Box Prefix (A ↠ Solved Prefix (List (OTy * OTy) * B)) w) =>
    '(C1,a1) <- m ;;
    '(C2,b2) <- f _ _ a1 ;;
    pure (subst C1 _ ++ C2, b2).
#[export] Instance fail_prenex : Fail Prenex :=
  fun A w => None.
#[export] Instance tcm_prenex : TypeCheckM Prenex :=
  {| equals w τ1 τ2 := Some (existT w (refl, ([(τ1,τ2)], tt)));
     pick w := let α := world.fresh w in
               Some (existT (w ، α) (step, (List.nil, oty.evar world.in_zero)));
  |}.

#[local] Existing Instance instpred_prod_ty.
#[local] Existing Instance instpred_subst_prod_ty.

#[export] Instance wp_prenex : WeakestPre Prefix Prenex :=
  fun A w o Q => wp_option o (fun d =>
    wp_diamond d (fun w1 θ1 '(C,a) => instpred C ∧ Q w1 θ1 a))%I.

#[export] Instance wlp_prenex : WeakestLiberalPre Prefix Prenex :=
  fun A w o Q => wlp_option o (fun d =>
    wlp_diamond d (fun w1 θ1 '(C,a) => instpred C → Q w1 θ1 a))%I.

#[export] Instance axiomatic_prenex : AxiomaticSemantics Prefix Prenex.
Proof.
  constructor; intros; predsimpl.
  - destruct m as [(w1 & θ1 & C1 & a1)|]; predsimpl.
    destruct f as [(w2 & θ2 & C2 & b2)|]; predsimpl.
    rewrite Sub.and_wp_r. apply Sub.proper_wp_bientails.
    rewrite bi.and_assoc. apply bi.and_proper; auto.
    rewrite instpred_list_app. apply bi.and_proper; auto.
    now rewrite instpred_subst.
  - destruct m as [(w1 & θ1 & C1 & a1)|]; predsimpl.
    iIntros "PQ". iApply Sub.wp_mono. iIntros "!> [HC HP]".
    iMod "PQ". iSplit; auto. iApply "PQ"; auto.
  - destruct m as [(w1 & θ1 & C1 & a1)|]; predsimpl.
    destruct f as [(w2 & θ2 & C2 & b2)|]; predsimpl.
    rewrite Sub.wlp_frame. apply Sub.proper_wlp_bientails.
    rewrite <- impl_and. apply bi.impl_proper; auto.
    rewrite instpred_list_app. apply bi.and_proper; auto.
    now rewrite instpred_subst_list.
  - destruct m as [(w1 & θ1 & C1 & a1)|]; predsimpl.
    iIntros "#PQ". iApply Sub.wlp_mono. iIntros "!> #HP #HC".
    iMod "PQ". iApply "PQ". now iApply "HP".
  - destruct m as [(w1 & θ1 & C1 & a1)|]; predsimpl.
    rewrite Sub.wp_impl. predsimpl.
Qed.

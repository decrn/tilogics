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
From Em Require Import BaseLogic Prefix Spec.
From Em Require Import Related.Monad.Interface.

Require Em.Monad.Free Em.Shallow.Monad.Free.

Module D := Em.Monad.Free.
Module S := Em.Shallow.Monad.Free.

Import (hints) D S.

Import Pred Pred.notations Pred.Sub Pred.proofmode world.notations.

#[local] Set Implicit Arguments.

Import lr lr.notations.

Print S.Free.
Print Pred.Sub.

Section Relation.
  Context (DA : OType) (SA : Type) (RA : Rel DA SA).

  Fixpoint RawFree [w] (d : D.Free DA w) (s : S.Free SA) {struct d} : Pred w :=
    match d , s with
    | D.Ret d            , S.Ret s            =>
        RSat RA d s
    | D.Fail             , S.Fail             =>
        True
    | D.Equalsk d1 d2 dk , S.Equalsk s1 s2 sk =>
        RSat RTy d1 s1 ∧ RSat RTy d2 s2 ∧ RawFree dk sk
    | D.Pickk α k        , S.Pickk f          =>
        wlp step (∀ τ : Ty, eqₚ (lift τ) (oty.evar world.in_zero) -∗ RawFree k (f τ))
    | _           , _         => False
    end%I.

  #[export] Instance RFree : Rel (D.Free DA) (S.Free SA) :=
    MkRel RawFree.

End Relation.

#[export] Instance rtcmfree : RTypeCheckM D.Free S.Free RFree.
Proof.
  constructor; try easy.
  - intros DA DB SA SB RA RB w.
    apply bi.forall_intro. intros da.
    induction da; iIntros "_ %sa ra %df %sf #rf";
      destruct sa; cbn - [thick]; auto.
    + iMod "rf". now iApply "rf".
    + iDestruct "ra" as "(#r1 & #r2 & #rk)". repeat iSplit; auto.
      iApply IHda; auto.
    + iApply (wlp_mono with "[] ra"). iIntros "!> #ra %t #Heq".
      iApply IHda; auto. now iApply "ra".
  - constructor; cbn. pred_unfold.
Qed.

#[export] Instance rtclogicmfree : RTypeCheckLogicM D.Free S.Free RFree rtcmfree.
Proof.
  constructor.
  - intros DA SA RA w. cbn.
    apply bi.forall_intro; intros da.
    apply bi.forall_intro; intros sa. revert w da.
    induction sa; intros w []; cbn; try easy.
    + iIntros "_ ra %DQ %SQ RQ". iMod "RQ". now iApply "RQ".
    + iIntros "_ (#r1 & #r2 & #rk) %DQ %SQ RQ".
      iApply rand; [ by iApply req | by iApply IHsa ].
    + iIntros "_ #rk %DQ %SQ RQ".
      iApply rwpstep. iIntros "!> %τ #Heq".
      iApply H. auto. now iApply "rk".
      iIntros (? ?) "!> %da %sa #ra". iMod "RQ".
      iSpecialize ("RQ" $! da sa with "ra").
      now rewrite trans_refl_r.
Qed.

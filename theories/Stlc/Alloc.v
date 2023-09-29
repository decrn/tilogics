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
  Context
  Stlc.Persistence
  Stlc.Spec
  Stlc.Worlds.

Import ctx.notations.

#[local] Set Implicit Arguments.

Module alloc.

  Inductive Alloc (w : World) : TYPE :=
    | refl         : Alloc w w
    | fresh {α w'} : Alloc (w ▻ α) w' -> Alloc w w'.
  #[global] Arguments refl {_}.
  #[global] Arguments fresh {_ _ _} _.

  Fixpoint persist_in {w0 α} (αIn : α ∈ w0) {w1} (θ : Alloc w0 w1) {struct θ} :=
    match θ with
    | refl     => αIn
    | fresh θ' => persist_in (ctx.in_succ αIn) θ'
    end.

  Canonical Structure acc_alloc : ACC :=
    {| acc              := Alloc;
       lk w0 w1 θ α αIn := ṫy.var (persist_in αIn θ)
    |}.

  #[export] Instance refl_alloc : Refl Alloc :=
    fun w => refl.
  #[export] Instance trans_alloc : Trans Alloc :=
    fix trans {w0 w1 w2} (θ1 : Alloc w0 w1) : Alloc w1 w2 -> Alloc w0 w2 :=
    match θ1 with
    | refl      => fun θ2 => θ2
    | fresh θ1' => fun θ2 => fresh (trans θ1' θ2)
    end.

  #[export] Instance step_alloc : Step Alloc :=
    fun w α => fresh refl.

  #[export] Instance refltrans_alloc : ReflTrans Alloc.
  Proof.
    constructor.
    - easy.
    - intros ? ? r; induction r; cbn; [|rewrite IHr]; easy.
    - induction r1; cbn; congruence.
  Qed.

  Lemma snoc_r {w1 w2} (r : Alloc w1 w2) :
    forall α, Alloc w1 (w2 ▻ α).
  Proof.
    induction r; cbn; intros β.
    - econstructor 2; constructor 1.
    - econstructor 2. apply IHr.
  Qed.

  Lemma nil_l {w} : Alloc ctx.nil w.
  Proof. induction w; [constructor|now apply snoc_r]. Defined.

  #[export] Instance lkrefl : LkRefl Alloc.
  Proof. easy. Qed.
  #[export] Instance lktrans : LkTrans Alloc.
  Proof.
    intros w0 w1 w2 θ1 θ2 α αIn. DepElim.hnf_eq. f_equal.
    induction θ1; cbn; [easy|]. now rewrite IHθ1.
  Qed.
  #[export] Instance lkstep : LkStep Alloc.
  Proof. easy. Qed.

  Definition incl {Θ} {reflΘ : Refl Θ} {transΘ : Trans Θ} {stepΘ : Step Θ} :=
    fix incl {w0 w1} (θ : Alloc w0 w1) : Θ w0 w1 :=
      match θ with
      | alloc.refl => Worlds.refl
      | alloc.fresh θ' => Worlds.trans step (incl θ')
      end.

  Lemma incl_alloc {w0 w1} (θ : alloc.acc_alloc w0 w1) :
      incl θ = θ.
  Proof. induction θ; cbn; now f_equal. Qed.

End alloc.
Export alloc (Alloc).
Export (hints) alloc.

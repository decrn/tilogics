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

From Em Require Import Prelude Persistence Spec Worlds.

Import world.notations.

#[local] Set Implicit Arguments.

Module prefix.

  Inductive Rel (w : World) : TYPE :=
  | refl        : Rel w w
  | snoc {w' α} : Rel w w' → Rel w (w' ▻ α).
  #[global] Arguments refl {_}.
  #[global] Arguments snoc {_ _ _} _.

  Fixpoint persist_in {w0 w1} (θ : Rel w0 w1) [α] (αIn : α ∈ w0) : α ∈ w1 :=
    match θ with
    | refl    => αIn
    | snoc θ' => world.in_succ (persist_in θ' αIn)
    end.

  Canonical Structure Prefix : SUB :=
    {| sub              := Rel;
       lk w0 w1 θ α αIn := ṫy.var (persist_in θ αIn)
    |}.

  #[export] Instance refl_prefix : Refl Prefix :=
    fun w => refl.
  #[export] Instance trans_prefix : Trans Prefix :=
    fix trans {w0 w1 w2} (θ1 : Prefix w0 w1) (θ2 : Prefix w1 w2) : Prefix w0 w2 :=
      match θ2 with
      | refl     => θ1
      | snoc θ2' => snoc (trans θ1 θ2')
      end.

  #[export] Instance step_prefix : Step Prefix :=
    fun w α => snoc refl.
  #[export] Instance refltrans_prefix : ReflTrans Prefix.
  Proof.
    constructor.
    - intros ? ? θ; induction θ; cbn; now f_equal.
    - easy.
    - intros ? ? ? ? θ1 θ2 θ3. induction θ3; cbn; now f_equal.
  Qed.

  Fixpoint nil {w} : Prefix world.nil w :=
    match w with
    | ε      => refl
    | w' ▻ α => snoc nil
    end.

  Lemma nil_unique {w} (θ : Prefix world.nil w) : nil = θ.
  Proof. induction θ; subst; auto. Qed.

  #[export] Instance lkrefl : LkRefl Prefix.
  Proof. easy. Qed.
  #[export] Instance lktrans : LkTrans Prefix.
  Proof.
    intros w0 w1 w2 θ1 θ2 α αIn. do 2 (unfold lk; cbn).
    f_equal. induction θ2; cbn; now f_equal.
  Qed.
  #[export] Instance lkstep : LkStep Prefix.
  Proof. easy. Qed.

End prefix.
Export prefix (Prefix).
Export (hints) prefix.
Notation "w1 ⊑⁺ w2" := (sub Prefix w1 w2) (at level 80).
Infix "⊙⁺" := (trans (Θ := Prefix)) (at level 60, right associativity).
Notation "□⁺ A" := (Box Prefix A)
  (at level 9, right associativity, format "□⁺ A") : indexed_scope.
Notation "◇⁺ A" := (Diamond Prefix A)
  (at level 9, right associativity, format "◇⁺ A") : indexed_scope.

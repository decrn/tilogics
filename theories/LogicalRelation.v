(******************************************************************************)
(* Copyright (c) 2022 Steven Keuchel                                          *)
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
     Definitions
     STLC
     Triangular.

Set Implicit Arguments.

#[local] Arguments Ty_hole {Σ i} xIn.
#[local] Arguments Ty_bool {Σ}.
#[local] Arguments Ty_func {Σ}.
#[local] Open Scope indexed_scope.

Module LR.

  Import (hints) Tri.

  Definition RELATION (Θ : ACC) (A : TYPE) : Type :=
    forall w0 w1 (θ01 : Θ w0 w1),
      A w0 -> A w1 -> Prop.

  Definition RProper {Θ A} {reflΘ : Refl Θ} (R : RELATION Θ A) {w} (a : A w) : Prop :=
    R w w refl a a.

  Definition RBox {Θ A} {transΘ : Trans Θ} (R : RELATION Θ A) : RELATION Θ (Box Θ A) :=
    fun w0 w1 θ01 ba0 ba1 =>
      forall (w2 w3 : World) (θ02 : Θ w0 w2) (θ13 : Θ w1 w3) (θ23 : Θ w2 w3),
        θ01 ⊙ θ13 = θ02 ⊙ θ23 ->
        R w2 w3 θ23 (ba0 w2 θ02) (ba1 w3 θ13).

  (*         Θ01          *)
  (*    w0 -------> w1    *)
  (*     |          |     *)
  (* Θ02 |          | Θ13 *)
  (*     |    //    |     *)
  (*     ↓          ↓     *)
  (*    w2 -------> w3    *)
  (*         θ23          *)

  Definition RImpl {Θ A B} (RA : RELATION Θ A) (RB : RELATION Θ B) : RELATION Θ (Impl A B) :=
    fun w0 w1 θ01 f0 f1 =>
      forall a0 a1,
        RA w0 w1 θ01 a0 a1 ->
        RB w0 w1 θ01 (f0 a0) (f1 a1).

  Definition RTy {Θ} {pers : Persistent Θ Ty} : RELATION Θ Ty :=
    fun w0 w1 θ01 t0 t1 =>
      t1 = persist _ t0 _ θ01.

  Lemma rty_bool {w0 w1} {θ01 : Tri w0 w1} :
    RTy θ01 Ty_bool Ty_bool.
  Proof. unfold RTy. now rewrite Tri.persist_bool. Qed.

  Lemma rty_func {w0 w1} (θ01 : Tri w0 w1) (t1_0 t2_0 : Ty w0) (t1_1 t2_1 : Ty w1) :
    RTy θ01 t1_0 t1_1 ->
    RTy θ01 t2_0 t2_1 ->
    RTy θ01 (Ty_func t1_0 t2_0) (Ty_func t1_1 t2_1).
  Proof. unfold RTy; intros. now rewrite Tri.persist_func; f_equal. Qed.

  Definition RValid {Θ A} (R : RELATION Θ A) (a : ⊢ A) : Prop :=
    forall w0 w1 θ01,
      R w0 w1 θ01 (a w0) (a w1).

  Definition RUnit {Θ} : RELATION Θ Unit :=
    fun _ _ _ _ _ => True.

  Definition RIff {Θ} : RELATION Θ PROP :=
    fun w0 w1 θ01 p q => (q <-> p)%type.

End LR.

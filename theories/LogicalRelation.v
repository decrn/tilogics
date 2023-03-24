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
     Predicates
     STLC
     Triangular.
From Equations Require Import
  Equations.

Set Implicit Arguments.

#[local] Arguments Ty_hole {Σ i} xIn.
#[local] Arguments Ty_bool {Σ}.
#[local] Arguments Ty_func {Σ}.
#[local] Open Scope indexed_scope.

Module LR.

  Import (hints) Tri.
  Import Pred.
  Import Pred.notations.

  #[local] Open Scope pred_scope.

  Definition RELATION (Θ : ACC) (A : TYPE) : Type :=
    forall w0 w1 (θ01 : Θ w0 w1),
      A w0 -> A w1 -> Pred w1.

  Definition RProper {Θ A} {reflΘ : Refl Θ} (R : RELATION Θ A) {w} (a : A w) : Prop :=
    entails Trueₚ (R w w refl a a).

  Definition RPred (Θ : ACC) {instΘ : forall w, Inst (Θ w) (Assignment w)} :
    RELATION Θ Pred := fun w0 w1 r01 p0 p1 => Ext p0 r01 <->ₚ p1.

  Definition RBox Θ {transΘ : Trans Θ} {instΘ : forall w, Inst (Θ w) (Assignment w)}
     {A} (R : RELATION Θ A) : RELATION Θ (Box Θ A) :=
    fun w0 w1 θ01 ba0 ba1 =>
       ∀ₚ w2 ∶ Const World,
       ∀ₚ w3 ∶ Const World,
       ∀ₚ θ02 ∶ Const (Θ w0 w2),
       ∀ₚ θ13 ∶ Const (Θ w1 w3),
       ∀ₚ θ23 ∶ Const (Θ w2 w3),
         Acc.wlp θ13
           (θ01 ⊙ θ13 =ₚ θ02 ⊙ θ23 ->ₚ
            R w2 w3 θ23 (ba0 w2 θ02) (ba1 w3 θ13)).

  (*         Θ01          *)
  (*    w0 -------> w1    *)
  (*     |          |     *)
  (* Θ02 |    //    | Θ13 *)
  (*     |          |     *)
  (*     ↓          ↓     *)
  (*    w2 -------> w3    *)
  (*         θ23          *)

  Import SigTNotations.

  Definition RDiamond Θ {transΘ : Trans Θ} {instΘ : forall w, Inst (Θ w) (Assignment w)}
    {A} (R : RELATION Θ A) : RELATION Θ (Diamond Θ A) :=
    fun w0 w1 θ01 da0 da1 =>
      match da0 , da1 with
      | (w2; (θ02,a2)) , (w3; (θ13,a3)) =>
          ∃ₚ θ23 ∶ Const (Θ w2 w3),
          Acc.wp θ13
            ((θ01 ⊙ θ13) =ₚ (θ02 ⊙ θ23) /\ₚ
             R w2 w3 θ23 a2 a3)
      end.

  Definition RImpl {Θ A B} (RA : RELATION Θ A) (RB : RELATION Θ B) : RELATION Θ (Impl A B) :=
    fun w0 w1 θ01 f0 f1 =>
      (∀ₚ a0 ∶ Const (A w0),
       ∀ₚ a1 ∶ Const (A w1),
         RA w0 w1 θ01 a0 a1 ->ₚ
         RB w0 w1 θ01 (f0 a0) (f1 a1))%P.

  Definition RTy {Θ} {pers : Persistent Θ Ty} : RELATION Θ Ty :=
    fun w0 w1 θ01 t0 t1 =>
      persist _ t0 _ θ01 =ₚ t1.

  Lemma rty_bool {w0 w1} {θ01 : Tri w0 w1} :
    ⊤ₚ ⊢ₚ RTy θ01 Ty_bool Ty_bool.
  Proof. unfold RTy. now rewrite Tri.persist_bool. Qed.

  Lemma rty_func {w0 w1} (θ01 : Tri w0 w1) (t1_0 t2_0 : Ty w0) (t1_1 t2_1 : Ty w1) :
    ⊤ₚ ⊢ₚ (RTy θ01 t1_0 t1_1 ->ₚ
           RTy θ01 t2_0 t2_1 ->ₚ
           RTy θ01 (Ty_func t1_0 t2_0) (Ty_func t1_1 t2_1)).
  Proof.
    unfold RTy. rewrite Tri.persist_func.
    rewrite (peq_ty_noconfusion (Ty_func _ _)).
    (* TODO: Don't break the abstraction. *)
    firstorder.
  Qed.

  Definition RValid {Θ A} (R : RELATION Θ A) (a : ⊢ A) : Prop :=
    forall w0 w1 θ01,
      ⊤ₚ ⊢ₚ R w0 w1 θ01 (a w0) (a w1).

  Definition RUnit {Θ} : RELATION Θ Unit :=
    fun _ _ _ _ _ => Trueₚ.

  Section Option.

    Import Prelude.option.

    Definition ROption {Θ A} (R : RELATION Θ A) : RELATION Θ (Option A) :=
      fun w0 w1 r01 m0 m1 =>
        match m0 , m1 with
        | Some a0 , Some a1 => R w0 w1 r01 a0 a1
        | Some _  , None    => Trueₚ
        | None    , Some _  => Falseₚ
        | None    , None    => Trueₚ
        end.

    Lemma proper_option_bind {Θ} {transR : Trans Θ}
      {instΘ : forall w, Inst (Θ w) (Assignment w)}
      {A B} (RA : RELATION Θ A) (RB : RELATION Θ B) :
      RValid
        (RImpl (ROption RA) (RImpl (RImpl RA (ROption RB)) (ROption RB)))
        (fun w => bind).
    Proof.
      intros w0 w1 r01.
      apply forall_r. intros m0.
      apply forall_r. intros m1.
      apply impl_and_adjoint. rewrite and_true_l.
      apply forall_r. intros f0.
      apply forall_r. intros f1.
      apply impl_and_adjoint.
      (* cbv [Entails ROption RImpl ROption PImpl Forall Const Impl Option] in *. *)
      (* intros ι [rm rf]. *)
      destruct m0 as [a0|], m1 as [a1|]; cbn.
      - rewrite and_comm. apply impl_and_adjoint.
        apply forall_l. exists a0.
        apply forall_l. exists a1.
        reflexivity.
      - now destruct (f0 a0).
      - rewrite and_false_l. easy.
      - easy.
    Qed.

  End Option.

End LR.

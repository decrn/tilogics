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
From Em Require Import Monad.Interface Prefix.

Import Pred Pred.notations Pred.Sub Pred.proofmode world.notations.

#[local] Set Implicit Arguments.

Inductive Free (A : OType) (w : World) : Type :=
| Ret (a : A w)
| Pickk α (k : Free A (w ، α)).
#[global] Arguments Ret {A} [w] a.
#[global] Arguments Pickk {A} [w] α k.

#[export] Instance pure_free : Pure Free :=
  fun A w a => Ret a.

#[export] Instance bind_free : Bind Prefix Free :=
  fun A B =>
    fix bind {w} m f {struct m} :=
    match m with
    | Ret a           => f _ refl a
    | Pickk α k     => Pickk α (bind k (_4 f step))
    end.

#[export] Instance wp_free : WeakestPre Prefix Free :=
  fun A =>
    fix WP {w} (m : Free A w) (POST : ◻(A ⇢ Pred) w) {struct m} :=
    match m with
    | Ret a => POST _ refl a
    | Pickk α k => Sub.wp step (WP k (_4 POST step))
    end%P.

#[export] Instance wlp_free : WeakestLiberalPre Prefix Free :=
  fun A =>
    fix WLP {w} (m : Free A w) (POST : ◻(A ⇢ Pred) w) {struct m} :=
    match m with
    | Ret a => POST _ refl a
    | Pickk α k => Sub.wlp step (WLP k (_4 POST step))
    end%P.

Lemma wp_free_mono [A w0] (m : Free A w0) (P Q : ◻(A ⇢ Pred) w0) :
  ◼(fun _ θ1 => ∀ₚ a, P _ θ1 a -∗ Q _ θ1 a)%P ⊢ (WP m P -∗ WP m Q).
Proof.
  induction m; cbn; iIntros "#PQ".
  - now iMod "PQ".
  - iApply Sub.wp_mono. iModIntro. iApply IHm. iIntros "%w1 %θ1 !> %a1".
    iMod "PQ". iSpecialize ("PQ" $! a1). now rewrite trans_refl_r.
Qed.

Lemma wlp_free_mono [A w0] (m : Free A w0) (P Q : ◻(A ⇢ Pred) w0) :
  ◼(fun _ θ1 => ∀ₚ a, P _ θ1 a -∗ Q _ θ1 a)%P ⊢ (WLP m P -∗ WLP m Q).
Proof.
  induction m; cbn; iIntros "#PQ".
  - now iMod "PQ".
  - iApply Sub.wlp_mono. iModIntro. iApply IHm. iIntros "%w1 %θ1 !> %a1".
    iMod "PQ". iSpecialize ("PQ" $! a1). now rewrite trans_refl_r.
Qed.

#[local] Notation "∀ x , P" :=
  (@forall_relation _ _ (fun x => P%signature))
    (at level 200, x binder, right associativity) : signature_scope.
#[local] Notation "A → P" :=
  (@pointwise_relation A%type _ P%signature) : signature_scope.

#[export] Instance proper_wp_entails {A w} (m : Free A w) :
  Proper ((∀ w1, w ⊑⁺ w1 → A w1 → (⊢ₚ)) ==> (⊢ₚ)) (WP m).
Proof.
  intros P Q PQ. iApply wp_free_mono.
  iIntros "%w1 %θ1 !> %a1". iApply PQ.
Qed.

#[export] Instance proper_wp_bientails {A w} (m : Free A w) :
  Proper ((∀ w1, w ⊑⁺ w1 → A w1 → (⊣⊢ₚ)) ==> (⊣⊢ₚ)) (WP m).
Proof.
  intros P Q PQ; iSplit; iApply proper_wp_entails;
    intros w1 θ1 a1; now rewrite (PQ w1 θ1 a1).
Qed.

#[export] Instance proper_wlp_entails {A w} (m : Free A w) :
  Proper ((∀ w1, w ⊑⁺ w1 → A w1 → (⊢ₚ)) ==> (⊢ₚ)) (WLP m).
Proof.
  intros P Q PQ. iApply wlp_free_mono.
  iIntros "%w1 %θ1 !> %a1". iApply PQ.
Qed.

#[export] Instance proper_wlp_bientails {A w} (m : Free A w):
  Proper ((∀ w1, w ⊑⁺ w1 → A w1 → (⊣⊢ₚ)) ==> (⊣⊢ₚ)) (WLP m).
Proof.
  intros P Q PQ; iSplit; iApply proper_wlp_entails;
    intros w1 θ1 a1; now rewrite (PQ w1 θ1 a1).
Qed.

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

From Equations Require Import Equations.
From Em Require Import BaseLogic Monad.Interface Parallel Triangular.

Import Pred world.notations Pred.notations.
Import (hints) Par Tri.

Set Implicit Arguments.

#[local] Notation "s [ ζ ]" :=
  (subst s ζ)
    (at level 8, left associativity,
      format "s [ ζ ]").

#[local] Notation "▷ A" :=
  (fun (w : World) => ∀ α (αIn : α ∈ w), A%W (w - α))
    (at level 9, right associativity).

(* In this section we define a generic Bove-Capretta style accessibility
   predicate for functions that recurse on smaller contexts by removing an
   element.

   See: BOVE, ANA, and VENANZIO CAPRETTA. “Modelling General Recursion in
   Type Theory.” Mathematical Structures in Computer Science, vol. 15,
   no. 4, 2005, pp. 671–708., doi:10.1017/S0960129505004822. *)
Section RemoveAcc.

  (* Coq only generates non-dependent elimination schemes for inductive
     families in Prop. Hence, we disable the automatic generation and
     define the elimination schemes for the predicate ourselves. *)
  #[local] Unset Elimination Schemes.

  Inductive remove_acc : World → Prop :=
    remove_acc_intro : ⊧ ▷remove_acc ⇢ remove_acc.

  Definition remove_acc_inv : ⊧ remove_acc ⇢ ▷remove_acc :=
    fun w d => match d with remove_acc_intro f => f end.

  (* We only define a non-dependent elimination scheme for Type. *)
  Definition remove_acc_rect (P : OType) (f : ⊧ ▷P ⇢ P) :
    ⊧ remove_acc ⇢ P :=
    fix F w (d : remove_acc w) {struct d} : P w :=
      f w (fun α αIn => F (w - α) (remove_acc_inv d αIn)).

  Fixpoint remove_acc_step {w α} (r : remove_acc w) {struct r} :
    remove_acc (world.snoc w α) :=
    remove_acc_intro
      (fun β (βIn : β ∈ world.snoc w α) =>
         match world.view βIn in @world.SnocView _ _ β βIn
               return remove_acc (world.snoc w α - β) with
         | world.isZero   => r
         | world.isSucc i => remove_acc_step (remove_acc_inv r i)
         end).

  Definition remove_acc_all : ⊧ remove_acc :=
    fix all w :=
      match w with
      | world.nil      => remove_acc_intro
                            (fun x (xIn : x ∈ world.nil) =>
                               match world.view xIn with end)
      | world.snoc w b => remove_acc_step (all w)
      end.

  Definition loeb {A : World → Type} : (⊧ ▷A ⇢ A) → (⊧ A) :=
    fun step w => remove_acc_rect step (remove_acc_all w).

  (* Derive a dependent elimination scheme for Prop. *)
  Scheme remove_acc_ind := Induction for remove_acc Sort Prop.

  #[local] Notation "▶ P" :=
    (fun (f : ▷_ _) => forall α (αIn : α ∈ _), P (_ - α) (f α αIn))
      (at level 9, right associativity).

  Definition loeb_elim {A} (step : ⊧ ▷A ⇢ A) (P : ∀ [w], A w → Prop)
    (pstep: ∀ w (f : ▷A w) (IH : ▶P f), P (step w f)) w : P (loeb step w).
  Proof. unfold loeb. induction (remove_acc_all w). eauto. Qed.

End RemoveAcc.

Section Operations.

  Definition singleton {w x} (xIn : x ∈ w) (t : OTy (w - x)) :
    Solved Tri Unit w :=
    Some (existT (w - x) (thick (Θ := Tri) x t, tt)).

End Operations.

Section Implementation.

  Definition C := Box Tri (Solved Tri Unit).

  Definition ctrue : ⊧ C :=
    fun w0 w1 r01 => pure tt.
  Definition cfalse : ⊧ C :=
    fun w0 w1 r01 => fail.
  Definition cand : ⊧ C ⇢ C ⇢ C :=
    fun w0 c1 c2 w1 r01 =>
      bind (c1 w1 r01) (fun w2 r12 _ => _4 c2 r01 r12).
  #[global] Arguments cfalse {w} [w1] _.
  #[global] Arguments ctrue {w} [w1] _.

  Definition AUnifier : OType :=
    OTy ⇢ OTy ⇢ C.

End Implementation.

Section Correctness.

  Local Existing Instance proper_subst_bientails.
  Lemma instpred_ctrue {w0 w1} (θ1 : Tri w0 w1) :
    instpred (ctrue θ1) ⊣⊢ₚ ⊤ₚ.
  Proof. cbn. now rewrite Sub.wp_refl. Qed.

  Lemma instpred_cfalse {w0 w1} (θ1 : Tri w0 w1) :
    instpred (cfalse θ1) ⊣⊢ₚ ⊥ₚ.
  Proof. reflexivity. Qed.

  Lemma instpred_cand_intro {w0} (c1 c2 : C w0) P Q :
    (∀ w1 (θ1 : Tri w0 w1), instpred (c1 w1 θ1) ⊣⊢ₚ P[θ1]) →
    (∀ w1 (θ1 : Tri w0 w1), instpred (c2 w1 θ1) ⊣⊢ₚ Q[θ1]) →
    (∀ w1 (θ1 : Tri w0 w1), instpred (cand c1 c2 θ1) ⊣⊢ₚ (P /\ₚ Q)[θ1]).
  Proof.
    unfold instpred, instpred_solved, cand. intros H1 H2 w1 θ1.
    rewrite wp_solved_bind, subst_and, <- H1, wp_solved_frame.
    unfold _4. apply proper_wp_solved_bientails. intros w2 θ2 [].
    cbn. rewrite and_true_l, <- subst_pred_trans. apply H2.
  Qed.

End Correctness.

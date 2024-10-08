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

Import Pred Pred.notations Pred.proofmode world.notations.
Import (hints) Par Tri.

Set Implicit Arguments.

#[local] Notation "s [ ζ ]" :=
  (subst s ζ)
    (at level 7, left associativity,
      format "s [ ζ ]").

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
    remove_acc_intro : ⊧ ▹remove_acc ↠ remove_acc.

  Definition remove_acc_inv : ⊧ remove_acc ↠ ▹remove_acc :=
    fun w d => match d with remove_acc_intro f => f end.

  (* We only define a non-dependent elimination scheme for Type. *)
  Definition remove_acc_rect (P : OType) (f : ⊧ ▹P ↠ P) :
    ⊧ remove_acc ↠ P :=
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

  (* Calculating the full predicate is costly. It has quadratic running
     time in the size of the context. This code is deleted in the extraction
     but for computations inside of Coq, it is better to not use this directly
     but the [remove_acc_all_gen] defined below. *)

  (* Similar to the Acc_intro_generator from the Coq standrd library.
     Adds 2ⁿ - 1 [remove_acc_intro]s to the given [all]. *)
  Fixpoint remove_acc_intro_gen (n : nat) (all : ⊧ remove_acc) : ⊧ remove_acc :=
    match n with
    | 0   => all
    | S m =>
        fun w =>
          remove_acc_intro
            (fun α αIn =>
               remove_acc_intro_gen m (remove_acc_intro_gen m all) (w - α))
    end.

  Definition remove_acc_all_gen : ⊧ remove_acc :=
    remove_acc_intro_gen 20 (remove_acc_all).

  Definition loeb {A : World → Type} : (⊧ ▹A ↠ A) → (⊧ A) :=
    fun step w => remove_acc_rect step (remove_acc_all w).

  (* Derive a dependent elimination scheme for Prop. *)
  Scheme remove_acc_ind := Induction for remove_acc Sort Prop.

  #[local] Notation "▸ P" :=
    (fun (f : ▹_ _) => ∀ α (αIn : α ∈ _), P (_ - α) (f α αIn))
      (at level 9, right associativity).

  Definition loeb_elim {A} (step : ⊧ ▹A ↠ A) (P : ∀ [w], A w → Prop)
    (pstep: ∀ w (f : ▹A w) (IH : ▸P f), P (step w f)) w : P (loeb step w).
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
  Definition cand : ⊧ C ↠ C ↠ C :=
    fun w0 c1 c2 w1 r01 =>
      bind (c1 w1 r01) (fun w2 r12 _ => _4 c2 r01 r12).
  #[global] Arguments cfalse {w} [w1] _.
  #[global] Arguments ctrue {w} [w1] _.

  Definition AUnifier : OType :=
    OTy ↠ OTy ↠ C.

End Implementation.

Section Correctness.

  Lemma instpred_ctrue {w0 w1} (θ1 : Tri w0 w1) :
    instpred (ctrue θ1) ⊣⊢ ⊤.
  Proof. cbn. now rewrite Sub.wp_refl. Qed.

  Lemma instpred_cfalse {w0 w1} (θ1 : Tri w0 w1) :
    instpred (cfalse θ1) ⊣⊢ ⊥.
  Proof. reflexivity. Qed.

  Lemma instpred_cand_intro {w0} (c1 c2 : C w0) P Q :
    (∀ w1 (θ1 : Tri w0 w1), instpred (c1 w1 θ1) ⊣⊢ P[θ1]) →
    (∀ w1 (θ1 : Tri w0 w1), instpred (c2 w1 θ1) ⊣⊢ Q[θ1]) →
    (∀ w1 (θ1 : Tri w0 w1), instpred (cand c1 c2 θ1) ⊣⊢ (P ∧ Q)[θ1]).
  Proof.
    unfold instpred, instpred_solved, cand. intros H1 H2 w1 θ1.
    rewrite wp_solved_bind subst_and -H1 wp_solved_frame.
    unfold _4. apply proper_wp_solved_bientails. intros w2 θ2 [].
    cbn. rewrite and_true_l -subst_pred_trans. apply H2.
  Qed.

End Correctness.

Section OccursCheck.
  Import option.notations.
  Import (hints) Par.

  Definition occurs_check_in : ⊧ ∀ α, (α ∈) ↠ ▹(Option (α ∈)) :=
    fun w x xIn y yIn =>
      match world.occurs_check_view yIn xIn with
      | world.Same _      => None
      | world.Diff _ xIn' => Some xIn'
      end.

  Load UnificationStlcOccursCheck.

End OccursCheck.

Section Implementation.

  Definition flex : ⊧ ∀ α, world.In α ↠ OTy ↠ Solved Tri Unit :=
    fun w α αIn τ =>
      match varview τ with
      | is_var βIn =>
          match world.occurs_check_view αIn βIn with
          | world.Same _      => pure tt
          | world.Diff _ βIn' => singleton αIn (oty.evar βIn')
          end
      | not_var _ =>
          match occurs_check τ αIn with
          | Some τ' => singleton αIn τ'
          | None    => fail
          end
      end.
  #[global] Arguments flex {w} α {αIn} τ : rename.

  Section OpenRecursion.

    Context [w] (lamgu : ▹AUnifier w).
    Arguments lamgu {_ _} _ _ {_} _.

    Definition aflex α {αIn : α ∈ w} (τ : OTy w) : C w :=
      fun _ θ =>
        match θ with
        | Tri.nil          => flex α τ
        | Tri.cons β τ' θ' => lamgu (lk (thick β τ') αIn) τ[thick β τ'] θ'
        end.
    #[global] Arguments aflex α {αIn} τ [w1] _.

    Load UnificationStlcUnifier.

  End OpenRecursion.

  Definition amgu : ⊧ AUnifier :=
    fun w => loeb atrav w.

  Definition mgu `{HMap Tri Θ} : ⊧ OTy ↠ OTy ↠ Solved Θ Unit :=
    fun w s t => solved_hmap (@amgu w s t _ refl).

  Definition asolve : ⊧ List (Prod OTy OTy) ↠ C :=
    fix asolve {w} cs {struct cs} :=
      match cs with
      | List.nil             => ctrue
      | List.cons (t1,t2) cs => cand (amgu t1 t2) (asolve cs)
      end.

  Definition solve `{HMap Tri Θ} : ⊧ List (Prod OTy OTy) ↠ Solved Θ Unit :=
    fun w cs => solved_hmap (asolve cs refl).

End Implementation.

Section Correctness.

  Definition AUnifierCorrect : ⊧ AUnifier ↠ PROP :=
    fun w0 bu =>
      ∀ (t1 t2 : OTy w0) w1 (θ1 : w0 ⊑⁻ w1),
        instpred (bu t1 t2 w1 θ1) ⊣⊢ (t1 ≈ t2)[θ1].

  Lemma flex_correct {w α} (αIn : α ∈ w) (t : OTy w) :
    instpred (flex α t) ⊣⊢ oty.evar αIn ≈ t.
  Proof.
    unfold flex. destruct varview; cbn.
    - destruct world.occurs_check_view; predsimpl.
      unfold instpred, instpred_unit.
      rewrite Sub.wp_thick; predsimpl.
      now rewrite lk_thin.
    - pose proof (occurs_check_spec αIn t) as HOC. destruct occurs_check; cbn.
      + subst. unfold instpred, instpred_unit.
        now rewrite Sub.wp_thick; predsimpl.
      + destruct HOC as [HOC|HOC].
        * subst. now contradiction (H α αIn).
        * apply pno_cycle in HOC. apply split_bientails. now split.
  Qed.

  Section InnerRecursion.

    Context [w] (lamgu : ▹AUnifier w).
    Context (lamgu_correct : ∀ x (xIn : x ∈ w), AUnifierCorrect (lamgu xIn)).

    Lemma aflex_correct {α} (αIn : α ∈ w) (t : OTy w) w1 (θ1 : w ⊑⁻ w1) :
      instpred (aflex lamgu α t θ1) ⊣⊢ (oty.evar αIn ≈ t)[θ1].
    Proof.
      destruct θ1; cbn; Tri.folddefs.
      Tri.folddefs.
      - now rewrite flex_correct subst_pred_refl.
      - now rewrite lamgu_correct !subst_eq !subst_trans.
    Qed.

    Load UnificationStlcCorrect.

  End InnerRecursion.

  Lemma amgu_correct : ∀ w, AUnifierCorrect (@amgu w).
  Proof. apply loeb_elim, atrav_correct. Qed.

  Definition mgu_correct `{LkHMap Tri Θ} w (t1 t2 : OTy w) :
    instpred (mgu (Θ := Θ) t1 t2) ⊣⊢ t1 ≈ t2.
  Proof.
    unfold mgu. rewrite instpred_solved_hmap.
    now rewrite amgu_correct subst_pred_refl.
  Qed.

  #[local] Existing Instance instpred_prod_ty.

  Lemma asolve_correct {w0} (C : List (OTy * OTy) w0) :
    ∀ w1 (θ1 : w0 ⊑⁻ w1),
      instpred (asolve C θ1) ⊣⊢ (instpred C)[θ1].
  Proof.
    induction C as [|[t1 t2]]; cbn [asolve]; intros.
    - now rewrite instpred_ctrue.
    - apply instpred_cand_intro; auto. intros. apply amgu_correct.
  Qed.

  Lemma solve_correct `{LkHMap Tri Θ} {w} (C : List (OTy * OTy) w) :
    WP (solve (Θ := Θ) C) (fun _ _ _ => ⊤) ⊣⊢ instpred C.
  Proof.
    change (instpred (solve (Θ := Θ) C) ⊣⊢ instpred C).
    unfold solve. rewrite instpred_solved_hmap.
    now rewrite asolve_correct subst_pred_refl.
  Qed.

End Correctness.

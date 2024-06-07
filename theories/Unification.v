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
From Em Require Import BaseLogic Monad.Interface Parallel Triangular UnificationGeneric.

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

Section OccursCheck.
  Import option.notations.
  Import (hints) Par.

  Definition occurs_check_in : ⊧ ∀ α, (α ∈) ⇢ ▷(Option (α ∈)) :=
    fun w x xIn y yIn =>
      match world.occurs_check_view yIn xIn with
      | world.Same _      => None
      | world.Diff _ xIn' => Some xIn'
      end.

  Definition occurs_check : ⊧ OTy ⇢ ▷(Option OTy) :=
    fun w =>
      fix oc (t : OTy w) β (βIn : β ∈ w) {struct t} :=
      match t with
      | oty.evar αIn   => oty.evar <$> occurs_check_in αIn βIn
      | oty.bool       => Some oty.bool
      | oty.func t1 t2 => oty.func <$> oc t1 β βIn <*> oc t2 β βIn
      end.

  Lemma occurs_check_spec {w α} (αIn : α ∈ w) (t : OTy w) :
    match occurs_check t αIn with
    | Some t' => t = t'[thin α]
    | None => t = oty.evar αIn \/ oty.OTy_subterm (oty.evar αIn) t
    end.
  Proof.
    induction t; cbn.
    - unfold occurs_check_in. destruct world.occurs_check_view; cbn.
      + now left.
      + now rewrite lk_thin.
    - reflexivity.
    - destruct (occurs_check t1 αIn), (occurs_check t2 αIn);
        cbn; subst; auto; right;
        match goal with
        | H: _ \/ oty.OTy_subterm _ ?t |- _ =>
            destruct H;
            [ subst; constructor; constructor
            | constructor 2 with t; auto; constructor; constructor
            ]
        end.
  Qed.

End OccursCheck.

Section VarView.

  Inductive VarView {w} : OTy w → Type :=
  | is_var {x} (xIn : x ∈ w) : VarView (oty.evar xIn)
  | not_var {t} (H: ∀ x (xIn : x ∈ w), t <> oty.evar xIn) : VarView t.
  #[global] Arguments not_var {w t} &.

  Definition varview {w} (t : OTy w) : VarView t :=
    match t with
    | oty.evar xIn => is_var xIn
    | _            => not_var (fun _ _ e => noConfusion_inv e)
    end.

End VarView.

Section Implementation.

  Definition flex : ⊧ ∀ α, world.In α ⇢ OTy ⇢ Solved Tri Unit :=
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

  Section MguO.

    Context [w] (lamgu : ▷AUnifier w).
    Arguments lamgu {_ _} _ _ {_} _.

    Definition aflex α {αIn : α ∈ w} (τ : OTy w) : C w :=
      fun _ θ =>
        match θ with
        | Tri.nil          => flex α τ
        | Tri.cons β τ' θ' => lamgu (lk (thick β τ') αIn) τ[thick β τ'] θ'
        end.
    #[global] Arguments aflex α {αIn} τ [w1] _.

    Definition atrav : (OTy ⇢ OTy ⇢ C)%W w :=
      fix atrav s t {struct s} :=
        match s , t with
        | @oty.evar _ α _  , t               => aflex α t
        | s                , @oty.evar _ β _ => aflex β s
        | oty.bool         , oty.bool        => ctrue
        | oty.func s1 s2   , oty.func t1 t2  => cand (atrav s1 t1) (atrav s2 t2)
        | _                , _               => cfalse
        end.

    Section atrav_elim.

      Context (P : OTy w → OTy w → C w → Type).
      Context (fflex1 : ∀ α (αIn : α ∈ w) (t : OTy w), P (oty.evar αIn) t (aflex α t)).
      Context (fflex2 : ∀ α (αIn : α ∈ w) (t : OTy w), P t (oty.evar αIn) (aflex α t)).
      Context (fbool : P oty.bool oty.bool ctrue).
      Context (fbool_func : ∀ T1 T2 : OTy w, P oty.bool (oty.func T1 T2) cfalse).
      Context (ffunc_bool : ∀ T1 T2 : OTy w, P (oty.func T1 T2) oty.bool cfalse).
      Context (ffunc : ∀ s1 s2 t1 t2 : OTy w,
        (P s1 t1 (atrav s1 t1)) →
        (P s2 t2 (atrav s2 t2)) →
        P (oty.func s1 s2) (oty.func t1 t2)
          (cand (atrav s1 t1) (atrav s2 t2))).

      Lemma atrav_elim : ∀ (t1 t2 : OTy w), P t1 t2 (atrav t1 t2).
      Proof. induction t1; intros t2; cbn; auto; destruct t2; auto. Qed.

    End atrav_elim.

  End MguO.

  Definition amgu : ⊧ AUnifier :=
    fun w => loeb atrav w.

  Definition mgu `{HMap Tri Θ} : ⊧ OTy ⇢ OTy ⇢ Solved Θ Unit :=
    fun w s t => solved_hmap (@amgu w s t _ refl).

  Definition asolve : ⊧ List (Prod OTy OTy) ⇢ C :=
    fix asolve {w} cs {struct cs} :=
      match cs with
      | List.nil             => ctrue
      | List.cons (t1,t2) cs => cand (amgu t1 t2) (asolve cs)
      end.

  Definition solve `{HMap Tri Θ} : ⊧ List (Prod OTy OTy) ⇢ Solved Θ Unit :=
    fun w cs => solved_hmap (asolve cs refl).

End Implementation.

Section Correctness.

  Definition AUnifierCorrect : ⊧ AUnifier ⇢ PROP :=
    fun w0 bu =>
      ∀ (t1 t2 : OTy w0) w1 (θ1 : w0 ⊑⁻ w1),
        instpred (bu t1 t2 w1 θ1) ⊣⊢ₚ (t1 =ₚ t2)[θ1].

  Lemma flex_correct {w α} (αIn : α ∈ w) (t : OTy w) :
    instpred (flex α t) ⊣⊢ₚ oty.evar αIn =ₚ t.
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

    Context [w] (lamgu : ▷AUnifier w).
    Context (lamgu_correct : ∀ x (xIn : x ∈ w),
                AUnifierCorrect (lamgu xIn)).

    Lemma aflex_correct {α} (αIn : α ∈ w) (t : OTy w) w1 (θ1 : w ⊑⁻ w1) :
      instpred (aflex lamgu α t θ1) ⊣⊢ₚ (oty.evar αIn =ₚ t)[θ1].
    Proof.
      destruct θ1; cbn; Tri.folddefs.
      Tri.folddefs.
      - now rewrite flex_correct, subst_pred_refl.
      - now rewrite lamgu_correct, !subst_eq, !subst_trans.
    Qed.

    Lemma atrav_correct : AUnifierCorrect (atrav lamgu).
    Proof.
      intros t1 t2. pattern (atrav lamgu t1 t2). apply atrav_elim; clear t1 t2.
      - intros α αIn t w1 θ1. now rewrite aflex_correct.
      - intros α αIn t w1 θ1. now rewrite aflex_correct.
      - intros. now rewrite instpred_ctrue.
      - intros. predsimpl.
      - intros. predsimpl.
      - intros s1 s2 t1 t2 IH1 IH2 w1 θ1.
        rewrite peq_ty_noconfusion. now apply instpred_cand_intro.
    Qed.

  End InnerRecursion.

  Lemma amgu_correct : ∀ w, AUnifierCorrect (@amgu w).
  Proof. apply loeb_elim, atrav_correct. Qed.

  Definition mgu_correct `{LkHMap Tri Θ} w (t1 t2 : OTy w) :
    instpred (mgu (Θ := Θ) t1 t2) ⊣⊢ₚ t1 =ₚ t2.
  Proof.
    unfold mgu. rewrite instpred_solved_hmap.
    now rewrite amgu_correct, subst_pred_refl.
  Qed.

  #[local] Existing Instance instpred_prod_ty.

  Lemma asolve_correct {w0} (C : List (OTy * OTy) w0) :
    ∀ w1 (θ1 : w0 ⊑⁻ w1),
      instpred (asolve C θ1) ⊣⊢ₚ (instpred C)[θ1].
  Proof.
    induction C as [|[t1 t2]]; cbn [asolve]; intros.
    - now rewrite instpred_ctrue.
    - apply instpred_cand_intro; auto. intros. apply amgu_correct.
  Qed.

  Lemma solve_correct `{LkHMap Tri Θ} {w} (C : List (OTy * OTy) w) :
    WP (solve (Θ := Θ) C) (fun _ _ _ => ⊤ₚ)%P ⊣⊢ₚ instpred C.
  Proof.
    change (instpred (solve (Θ := Θ) C) ⊣⊢ₚ instpred C).
    unfold solve. rewrite instpred_solved_hmap.
    now rewrite asolve_correct, subst_pred_refl.
  Qed.

End Correctness.

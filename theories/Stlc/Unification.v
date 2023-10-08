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

From Coq Require Import
  Arith.PeanoNat.
From Equations Require Import
  Equations.
From Em Require Import
  Context
  Prelude
  Stlc.Alloc
  Stlc.Instantiation
  Stlc.Predicates
  Stlc.Persistence
  Stlc.Substitution
  Stlc.Triangular
  Stlc.Worlds.

Import Pred ctx.notations Tri.notations World.notations Pred.notations.
Import (hints) Diamond Sub Tri.

Set Implicit Arguments.

Notation OptionDiamond := (DiamondT Tri Option).

#[local] Notation "s [ ζ ]" :=
  (persist s ζ)
    (at level 8, left associativity,
      format "s [ ζ ]").

Ltac folddefs :=
  repeat
    match goal with
    | |- context[@Tri.refl ?w] =>
        change_no_check (@Tri.refl w) with (@refl Tri _ w)
    | |- context[Tri.cons ?x ?t refl] =>
        change_no_check (Tri.cons x t refl) with (thick x t)
    | |- context[Tri.cons ?x ?t ?r] =>
        change_no_check (Tri.cons x t r) with (thick x t ⊙⁻ r)
    end.

Definition löb {A} : (⊢ʷ ▷A -> A) -> (⊢ʷ A) :=
  fun step w => ctx.remove_acc_rect A step (ctx.remove_acc_all w).

Definition löb_elim {A} (step : ⊢ʷ ▷A -> A) (P : forall w, A w -> Prop)
  (IH: forall w (f : ▷A w) (pf : forall x xIn, P (w - x) (f x xIn)), P w (step w f)) :
  forall w, P w (löb step w).
Proof. intros w. unfold löb. induction (ctx.remove_acc_all w). now apply IH. Qed.

Section Operations.

  Definition fail {A} : ⊢ʷ OptionDiamond A :=
    fun w => None.
  #[global] Arguments fail {A w}.

  Definition singleton {w x} (xIn : x ∈ w) (t : Ṫy (w - x)) :
    OptionDiamond Unit w :=
    Some (existT (w - x) (thick (Θ := Tri) x t, tt)).

End Operations.

Section OccursCheck.
  Import option.notations.
  Import (hints) Sub.

  Definition occurs_check_in : ⊢ʷ ∀ x, ctx.In x -> ▷(Option (ctx.In x)) :=
    fun w x xIn y yIn =>
      match ctx.occurs_check_view yIn xIn with
      | ctx.Same _      => None
      | ctx.Diff _ xIn' => Some xIn'
      end.

  Definition occurs_check : ⊢ʷ Ṫy -> ▷(Option Ṫy) :=
    fun w =>
      fix oc (t : Ṫy w) β (βIn : β ∈ w) {struct t} :=
      match t with
      | ṫy.var αIn    => ṫy.var <$> occurs_check_in αIn βIn
      | ṫy.bool       => Some ṫy.bool
      | ṫy.func t1 t2 => ṫy.func <$> oc t1 β βIn <*> oc t2 β βIn
      end.

  Lemma occurs_check_spec {w α} (αIn : α ∈ w) (t : Ṫy w) :
    option.spec
      (fun t' => t = t'[thin α])
      (t = ṫy.var αIn \/ ṫy.Ṫy_subterm (ṫy.var αIn) t)
      (occurs_check t αIn).
  Proof.
    induction t; cbn.
    - unfold occurs_check_in.
      destruct (ctx.occurs_check_view αIn αIn0); constructor.
      + left. reflexivity.
      + cbn. now rewrite lk_thin.
    - constructor. reflexivity.
    - repeat option.tactics.mixin; subst; auto; right;
        match goal with
        | H: _ \/ ṫy.Ṫy_subterm _ ?t |- _ =>
            destruct H;
            [ subst; constructor; constructor
            | constructor 2 with t; auto; constructor; constructor
            ]
        end.
  Qed.

End OccursCheck.

Section VarView.

  Inductive VarView {w} : Ṫy w -> Type :=
  | is_var {x} (xIn : x ∈ w) : VarView (ṫy.var xIn)
  | not_var {t} (H: forall x (xIn : x ∈ w), t <> ṫy.var xIn) : VarView t.
  #[global] Arguments not_var {w t} &.

  Definition varview {w} (t : Ṫy w) : VarView t :=
    match t with
    | ṫy.var xIn => is_var xIn
    | _         => not_var (fun _ _ => noConfusion_inv)
    end.

End VarView.

Section Implementation.

  Definition C := Box Tri (OptionDiamond Unit).

  Definition ctrue : ⊢ʷ C :=
    fun w0 w1 r01 => pure tt.
  Definition cfalse : ⊢ʷ C :=
    fun w0 w1 r01 => fail.
  Definition cand : ⊢ʷ C -> C -> C :=
    fun w0 c1 c2 w1 r01 =>
      bind (c1 w1 r01) (fun w2 r12 _ => _4 c2 r01 r12).
  #[global] Arguments cfalse {w} [w1] _.
  #[global] Arguments ctrue {w} [w1] _.

  Definition BoxUnifier : TYPE :=
    Ṫy -> Ṫy -> C.

  Definition flex : ⊢ʷ ∀ α, ctx.In α -> Ṫy -> OptionDiamond Unit :=
    fun w α αIn τ =>
      match varview τ with
      | is_var βIn =>
          match ctx.occurs_check_view αIn βIn with
          | ctx.Same _      => pure tt
          | ctx.Diff _ βIn' => singleton αIn (ṫy.var βIn')
          end
      | not_var _ =>
          match occurs_check τ αIn with
          | Some τ' => singleton αIn τ'
          | None    => fail
          end
      end.
  #[global] Arguments flex {w} α {αIn} τ : rename.

  Section MguO.

    Context [w] (lamgu : ▷BoxUnifier w).
    Arguments lamgu {_ _} _ _ {_} _.

    Definition aflex α {αIn : α ∈ w} (τ : Ṫy w) : C w :=
      fun _ θ =>
        match θ with
        | Tri.refl         => flex α τ
        | Tri.cons β τ' θ' => lamgu (lk (thick β τ') αIn) τ[thick β τ'] θ'
        end.
    #[global] Arguments aflex α {αIn} τ [w1] _.

    Definition atrav : (Ṫy -> Ṫy -> C)%W w :=
      fix bmgu s t {struct s} :=
        match s , t with
        | @ṫy.var _ α _  , t             => aflex α t
        | s             , @ṫy.var _ β _  => aflex β s
        | ṫy.bool       , ṫy.bool       => ctrue
        | ṫy.func s1 s2 , ṫy.func t1 t2 => cand (bmgu s1 t1) (bmgu s2 t2)
        | _             , _             => cfalse
        end.

    Section atrav_elim.

      Context (P : Ṫy w -> Ṫy w -> C w -> Type).
      Context (fflex1 : forall (x : nat) (xIn : x ∈ w) (t : Ṫy w), P (ṫy.var xIn) t (aflex x t)).
      Context (fflex2 : forall (x : nat) (xIn : x ∈ w) (t : Ṫy w), P t (ṫy.var xIn) (aflex x t)).
      Context (fbool : P ṫy.bool ṫy.bool ctrue).
      Context (fbool_func : forall T1 T2 : Ṫy w, P ṫy.bool (ṫy.func T1 T2) cfalse).
      Context (ffunc_bool : forall T1 T2 : Ṫy w, P (ṫy.func T1 T2) ṫy.bool cfalse).
      Context (ffunc : forall s1 s2 t1 t2 : Ṫy w,
        (P s1 t1 (atrav s1 t1)) ->
        (P s2 t2 (atrav s2 t2)) ->
        P (ṫy.func s1 s2) (ṫy.func t1 t2)
          (cand (atrav s1 t1) (atrav s2 t2))).

      Lemma atrav_elim : forall (t1 t2 : Ṫy w), P t1 t2 (atrav t1 t2).
      Proof. induction t1; intros t2; cbn; auto; destruct t2; auto. Qed.

    End atrav_elim.

  End MguO.

  Definition amgu : ⊢ʷ BoxUnifier :=
    löb atrav.

  Definition mgu : ⊢ʷ Ṫy -> Ṫy -> OptionDiamond Unit :=
    fun w s t => T (@amgu w s t).

  Definition asolver : ⊢ʷ List (Prod Ṫy Ṫy) -> C :=
    fix asolver {w} cs {struct cs} :=
      match cs with
      | List.nil             => ctrue
      | List.cons (t1,t2) cs => cand (amgu t1 t2) (asolver cs)
      end.

  Definition solver : ⊢ʷ List (Prod Ṫy Ṫy) -> OptionDiamond Unit :=
    fun w cs => asolver cs refl.

  Import option.notations.

  Definition solveoptiondiamond {A} {pA : Persistent A} :
    Diamond alloc.acc_alloc (List (Ṫy * Ṫy) * A) ctx.nil ->
    Option (Diamond alloc.acc_alloc A) ctx.nil :=
    fun '(existT w1 (θ1, (cs, a))) =>
      '(existT w2 (θ2, tt))      <- solver cs;;
      Some (existT w2 (alloc.nil_l,persist a θ2)).

  Definition optiondiamond2schematic {A} :
    Option (Diamond alloc.acc_alloc A) ctx.nil ->
    option (Schematic A) :=
      option.map
        (fun '(existT w (θ,a)) => existT w a).

End Implementation.

Section Correctness.

  Lemma instpred_ctrue {w0 w1} (θ1 : Tri w0 w1) :
    instpred (ctrue θ1) ⊣⊢ₚ Trueₚ.
  Proof. cbn. now rewrite Acc.wp_refl. Qed.

  Lemma instpred_cfalse {w0 w1} (θ1 : Tri w0 w1) :
    instpred (cfalse θ1) ⊣⊢ₚ Falseₚ.
  Proof. reflexivity. Qed.

  Lemma instpred_cand_intro {w0} (c1 c2 : C w0) P Q :
    (forall w1 (θ1 : Tri w0 w1), instpred (c1 w1 θ1) ⊣⊢ₚ P[θ1]) ->
    (forall w1 (θ1 : Tri w0 w1), instpred (c2 w1 θ1) ⊣⊢ₚ Q[θ1]) ->
    (forall w1 (θ1 : Tri w0 w1), instpred (cand c1 c2 θ1) ⊣⊢ₚ (P /\ₚ Q)[θ1]).
  Proof.
    unfold instpred, instpred_optiondiamond, cand. intros H1 H2 w1 θ1.
    rewrite wp_optiondiamond_bind, persist_and, <- H1, wp_optiondiamond_and.
    unfold _4. apply proper_wp_optiondiamond_bientails. intros w2 θ2 [].
    cbn. rewrite and_true_l, <- persist_pred_trans. apply H2.
  Qed.

  Definition BoxUnifierCorrect : ⊢ʷ BoxUnifier -> PROP :=
    fun w0 bu =>
      forall (t1 t2 : Ṫy w0) w1 (θ1 : w0 ⊒⁻ w1),
        instpred (bu t1 t2 w1 θ1) ⊣⊢ₚ (t1 =ₚ t2)[θ1].

  Lemma flex_correct {w α} (αIn : α ∈ w) (t : Ṫy w) :
    instpred (flex α t) ⊣⊢ₚ ṫy.var αIn =ₚ t.
  Proof.
    unfold flex. destruct varview; cbn.
    - destruct ctx.occurs_check_view; cbn.
      + now rewrite Acc.wp_refl, eqₚ_refl.
      + rewrite Acc.wp_thick, persist_true, and_true_r.
        cbn. now rewrite lk_thin.
    - destruct (occurs_check_spec αIn t) as [|[HOC|HOC]]; cbn.
      + subst. now rewrite Acc.wp_thick, persist_true, and_true_r.
      + subst. now contradiction (H α αIn).
      + apply pno_cycle in HOC. apply split_bientails. now split.
  Qed.

  Section InnerRecursion.

    Context [w] (lamgu : ▷BoxUnifier w).
    Context (lamgu_correct : forall x (xIn : x ∈ w),
                BoxUnifierCorrect (lamgu xIn)).

    Lemma aflex_correct {α} (αIn : α ∈ w) (t : Ṫy w) w1 (θ1 : w ⊒⁻ w1) :
      instpred (aflex lamgu α t θ1) ⊣⊢ₚ (ṫy.var αIn =ₚ t)[θ1].
    Proof.
      destruct θ1; cbn; folddefs.
      - now rewrite flex_correct, persist_pred_refl.
      - now rewrite lamgu_correct, !persist_eq, !persist_trans.
    Qed.

    Lemma atrav_correct : BoxUnifierCorrect (atrav lamgu).
    Proof.
      intros t1 t2. pattern (atrav lamgu t1 t2). apply atrav_elim; clear t1 t2.
      - intros α αIn t w1 θ1. now rewrite aflex_correct.
      - intros α αIn t w1 θ1. now rewrite aflex_correct.
      - intros. now rewrite instpred_ctrue, eqₚ_refl.
      - intros. now rewrite instpred_cfalse, peq_ty_noconfusion.
      - intros. now rewrite instpred_cfalse, peq_ty_noconfusion.
      - intros s1 s2 t1 t2 IH1 IH2 w1 θ1.
        rewrite peq_ty_noconfusion. now apply instpred_cand_intro.
    Qed.

  End InnerRecursion.

  Lemma amgu_correct : forall w, BoxUnifierCorrect (@amgu w).
  Proof. apply löb_elim, atrav_correct. Qed.

  Definition mgu_correct w (t1 t2 : Ṫy w) :
    instpred (mgu t1 t2) ⊣⊢ₚ t1 =ₚ t2.
  Proof. unfold mgu, T. now rewrite amgu_correct, persist_pred_refl. Qed.

  #[local] Existing Instance instpred_prod_ty.

  Lemma asolver_correct {w0} (C : List (Ṫy * Ṫy) w0) :
    forall w1 (θ1 : w0 ⊒⁻ w1),
      instpred (asolver C θ1) ⊣⊢ₚ (instpred C)[θ1].
  Proof.
    induction C as [|[t1 t2]]; cbn - [ctrue cand]; intros.
    - now rewrite instpred_ctrue.
    - apply instpred_cand_intro; auto. intros. apply amgu_correct.
  Qed.

  Lemma solver_correct {w} (C : List (Ṫy * Ṫy) w) :
    instpred (solver C) ⊣⊢ₚ instpred C.
  Proof. unfold solver, T. now rewrite asolver_correct, persist_pred_refl. Qed.

End Correctness.

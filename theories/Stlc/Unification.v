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
    | |- context[Tri.cons ?x ?t ?r] =>
        change_no_check (Tri.cons x t r) with (thick x t ⊙⁻ r)
    end.

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
    fun w0 w1 r01 => None.
  Definition cand : ⊢ʷ C -> C -> C :=
    fun w0 c1 c2 w1 r01 =>
      bind (c1 w1 r01) (fun w2 r12 _ => _4 c2 r01 r12).
  #[global] Arguments cfalse {w} [w1] _.
  #[global] Arguments ctrue {w} [w1] _.

  Definition BoxUnifier : TYPE :=
    Ṫy -> Ṫy -> C.

  Definition flex : ⊢ʷ Ṫy -> ∀ α, ctx.In α -> OptionDiamond Unit :=
    fun w t α αIn =>
      match varview t with
      | is_var βIn =>
          match ctx.occurs_check_view αIn βIn with
          | ctx.Same _      => pure tt
          | ctx.Diff _ βIn' => singleton αIn (ṫy.var βIn')
          end
      | not_var _ =>
          match occurs_check t αIn with
          | Some t' => singleton αIn t'
          | None    => fail
          end
      end.

  Section MguO.

    Context [w] (lmgu : ▷BoxUnifier w).

    Definition boxflex (t : Ṫy w) {x} (xIn : x ∈ w) : C w :=
      Tri.box_intro_split
        (flex t xIn)
        (fun z zIn u =>
           let ζ := thick (Θ := Tri) z u in
           lmgu _ (lk ζ xIn) (persist t ζ)).

    Definition boxmgu : BoxUnifier w :=
      fix bmgu s t {struct s} :=
        match s , t with
        | ṫy.var xIn    , t             => boxflex t xIn
        | s             , ṫy.var yIn    => boxflex s yIn
        | ṫy.bool       , ṫy.bool       => ctrue
        | ṫy.func s1 s2 , ṫy.func t1 t2 => cand (bmgu s1 t1) (bmgu s2 t2)
        | _             , _             => cfalse
        end.

    Section boxmgu_elim.

      Context (P : Ṫy w -> Ṫy w -> C w -> Type).
      Context (fflex1 : forall (x : nat) (xIn : x ∈ w) (t : Ṫy w), P (ṫy.var xIn) t (boxflex t xIn)).
      Context (fflex2 : forall (x : nat) (xIn : x ∈ w) (t : Ṫy w), P t (ṫy.var xIn) (boxflex t xIn)).
      Context (fbool : P ṫy.bool ṫy.bool ctrue).
      Context (fbool_func : forall T1 T2 : Ṫy w, P ṫy.bool (ṫy.func T1 T2) cfalse).
      Context (ffunc_bool : forall T1 T2 : Ṫy w, P (ṫy.func T1 T2) ṫy.bool cfalse).
      Context (ffunc : forall s1 s2 t1 t2 : Ṫy w,
        (P s1 t1 (boxmgu s1 t1)) ->
        (P s2 t2 (boxmgu s2 t2)) ->
        P (ṫy.func s1 s2) (ṫy.func t1 t2)
          (cand (boxmgu s1 t1) (boxmgu s2 t2))).

      Lemma boxmgu_elim : forall (t1 t2 : Ṫy w), P t1 t2 (boxmgu t1 t2).
      Proof. induction t1; intros t2; cbn; auto; destruct t2; auto. Qed.

    End boxmgu_elim.

  End MguO.

  Definition bmgu_aux : ⊢ʷ ctx.remove_acc -> BoxUnifier :=
    fix bmgu {w} d {struct d} : BoxUnifier w :=
      boxmgu (fun α αIn => bmgu (ctx.remove_acc_inv d αIn)).

  Definition bmgu : ⊢ʷ BoxUnifier :=
    fun w => bmgu_aux (ctx.remove_acc_all w).

  Definition mgu : ⊢ʷ Ṫy -> Ṫy -> OptionDiamond Unit :=
    fun w s t => T (@bmgu w s t).

  Definition boxsolvelist : ⊢ʷ List (Prod Ṫy Ṫy) -> C :=
    fix solve {w} cs {struct cs} :=
      match cs with
      | List.nil             => ctrue
      | List.cons (t1,t2) cs => cand (bmgu t1 t2) (solve cs)
      end.

  Definition solvelist : ⊢ʷ List (Prod Ṫy Ṫy) -> OptionDiamond Unit :=
    fun w cs => boxsolvelist cs refl.

  Import option.notations.

  Definition solveoptiondiamond {A} {pA : Persistent A} :
    Diamond alloc.acc_alloc (List (Ṫy * Ṫy) * A) ctx.nil ->
    Option (Diamond alloc.acc_alloc A) ctx.nil :=
    fun '(existT w1 (θ1, (cs, a))) =>
      '(existT w2 (θ2, tt))      <- solvelist cs;;
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
    instpred (flex t αIn) ⊣⊢ₚ ṫy.var αIn =ₚ t.
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

    Context [w] (lmgu : ▷BoxUnifier w).
    Context (lmgu_correct : forall x (xIn : x ∈ w),
                BoxUnifierCorrect (lmgu xIn)).

    Lemma boxflex_correct {α} (αIn : α ∈ w) (t : Ṫy w) w1 (θ1 : w ⊒⁻ w1) :
      instpred (boxflex lmgu t αIn θ1) ⊣⊢ₚ (ṫy.var αIn =ₚ t)[θ1].
    Proof.
      destruct θ1; cbn; folddefs.
      - now rewrite flex_correct, persist_pred_refl.
      - now rewrite lmgu_correct, !persist_eq, !persist_trans.
    Qed.

    Lemma boxmgu_correct : BoxUnifierCorrect (boxmgu lmgu).
    Proof.
      intros t1 t2. pattern (boxmgu lmgu t1 t2). apply boxmgu_elim; clear t1 t2.
      - intros α αIn t w1 θ1. now rewrite boxflex_correct.
      - intros α αIn t w1 θ1. now rewrite boxflex_correct.
      - intros. now rewrite instpred_ctrue, eqₚ_refl.
      - intros. now rewrite instpred_cfalse, peq_ty_noconfusion.
      - intros. now rewrite instpred_cfalse, peq_ty_noconfusion.
      - intros s1 s2 t1 t2 IH1 IH2 w1 θ1.
        rewrite peq_ty_noconfusion. now apply instpred_cand_intro.
    Qed.

  End InnerRecursion.

  Section OuterRecursion.

    Lemma bmgu_aux_correct w d : BoxUnifierCorrect (@bmgu_aux w d).
    Proof. induction d. cbn. now apply boxmgu_correct. Qed.

    Lemma bmgu_correct w : BoxUnifierCorrect (@bmgu w).
    Proof. apply bmgu_aux_correct. Qed.

  End OuterRecursion.

  Definition mgu_correct w (t1 t2 : Ṫy w) :
    instpred (mgu t1 t2) ⊣⊢ₚ t1 =ₚ t2.
  Proof. unfold mgu, T. now rewrite bmgu_correct, persist_pred_refl. Qed.

  #[local] Existing Instance instpred_prod_ty.

  Lemma boxsolvelist_correct {w0} (C : List (Ṫy * Ṫy) w0) :
    forall w1 (θ1 : w0 ⊒⁻ w1),
      instpred (boxsolvelist C θ1) ⊣⊢ₚ (instpred C)[θ1].
  Proof.
    induction C as [|[t1 t2]]; cbn - [ctrue cand]; intros.
    - now rewrite instpred_ctrue.
    - apply instpred_cand_intro; auto. intros. apply bmgu_correct.
  Qed.

  Lemma solvelist_correct {w} (C : List (Ṫy * Ṫy) w) :
    instpred (solvelist C) ⊣⊢ₚ instpred C.
  Proof.
    unfold solvelist, T.
    now rewrite boxsolvelist_correct, persist_pred_refl.
  Qed.

End Correctness.

Module Löb.

  Section Recursor.

    Context (A : TYPE) (step : ⊢ʷ ▷A -> A).

    #[local] Obligation Tactic := auto using Nat.eq_le_incl, ctx.length_remove.
    Equations Löb {w : World} : A w by wf (ctx.length w) :=
    Löb := step (fun _ _ => Löb).
    #[global] Arguments Löb : clear implicits.

  End Recursor.

  Definition bmgu : ⊢ʷ BoxUnifier :=
    fun w s t => Löb boxmgu _ s t.

  Lemma bmgu_correct w : BoxUnifierCorrect (@bmgu w).
  Proof.
    pattern (@bmgu w). revert w. apply Löb_elim.
    intros w IH. now apply boxmgu_correct.
  Qed.

End Löb.

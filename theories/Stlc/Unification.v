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
  Arith.PeanoNat
  Classes.Morphisms
  Classes.Morphisms_Prop
  Relations.Relation_Definitions.
From Equations Require Import
  Equations.
From Em Require Import
  Context
  Prelude
  Stlc.Alloc
  Stlc.Instantiation
  Stlc.Predicates
  Stlc.Persistence
  Stlc.Spec
  Stlc.Substitution
  Stlc.Triangular
  Stlc.Worlds.

Import ctx.notations.
Import World.notations.

Set Implicit Arguments.

Reserved Notation "w1 ⊒ w2" (at level 80).

Notation OptionDiamond := (DiamondT Tri Option).

#[local] Notation "◇ A" := (DiamondT Tri id A) (at level 9, format "◇ A", right associativity).
#[local] Notation "? A" := (Option A) (at level 9, format "? A", right associativity).
Notation "◆ A" := (OptionDiamond A) (at level 9, format "◆ A", right associativity).


Ltac folddefs :=
  repeat
    match goal with
    | H: context[@Tri.refl ?w] |- _ =>
        change_no_check (@Tri.refl w) with (@refl Tri _ w) in H
    | |- context[@Tri.refl ?w] =>
        change_no_check (@Tri.refl w) with (@refl Tri _ w)
    | |- context[Tri.cons ?x ?t ?r] =>
        change_no_check (Tri.cons x t r) with (thick x t ⊙⁻ r)
    end.

Module BoveCapretta.

  Set Case Analysis Schemes.
  Inductive dom (w : World) : Type :=
  | domstep : (forall x (xIn : x ∈ w), dom (w - x)) -> dom w.

  #[local] Obligation Tactic := auto using Nat.eq_le_incl, ctx.length_remove.
  Equations indom {w : World} : dom w by wf (ctx.length w) :=
  indom := domstep (fun _ _ => indom).
  #[global] Arguments indom w : clear implicits.

  Definition dom_inv w (d : dom w) :
    (forall x (xIn : x ∈ w), dom (w - x)) :=
    match d with domstep x => x end.

End BoveCapretta.

Section Löb.

  Import Tri.notations.

  Context (A : TYPE) (step : ⊢ʷ ▷A -> A).

  #[local] Obligation Tactic := auto using Nat.eq_le_incl, ctx.length_remove.
  Equations Löbaux {w : World} : A w by wf (ctx.length w) :=
  Löbaux := step (fun _ _ => Löbaux).
  Local Arguments Löbaux : clear implicits.

  Transparent Löbaux.
  Definition Löb : ⊢ʷ A := Löbaux.

  Context (P : forall w : World, A w -> Type).
  Context (pstep : forall w,
        (forall x (xIn : x ∈ w), P (Löb (w - x))) ->
        P (step (fun x xIn => Löb (w - x)))).

  Definition Löb_elim : forall w, P (Löb w) :=
    Löbaux_elim P pstep.

End Löb.

Section Operations.
  Import Tri.notations.
  Import (hints) Tri.
  Import Pred Pred.notations.

  Definition box2later {A} : ⊢ʷ □⁻A -> ▶A.
    intros w a x xIn t. apply a. econstructor.
    apply t. constructor.
  Defined.

  Definition sooner2diamond {A} : ⊢ʷ ◀A -> ◇A :=
    fun w a =>
      match a with
        existT x (existT xIn (t , a)) =>
        existT (w - x) (pair (thick (Θ := Tri) x t) a)
      end.

  Definition sooner2diamondtm {A} : ⊢ʷ ◀A -> ◆A.
    intros w a. destruct a as [σ [σIn [t a]]].
    constructor.
    econstructor. split; try eassumption.
    econstructor 2. auto. constructor 1.
  Defined.

  (* Import LR. *)
  Import (hints) Diamond.

  Definition fail {A} : ⊢ʷ ◆A :=
    fun w => None.

  Definition acc {A} {w0 w1} (ζ1 : w0 ⊒⁻ w1) : ◆A w1 -> ◆A w0 :=
    @option.map (Diamond Tri A w1) (Diamond Tri A w0)
      (fun '(existT w2 (ζ2 , a)) => existT w2 (ζ1 ⊙⁻ ζ2, a)).

  Definition η1 {A} {w x} {xIn : x ∈ w} (t : Ṫy (w - x)) (a : A (w - x)) : ◆A w :=
    sooner2diamondtm (existT x (existT xIn (t, a))).

  Definition tell1 {w x} (xIn : x ∈ w) (t : Ṫy (w - x)) : ◆Unit w :=
    Some (existT (w - x) (thick (Θ := Tri) x t, tt)).

End Operations.

Section OccursCheck.
  Import option.notations.
  Import Tri.notations.
  Import World.notations.
  Import Sub.

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
      (fun t' => t = persist t' (thin α))
      (t = ṫy.var αIn \/ ṫy.Ṫy_subterm (ṫy.var αIn) t)
      (occurs_check t αIn).
  Proof.
    induction t; cbn.
    - unfold occurs_check_in.
      destruct (ctx.occurs_check_view αIn αIn0); constructor.
      + left. reflexivity.
      + cbn - [lk]. now rewrite lk_thin.
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

Definition Hom (A B : TYPE) := ⊢ʷ A -> B.

Definition fmap {A B} (f : Hom A B) : Hom ◆A ◆B.
Proof.
  intros w0 [[w1 [ζ1 a1]]|].
  - constructor 1. exists w1. split. auto. apply f. auto.
  - constructor 2.
Defined.
(* Notation "f <$> a" := (fmap f a) (at level 20). *)

Local Notation "s [ ζ ]" :=
  (persist _ s _ ζ)
    (at level 8, left associativity,
      format "s [ ζ ]").
(* Local Coercion Sub.triangular : Tri.Tri >-> Sub.Sub. *)

Section Mult.
  Import option.notations.
  Import (hints) Diamond Tri.
  Import Tri.notations.

  Definition μ {A} : Hom ◆◆A ◆A :=
    fun w0 a0 => '(existT w1 (ζ1 , a1)) <- a0;; acc ζ1 a1.

  Definition ebind {A B} : Hom A ◆B -> Hom ◆A ◆B :=
    fun f w0 a0 => '(existT w1 (ζ1, a1)) <- a0 ;; acc ζ1 (f w1 a1).

  (* see Kobayashi, S. (1997). Monad as modality. *)
  Definition strength {A B} : Hom (□⁻A * ◆B) (◆(□⁻A * B)) :=
    fun w0 '(a0,b0) => bind b0 (fun w1 ζ1 b1 => pure (_4 a0 ζ1, b1)).

End Mult.

#[local] Notation "⟨ ζ ⟩ x <- ma ;; mb" :=
  (bind ma (fun _ ζ x => mb))
    (at level 80, x at next level,
      ma at next level, mb at level 200,
      right associativity).

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

  Import Tri.notations.
  Import (hints) Diamond Tri.
  Import Pred Pred.notations.

  Definition C := Box Tri (OptionDiamond Unit).
  (* Definition RC := LR.RBox (RM LR.RUnit). *)

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

  Definition flex : ⊢ʷ Ṫy -> ∀ x, ctx.In x -> ◆Unit :=
    fun w t x xIn =>
      match varview t with
      | is_var yIn =>
          match ctx.occurs_check_view xIn yIn with
          | ctx.Same _      => pure tt
          | ctx.Diff _ yIn' => tell1 xIn (ṫy.var yIn')
          end
      | not_var _ =>
          match occurs_check t xIn with
          | Some t' => tell1 xIn t'
          | None    => None
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

  Definition bmgu : ⊢ʷ BoxUnifier :=
    fun w s t => Löb boxmgu _ s t.

  Definition mgu : ⊢ʷ Ṫy -> Ṫy -> ◆Unit :=
    fun w s t => T (@bmgu w s t).

  Definition boxsolvelist : ⊢ʷ List (Prod Ṫy Ṫy) -> C :=
    fix solve {w} cs {struct cs} :=
      match cs with
      | List.nil             => ctrue
      | List.cons (t1,t2) cs => cand (bmgu t1 t2) (solve cs)
      end.

  Definition solvelist : ⊢ʷ List (Prod Ṫy Ṫy) -> ◆Unit :=
    fun w cs => boxsolvelist cs Tri.refl.

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

  Definition solve_schematic {A} {pA : Persistent A} :
    Diamond alloc.acc_alloc (List (Ṫy * Ṫy) * A) ctx.nil ->
    option (Schematic A) :=
    fun od => optiondiamond2schematic (solveoptiondiamond od).

End Implementation.

Section Correctness.

  Import World.notations.
  Import Pred Pred.notations.
  Import (hints) Pred.Acc Tri.

  #[local] Notation "s [ ζ ]" :=
    (persist s ζ)
      (at level 8, left associativity,
        format "s [ ζ ]").

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
    rewrite wp_optiondiamond_bind. unfold _4. rewrite persist_and, <- H1.
    rewrite wp_optiondiamond_and.
    apply proper_wp_optiondiamond_bientails.
    intros w2 θ2 []. cbn. rewrite and_true_l.
    change (instpred (c2 w2 (θ1 ⊙⁻ θ2)) ⊣⊢ₚ Q[θ1][θ2]).
    rewrite <- persist_pred_trans. apply H2.
  Qed.

  Definition BoxUnifierCorrect : ⊢ʷ BoxUnifier -> PROP :=
    fun w0 bu =>
      forall (t1 t2 : Ṫy w0) w1 (θ1 : w0 ⊒⁻ w1),
        instpred (bu t1 t2 w1 θ1) ⊣⊢ₚ (t1 =ₚ t2)[θ1].

  Section Correctness.

    Import Tri.notations.
    Import (hints) Pred.Acc.

    Context [w] (lmgu : ▷BoxUnifier w).
    Context (lmgu_correct : forall x (xIn : x ∈ w),
                BoxUnifierCorrect (lmgu xIn)).

    Lemma flex_correct {α} (αIn : α ∈ w) (t : Ṫy w) :
      instpred (flex t αIn) ⊣⊢ₚ ṫy.var αIn =ₚ t.
    Proof.
      unfold flex. destruct varview; cbn.
      - destruct ctx.occurs_check_view; cbn.
        + now rewrite Acc.wp_refl, eqₚ_refl.
        + rewrite Acc.wp_thick. rewrite persist_true.
          rewrite and_true_r. cbn - [lk].
          now rewrite lk_thin.
      - destruct (occurs_check_spec αIn t) as [|[HOC|HOC]]; cbn.
        + subst. unfold tell1. cbn.
          rewrite Acc.wp_thick. rewrite persist_true.
          now rewrite and_true_r.
        + subst. now contradiction (H α αIn).
        + apply pno_cycle in HOC.
          apply split_bientails. now split.
    Qed.

    Lemma boxflex_correct {α} (αIn : α ∈ w) (t : Ṫy w) w1 (θ1 : w ⊒⁻ w1) :
      instpred (boxflex lmgu t αIn θ1) ⊣⊢ₚ (ṫy.var αIn =ₚ t)[θ1].
    Proof.
      destruct θ1; cbn - [persist].
      - change Tri.refl with (refl (Θ := Tri) (w:=w)).
        rewrite persist_pred_refl. apply flex_correct.
      - rewrite lmgu_correct.
        change (Tri.cons ?x ?t ?r) with (thick x t ⊙⁻ r).
        now rewrite !persist_eq, !persist_trans.
    Qed.

    Lemma boxmgu_correct : BoxUnifierCorrect (boxmgu lmgu).
    Proof.
      intros t1 t2.
      pattern (boxmgu lmgu t1 t2). apply boxmgu_elim; clear t1 t2.
      - intros α αIn t w1 θ1. now rewrite boxflex_correct.
      - intros α αIn t w1 θ1. now rewrite boxflex_correct.
      - intros. now rewrite instpred_ctrue, eqₚ_refl.
      - intros. now rewrite instpred_cfalse, peq_ty_noconfusion.
      - intros. now rewrite instpred_cfalse, peq_ty_noconfusion.
      - intros s1 s2 t1 t2 IH1 IH2 w1 θ1.
        rewrite peq_ty_noconfusion. now apply instpred_cand_intro.
    Qed.

  End Correctness.

  Lemma bmgu_correct w : BoxUnifierCorrect (@bmgu w).
  Proof.
    pattern (@bmgu w). revert w. apply Löb_elim.
    intros w IH. now apply boxmgu_correct.
  Qed.

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
    - apply instpred_cand_intro; auto.
      intros. apply bmgu_correct.
  Qed.

  Lemma solvelist_correct {w} (C : List (Ṫy * Ṫy) w) :
    instpred (solvelist C) ⊣⊢ₚ instpred C.
  Proof.
    unfold solvelist, T.
    change Tri.refl with (refl (w:=w)).
    rewrite boxsolvelist_correct.
    now rewrite persist_pred_refl.
  Qed.

  Print Assumptions solvelist_correct.

End Correctness.

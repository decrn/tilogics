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

(* Section MoveMe. *)

(*   Import (hints) Tri. *)

(*   Lemma persist_thin_thick {w x} (xIn : x ∈ w) (s t : Ṫy (w - x)) : *)
(*     persist (thin xIn t) (thick (Θ := Tri) x s) = t. *)
(*   Proof. *)
(*     induction t; cbn - [thick]; try rewrite Tri.persist_fix; f_equal; auto. *)
(*     cbn. unfold thickIn. now rewrite ctx.occurs_check_view_thin. *)
(*   Qed. *)

(* End MoveMe. *)

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

  (* Definition RM {A} (R : LR.RELATION Tri A) := LR.ROption (LR.RDiamond R). *)

  #[export] Instance pure_optiondiamond : Pure OptionDiamond :=
    fun A w a => Some (pure a).

  Definition fail {A} : ⊢ʷ ◆A :=
    fun w => None.

  Definition acc {A} {w0 w1} (ζ1 : w0 ⊒⁻ w1) : ◆A w1 -> ◆A w0 :=
    @option.map (Diamond Tri A w1) (Diamond Tri A w0)
      (fun '(existT w2 (ζ2 , a)) => existT w2 (ζ1 ⊙⁻ ζ2, a)).

  (* Lemma proper_pure {A} {RA : RELATION Tri A} : *)
  (*   RValid (RImpl RA (RM RA)) pure. *)
  (* Proof. *)
  (*   intros w0 w1 r01. cbv [RValid pure]. *)
  (*   apply forall_r. intros a0. *)
  (*   apply forall_r. intros a1. *)
  (*   apply impl_and_adjoint. rewrite and_true_l. *)
  (*   apply exists_r. exists r01. *)
  (*   rewrite Acc.wp_refl, ?trans_refl_l, trans_refl_r. *)
  (*   now rewrite eqₚ_refl, and_true_l. *)
  (* Qed. *)

  (* Lemma proper_fail {A} {RA : RELATION Tri A} : *)
  (*   RValid (RM RA) fail. *)
  (* Proof. easy. Qed. *)
  (* #[global] Arguments fail {A w}. *)

  Definition η1 {A} {w x} {xIn : x ∈ w} (t : Ṫy (w - x)) (a : A (w - x)) : ◆A w :=
    sooner2diamondtm (existT x (existT xIn (t, a))).

  Definition tell1 {w x} (xIn : x ∈ w) (t : Ṫy (w - x)) : ◆Unit w :=
    Some (existT (w - x) (thick (Θ := Tri) x t, tt)).

  #[export] Instance bind_optiondiamond : Bind Tri OptionDiamond :=
    fun A B w a0 f =>
      option.bind a0 (fun '(existT w1 (ζ1, a1)) => acc ζ1 (f w1 ζ1 a1)).

  (* Lemma proper_bind {A B} {RA : RELATION Tri A} {RB : RELATION Tri B} : *)
  (*   RValid (RImpl (RM RA) (RImpl (RBox (RImpl RA (RM RB))) (RM RB))) bind. *)
  (* Proof. *)
  (* Admitted. *)
  (* (* Proof. *) *)
  (* (*   intros w0 w1 r01. cbv [RValid bind]. *) *)
  (* (*   apply forall_r. intros m0. *) *)
  (* (*   apply forall_r. intros m1. *) *)
  (* (*   apply impl_and_adjoint. rewrite and_true_l. *) *)
  (* (*   apply forall_r. intros f0. *) *)
  (* (*   apply forall_r. intros f1. *) *)
  (* (*   apply impl_and_adjoint. unfold RM at 3. *) *)
  (* (*   unfold ROption. *) *)

  (* (*   Search option.bind. *) *)
  (* (*   rewrite Acc.wp_refl, ?trans_refl_l, trans_refl_r. *) *)
  (* (*   now rewrite eqₚ_refl, and_true_l. *) *)
  (* (* Qed. *) *)

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
  Import (hints) Tri.
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

Section Variant1.

  Import Tri.notations.
  Import (hints) Tri.
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

  (* Lemma proper_ctrue : LR.RValid RC ctrue. *)
  (* Proof. *)
  (*   unfold LR.RValid, RC, LR.RBox, ctrue. intros w0 w1 r01. *)
  (*   apply forall_r. intros w2. *)
  (*   apply forall_r. intros w3. *)
  (*   apply forall_r. intros r02. *)
  (*   apply forall_r. intros r13. *)
  (*   apply forall_r. intros r23. *)
  (*   apply Acc.entails_wlp. rewrite ext_true. *)
  (*   apply impl_and_adjoint. rewrite and_true_l. cbn. *)
  (*   eapply exists_r. exists r23. *)
  (*   rewrite Acc.wp_refl, trans_refl_r, ?trans_refl_l. *)
  (*   rewrite eqₚ_refl, and_true_l. apply true_r. *)
  (* Qed. *)

  (* Lemma proper_cfalse : LR.RValid RC cfalse. *)
  (* Proof. *)
  (*   unfold LR.RValid, LR.RBox, cfalse. intros w0 w1 r01. *)
  (*   apply forall_r. intros w2. *)
  (*   apply forall_r. intros w3. *)
  (*   apply forall_r. intros r02. *)
  (*   apply forall_r. intros r13. *)
  (*   apply forall_r. intros r23. *)
  (*   apply Acc.entails_wlp, impl_and_adjoint, true_r. *)
  (* Qed. *)

  (* Lemma ext_rbox {A} {RA : LR.RELATION Tri A} {w0 w1 w2} *)
  (*   {r01 : w0 ⊒⁻ w1} {r12 : w1 ⊒⁻ w2} (a0 : □⁻A w0) (a1 : □⁻A w1) : *)
  (*   Ext (LR.RBox RA r01 a0 a1) r12 ⊣⊢ₚ LR.RBox RA (r01 ⊙⁻ r12) a0 (_4 a1 r12). *)
  (* Proof. *)
  (*   unfold LR.RBox. *)
  (*   rewrite ext_forall. apply proper_bientails_forall. intros w3. *)
  (*   rewrite ext_forall. apply proper_bientails_forall. intros w4. *)
  (*   rewrite ext_forall. apply proper_bientails_forall. intros r03. *)
  (*   rewrite ext_forall. *)
  (*   setoid_rewrite ext_forall. *)
  (*   apply split_bientails; split. *)
  (*   - apply forall_r. intros r24. *)
  (*     apply forall_r. intros r34. *)
  (*     constructor. intros ι2 HQ ι4 <- Heq; pred_unfold. cbn in *. *)
  (*     apply HQ; now rewrite ?inst_trans in *. *)
  (*   - apply forall_r. intros r14. *)
  (*     apply forall_r. intros r34. *)
  (*     constructor. cbn. *)
  (*     intros ι2 HQ ι4 Heq1 Heq2. *)
  (* Abort. *)

  (* Lemma proper_bind' {A B} {RA : LR.RELATION _ A} {RB : LR.RELATION _ B} *)
  (*   {w0 w1} (r01 : w0 ⊒⁻ w1) (P : Pred w1) *)
  (*   (m1 : ◆A w1) *)
  (*   (m0 : ◆A w0) *)
  (*   (Q0 : □⁻(A -> ◆B) w0) *)
  (*   (Q1 : □⁻(A -> ◆B) w1) : *)
  (*   entails P (RM RA r01 m0 m1) -> *)
  (*   entails P (LR.RBox (LR.RImpl RA (RM RB)) r01 Q0 Q1) -> *)
  (*   entails P (RM RB r01 (bind m0 Q0) (bind m1 Q1)). *)
  (* Proof. *)
  (*   intros rm rq. *)
  (*   pose proof (@proper_bind A B RA RB w0 w1 r01). *)
  (*   unfold LR.RImpl at 1 in H. *)
  (*   rewrite forall_r in H. specialize (H m0). *)
  (*   rewrite forall_r in H. specialize (H m1). *)
  (*   apply impl_and_adjoint in H. rewrite and_true_l in H. *)
  (*   unfold LR.RImpl at 1 in H. *)
  (*   rewrite forall_r in H. specialize (H Q0). *)
  (*   rewrite forall_r in H. specialize (H Q1). *)
  (*   apply impl_and_adjoint in H. *)
  (*   rewrite <- H. *)
  (*   now apply and_right. *)
  (* Qed. *)

  (* Lemma proper_cand : LR.RValid (LR.RImpl RC (LR.RImpl RC RC)) cand. *)
  (* Proof. *)
  (*   intros w0 w1 r01. *)
  (*   apply forall_r. intros c11. *)
  (*   apply forall_r. intros c12. *)
  (*   apply impl_and_adjoint. rewrite and_true_l. *)
  (*   apply forall_r. intros c21. *)
  (*   apply forall_r. intros c22. *)
  (*   apply impl_and_adjoint. *)
  (*   unfold RC at 3, LR.RBox. *)
  (*   apply forall_r. intros w2. *)
  (*   apply forall_r. intros w3. *)
  (*   apply forall_r. intros r02. *)
  (*   apply forall_r. intros r13. *)
  (*   apply forall_r. intros r23. *)
  (*   apply Acc.entails_wlp. cbn. *)
  (*   rewrite <- impl_and_adjoint. *)
  (*   unfold cand. *)
  (*   eapply proper_bind'; eauto using LR.RUnit. *)
  (*   Unshelve. 3: apply LR.RUnit. *)
  (*   - rewrite ext_and. constructor. cbn. *)
  (*     intros ι3 [[H1 H2] Heq]. *)
  (*     exact (H1 _ _ r02 r13 r23 ι3 eq_refl Heq). *)
  (*   - unfold LR.RBox. *)
  (*     apply forall_r. intros w4. *)
  (*     apply forall_r. intros w5. *)
  (*     apply forall_r. intros r24. *)
  (*     apply forall_r. intros r35. *)
  (*     apply forall_r. intros r45. *)
  (*     apply Acc.entails_wlp. *)
  (*     rewrite <- impl_and_adjoint. *)
  (*     unfold LR.RImpl. *)
  (*     apply forall_r. intros ru4. *)
  (*     apply forall_r. intros ru5. *)
  (*     rewrite <- impl_and_adjoint. *)
  (*     unfold LR.RUnit at 1. *)
  (*     rewrite and_true_r. *)
  (*     unfold RM, RC. *)
  (*     rewrite <- ?ext_and. *)
  (*     rewrite <- ?ext_trans. *)
  (*     unfold _4. *)
  (*     constructor. repeat (pred_unfold; cbn). *)
  (*     intros ι5; intros [[[] ?] ?]. *)
  (*     specialize (H0 _ _ (r02 ⊙⁻ r24) (r13 ⊙⁻ r35) r45 ι5). *)
  (*     rewrite ?inst_trans in *. *)
  (*     rewrite H1, H2 in H0. *)
  (*     specialize (H0 eq_refl eq_refl). *)
  (*     destruct (c21 w4 (r02 ⊙⁻ r24)) as *)
  (*       [(w6 & r46 & [])|], (c22 w5 (r13 ⊙⁻ r35)) as [(w7 & r57 & [])|]; try easy. *)
  (* Qed. *)

  #[global] Arguments cfalse {w} [w1] _.
  #[global] Arguments ctrue {w} [w1] _.

  Definition Flex : TYPE :=
    Ṫy -> ∀ x, ctx.In x -> ◆Unit.
  Definition Unifier : TYPE :=
    Ṫy -> Ṫy -> ◆Unit.
  Definition SolveList : TYPE :=
    List (Prod Ṫy Ṫy) -> ◆Unit.
  Definition BoxFlex : TYPE :=
    Ṫy -> ∀ x, ctx.In x -> C.
  Definition BoxUnifier : TYPE :=
    Ṫy -> Ṫy -> C.
  Definition BoxSolveList : TYPE :=
    List (Prod Ṫy Ṫy) -> C.

  Definition flex : ⊢ʷ Flex :=
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

  Definition mgu : ⊢ʷ Unifier :=
    fun w s t => T (@bmgu w s t).

  Definition boxsolvelist : ⊢ʷ BoxSolveList :=
    fix solve {w} cs {struct cs} :=
      match cs with
      | List.nil             => ctrue
      | List.cons (t1,t2) cs => cand (bmgu t1 t2) (solve cs)
      end.

  Definition solvelist : ⊢ʷ SolveList :=
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

End Variant1.

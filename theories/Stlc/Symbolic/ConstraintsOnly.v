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

From Coq Require Import
  Classes.Morphisms
  Classes.Morphisms_Prop
  Lists.List
  Strings.String.

From Equations Require Import
  Equations.
From iris Require
  bi.interface
  proofmode.tactics.
From stdpp Require Import
  base gmap.
From Em Require Import
  Context
  Environment
  Prelude
  Stlc.Alloc
  Stlc.Instantiation
  Stlc.Spec
  Stlc.Substitution
  (* Stlc.Triangular *)
  Stlc.Persistence
  Stlc.Predicates
  Stlc.Sem
  Stlc.Worlds.
  (* LogicalRelation. *)
(* From Em Require *)
(*   Unification. *)

Import ctx.notations.
Import option.notations.

#[local] Set Implicit Arguments.
#[local] Arguments step : simpl never.
#[local] Arguments reduce : simpl never.
#[local] Arguments thick : simpl never.


#[local] Notation "<{ A ~ w }>" := (persist A w) (only parsing).
#[local] Notation "s [ ζ ]" :=
  (persist s ζ)
    (at level 8, left associativity,
      format "s [ ζ ]").


Module C.

  Import World.notations.
  Import Pred Pred.notations.
  Import (hints) Sub.

  Inductive CStr (w : World) : Type :=
  | Fls
  | Eq (t1 t2 : Ṫy w)
  | And (C1 C2 : CStr w)
  | Ex {x} (C : CStr (w ▻ x)).
  #[global] Arguments Fls {w}.
  #[global] Arguments Ex [w] x C.

  Definition denote : ⊢ʷ CStr -> Pred :=
    fix den {w} C {struct C} : Pred w :=
      match C with
      | Fls       => ⊥ₚ
      | Eq t1 t2  => t1 =ₚ t2
      | And C1 C2 => den C1 /\ₚ den C2
      | Ex x C    => ∃ₚ t : Ṫy w, Ext (den C) (reduce (Θ := Sub) x t)
      (* | Ex x C    => ∃ₚ t : ty, Ext (den C) (reduce (R := Sub) x (lift t _)) *)
      (* | Ex x C    => Acc.wlp (step (R := Sub)) (den C) *)
      end%P.

  Notation "C1 /\ C2" := (C.And C1 C2).
  Notation "t1 == t2" := (C.Eq t1 t2) (at level 80).
  Notation "∃∃ n , C" :=
    (C.Ex n C)
      (at level 80, right associativity, format "∃∃ n ,  C").
End C.
Export C (CStr).

Definition persist_sim_step_alloc_env := Sub.persist_sim_step (Θ := Alloc) (T := Ėnv).
Definition persist_sim_step_alloc_ty := Sub.persist_sim_step (Θ := Alloc) (T := Ṫy).
Definition persist_sim_step_alloc_sem {A} := Sub.persist_sim_step (Θ := Alloc) (T := Sem A).

Ltac wsimpl :=
  repeat
    (rewrite ?persist_refl, ?persist_trans, ?persist_liftEnv, ?persist_liftTy,
      ?inst_lift, ?inst_reduce, ?inst_persist,
      ?inst_step_snoc, ?inst_lift_env, ?lk_trans, ?trans_refl_l, ?trans_refl_r,
      ?persist_insert, ?liftEnv_insert,

      ?Pred.ext_refl, ?Pred.ext_tpb, ?Pred.ext_and, ?Pred.ext_eq,
      ?Pred.eqₚ_refl, ?Pred.impl_true_l, ?Pred.and_true_r, ?Pred.and_true_l,
      ?Pred.impl_true_r, ?Pred.impl_false_l, ?Pred.ext_impl, ?Pred.impl_and,
      ?Pred.ext_exists, ?Pred.ext_forall, ?Pred.Acc.wlp_true, ?Pred.eq_pair,
      ?Pred.eq_func,

      ?persist_sim_step_alloc_env, ?persist_sim_step_alloc_ty, ?persist_sim_step_alloc_sem,
      (* ?S.persist_pure, ?S.persist_fmap, ?S.persist_app, *)

      (* ?ProgramLogic.eqₚ_env_cons, *)
      ?step_reduce,
      (* ?ProgramLogic.equiv_true, *)
      ?lk_reduce_zero,
      ?lk_reduce_succ;
     cbn - [lk trans step thick Sub.up1]; auto);
  repeat setoid_rewrite Pred.ext_exists;
  repeat setoid_rewrite Pred.ext_forall;
  repeat
    match goal with
    | |- context[@persist ?A ?I ?Θ ?L ?w0 ?x ?w1 ?θ] =>
        is_var x; generalize (@persist A I Θ L w0 x w1 θ); clear x; intros x;
        try (clear w0 θ)
    | |- context[fun w : Ctx nat => Ty w] =>
        change_no_check (fun w : Ctx nat => Ty w) with Ty
    | |- context[fun w : Ctx nat => Sem ?X w] =>
        change_no_check (fun w : Ctx nat => Sem X w) with (Sem X)
    end.


(* Focus on the constraint generation only, forget about solving constraints
   and any semantic values. Also try to pass the type as an input instead of
   an output, i.e. checking instead of synthesizing. *)

Section Check.
  Import World.notations.
  Import C.

  Fixpoint check (e : Exp) : ⊢ʷ Ėnv -> Ṫy -> CStr :=
    fun (w : World) (G : Ėnv w) (tr : Ṫy w) =>
      match e with
      | exp.var x =>
          match lookup x G with
          | Some t => tr == t
          | None   => Fls
          end
      | exp.true => ṫy.bool == tr
      | exp.false => ṫy.bool == tr
      | exp.ifte e1 e2 e3 =>
          check e1 G ṫy.bool /\
          check e2 G tr /\
          check e3 G tr
      | exp.absu x e =>
          ∃∃ 1, ∃∃ 2,
            let G'  := <{ G ~ step (Θ := Alloc) ⊙ step }> in
            let tr' := <{ tr ~ step (Θ := Alloc) ⊙ step }> in
            let α1  := @ṫy.var (w ▻ 1 ▻ 2) 1 (ctx.in_succ ctx.in_zero) in
            let α2  := @ṫy.var (w ▻ 1 ▻ 2) 2 ctx.in_zero in
            (ṫy.func α1 α2 == tr') /\
            check e (G' ,, x∷α1) α2
      | exp.abst x xt e =>
          ∃∃ 2,
            let G'  := <{ G ~ step (Θ := Alloc) }> in
            let tr' := <{ tr ~ step (Θ := Alloc) }> in
            let α1  := lift xt _ in
            let α2  := @ṫy.var (w ▻ 2) 2 ctx.in_zero in
            (ṫy.func α1 α2 == tr') /\
            check e (G' ,, x∷α1) α2
      | exp.app e1 e2 =>
          ∃∃ 0,
            let G'  := <{ G ~ step (Θ := Alloc) }> in
            let tr' := <{ tr ~ step (Θ := Alloc) }> in
            let α   := @ṫy.var (w ▻ 0) 0 ctx.in_zero in
            check e1 G' (ṫy.func α tr') /\
            check e2 G' α
      end.

End Check.

Import iris.bi.interface.
Import iris.proofmode.tactics.
Import Pred Pred.notations Pred.proofmode.
Import (hints) Sub.

Notation "f <$> a" := (@Sem.fmap _ _ f _ a) (at level 61, left associativity).
Notation "f <*> a" := (@Sem.app _ _ _ f a) (at level 61, left associativity).

Lemma soundness e :
  forall (w : World) G t,
    C.denote (check e G t) ⊢ (∃ₚ ee : Sem Exp w, G |--ₚ e; t ~> ee)%P.
Proof.
  induction e; cbn; intros w G tr; wsimpl.
  - destruct lookup eqn:?; cbn.
    + apply exists_r. exists (Sem.pure (exp.var x)).
      constructor. intros ι. cbn.
      constructor. now rewrite lookup_inst Heqo H.
    + apply false_l.
  - apply exists_r. exists (Sem.pure exp.true).
    constructor. intros ι. cbn. intros <-. constructor.
  - apply exists_r. exists (Sem.pure exp.false).
    constructor. intros ι. cbn. intros <-. constructor.
  - rewrite IHe1 IHe2 IHe3.
    iIntros "([%e1' H1] & [%e2' H2] & [%e3' H3])".
    iExists (exp.ifte <$> e1' <*> e2' <*> e3').
    iStopProof. constructor. intros ι (IH1 & IH2 & IH3). now constructor.
  - iIntros "(%t1 & %t2 & H)". wsimpl. rewrite IHe. wsimpl.
    iDestruct "H" as "[Heq [%e' H]]". wsimpl.
    rewrite persist_insert. cbn. wsimpl.
    iExists (exp.abst x <$> Sem.decode_ty t1 <*> e').
    iStopProof. constructor. intros ι (Heq & IH). cbn in *.
    rewrite inst_insert in IH. rewrite <- Heq. now constructor.
  - iIntros "(%t2 & H)". wsimpl. rewrite IHe. wsimpl.
    iDestruct "H" as "[Heq [%e' H]]". wsimpl.
    rewrite persist_insert. wsimpl.
    iExists (exp.abst x t <$> e').
    iStopProof. constructor. intros ι (Heq & IH). cbn in *.
    rewrite inst_insert inst_lift in Heq IH.
    rewrite <- Heq. now constructor.
  - iIntros "(%t2 & H)". wsimpl. rewrite IHe1 IHe2. wsimpl.
    iDestruct "H" as "([%e1' H1] & [%e2' H2])". wsimpl.
    iExists (exp.app <$> e1' <*> e2').
    iStopProof. constructor. intros ι (H1 & H2). cbn in *.
    econstructor; eauto.
Qed.

Import iris.proofmode.tactics.
Import (* ProgramLogic *) Pred.proofmode.
Open Scope pred_scope.

Lemma completeness_aux {G e t ee} (T : G |-- e ∷ t ~> ee) :
  forall w0 (G0 : Ėnv w0) (t0 : Ṫy w0),
    ⊢ liftEnv G _ =ₚ G0 → lift t _ =ₚ t0 → C.denote (check e G0 t0).
Proof.
  induction T; intros w0 G0 t0; wsimpl.
  - constructor. intros ι. intros _ HeqG Heqt. cbn in *.
    rewrite inst_lift_env in HeqG.
    rewrite inst_lift in Heqt. subst.
    rewrite lookup_inst in H.
    destruct lookup.
    + injection H. easy.
    + discriminate H.
  - iIntros "#HeqG #Heqt". repeat iSplit.
    + iApply IHT1; wsimpl.
    + iApply IHT2; wsimpl.
    + iApply IHT3; wsimpl.
  - iIntros "#HeqG #Heqt".
    iExists (lift t1 w0), (lift t2 _). wsimpl.
    iSplit; wsimpl.
    iIntros "!> #Heq1 !> #Heq2". wsimpl.
    iApply IHT; wsimpl.
    iApply eqₚ_insert; wsimpl.
  - iIntros "#HeqG #Heqt".
    iExists (lift t2 _). wsimpl. iSplit; wsimpl.
    iIntros "!> #Heq1".
    iApply IHT; wsimpl.
    iApply eqₚ_insert; wsimpl.
  - iIntros "#HeqG #Heqt".
    iExists (lift t2 _). iIntros "!> #Heq1".
    iSplit.
    + iApply IHT1; wsimpl.
    + iApply IHT2; wsimpl.
Qed.

Corollary completeness G e t ee (T : G |-- e ∷ t ~> ee) :
  C.denote (check e (liftEnv G _) (lift t _)) env.nil.
Proof. eapply completeness_aux; now eauto. Qed.

Theorem correctness w G e t :
  C.denote (check e G t) ⊣⊢ (∃ₚ ee : Sem Exp w, G |--ₚ e; t ~> ee)%P.
Proof.
  apply split_bientails; split.
  - apply soundness.
  - constructor; cbn. intros ι [ee H]. hnf in H.
    eapply completeness_aux; eauto; hnf.
    + constructor; hnf.
      + now rewrite inst_lift_env.
      + now rewrite inst_lift.
Qed.

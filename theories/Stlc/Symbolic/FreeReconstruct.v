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
  Strings.String.
From Equations Require Import
  Equations.
From stdpp Require Import
  base gmap.
From Em Require Import
  Context
  Environment
  Prelude
  Stlc.Alloc
  Stlc.Instantiation
  Stlc.Persistence
  Stlc.Predicates
  Stlc.Sem
  Stlc.Spec
  Stlc.Substitution
  Stlc.Symbolic.Free
  Stlc.Unification
  Stlc.Unification.CorrectnessWithAssignments
  Stlc.Worlds.

Import ctx.notations.
Import World.notations.

Set Implicit Arguments.

#[local] Notation "s [ ζ ]" :=
  (persist s ζ)
    (at level 8, left associativity,
      format "s [ ζ ]").

Section Reconstruct.
  Import MonadNotations.
  Import World.notations.

  Notation "f <$> a" := (@Sem.fmap _ _ f _ a) (at level 61, left associativity).
  Notation "f <*> a" := (@Sem.app _ _ _ f a) (at level 61, left associativity).

  Definition reconstruct : Exp -> ⊢ʷ Ėnv -> Free (Ṫy * Sem Exp) :=
    fix gen e {w} Γ :=
      match e with
      | exp.var x =>
          match lookup x Γ with
          | Some t => Ret (t , Sem.pure (exp.var x))
          | None   => Fail
          end
      | exp.true  => Ret (ṫy.bool, Sem.pure exp.true)
      | exp.false => Ret (ṫy.bool, Sem.pure exp.false)
      | exp.ifte e1 e2 e3 =>
          [ θ1 ] '(t1,e1') <- gen e1 Γ ;;
          [ θ2 ] '(t2,e2') <- gen e2 Γ[θ1] ;;
          [ θ3 ] '(t3,e3') <- gen e3 Γ[θ1⊙θ2] ;;
          [ θ4 ] _         <- assert ṫy.bool t1[θ2⊙θ3] ;;
          [ θ5 ] _         <- assert t2[θ3⊙θ4] t3[θ4] ;;
          Ret (t3[θ4⊙θ5], exp.ifte <$> e1'[θ2⊙θ3⊙θ4⊙θ5] <*> e2'[θ3⊙θ4⊙θ5] <*> e3'[θ4⊙θ5])
      | exp.absu x e =>
          [ θ1 ] t1       <- choose ;;
          [ θ2 ] '(t2,e') <- gen e (Γ[θ1] ,, x∷t1) ;;
          Ret (ṫy.func t1[θ2] t2, exp.abst x <$> Sem.decode_ty t1[θ2] <*> e')
      | exp.abst x t1 e =>
          [ θ1 ] '(t2,e') <- gen e (Γ ,, x∷lift t1 _) ;;
          Ret (ṫy.func (lift t1 _) t2, exp.abst x t1 <$> e')
      | exp.app e1 e2 =>
          [ θ1 ] '(tf, e1') <- gen e1 Γ ;;
          [ θ2 ] '(t1, e2') <- gen e2 Γ[θ1] ;;
          [ θ3 ] t2 <- choose ;;
          [ θ4 ] _  <- assert tf[θ2⊙θ3] (ṫy.func t1[θ3] t2) ;;
          Ret (t2[θ4], exp.app <$> e1'[θ2⊙θ3⊙θ4] <*> e2'[θ3⊙θ4])
      end.

  Definition reconstruct_schematic (e : Exp) : option (Schematic (Ṫy * Sem Exp)) :=
    option.bind (prenex (reconstruct e ∅)) solve_schematic.

  Definition reconstruct_grounded (e : Exp) : option (Ty * Exp) :=
    option.map
      (fun s : Schematic _ =>
         let (w, te) := s in
         inst te (grounding w))
      (reconstruct_schematic e).

End Reconstruct.

Definition persist_sim_step_alloc_env := Sub.persist_sim_step (Θ := alloc.acc_alloc) (T := Ėnv).
Definition persist_sim_step_alloc_ty := Sub.persist_sim_step (Θ := alloc.acc_alloc) (T := Ṫy).
Definition persist_sim_step_alloc_sem {A} := Sub.persist_sim_step (Θ := alloc.acc_alloc) (T := Sem A).

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
      ?Sem.persist_pure, ?Sem.persist_fmap, ?Sem.persist_app,

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
    | |- context[@persist ?A ?I ?Θ ?w0 ?x ?w1 ?θ] =>
        is_var x; generalize (@persist A I Θ w0 x w1 θ); clear x; intros x;
        try (clear w0 θ)
    | |- context[@lk ?Θ (ctx.snoc ?w0 ?α) ?w1 ?θ ?α ctx.in_zero] =>
        is_var θ;
        generalize (@lk Θ (ctx.snoc w0 α) w1 θ α ctx.in_zero);
        clear θ w0; intros ?t
    | |- context[fun w : World => Ṫy w] =>
        change_no_check (fun w : World => Ṫy w) with Ṫy
    | |- context[fun w : Ctx nat => Sem ?X w] =>
        change_no_check (fun w : World => Sem X w) with (Sem X)
    end.

Section Correctness.

  Import Pred Pred.notations.
  Import (hints) Sub.
  Import Pred.proofmode.
  Import iris.proofmode.tactics.
  Open Scope pred_scope.

  Import Pred Pred.notations.
  Import World.notations.
  Import (notations) Sem.

  #[local] Arguments Sem.decode_ty : simpl never.
  #[local] Arguments step : simpl never.
  (* #[local] Arguments Free.choose : simpl never. *)

  Lemma soundness e :
    forall (w : World) (G : Ėnv w),
      ⊢ WLP (Θ := alloc.acc_alloc) (reconstruct e G) (fun w1 θ '(t,ee) =>
                                   G[θ] |--ₚ e; t ~> ee).
  Proof.
    induction e; cbn; intros w G; unfold T, _4; wsimpl.
    - destruct lookup eqn:?; wsimpl.
      constructor. intros ι _; pred_unfold.
      constructor. now rewrite lookup_inst Heqo.
    - constructor. intros ι _. pred_unfold. constructor.
    - constructor. intros ι _. pred_unfold. constructor.
    - rewrite wlp_bind. unfold _4. cbn.
      iPoseProof (IHe1 w G) as "-#IH1". iRevert "IH1". clear IHe1.
      (* change (fun w : World => ?A w * ?B w)%type with (Prod A B). *)
      iApply (@wlp_mono alloc.acc_alloc). iIntros (w1 θ1 (t1 & e1')) "!> HT1".

      rewrite wlp_bind. unfold _4.
      iPoseProof (IHe2 w1 G[θ1]) as "-#IH2". iRevert "IH2". clear IHe2.
      iApply (@wlp_mono alloc.acc_alloc). iIntros (w2 θ2 (t2 & e2')) "!> HT2".

      rewrite wlp_bind. unfold _4.
      iPoseProof (IHe3 w2 G[θ1 ⊙ θ2]) as "-#IH3". iRevert "IH3". clear IHe3.
      iApply (@wlp_mono alloc.acc_alloc). iIntros (w3 θ3 (t3 & e3')) "!> HT3". cbn.
      iIntros "Heq1 Heq2". wsimpl.
      iStopProof. constructor. intros ι (HT1 & HT2 & HT3 & Heq1 & Heq2).
      pred_unfold. constructor; auto.

    - iIntros "!>".
      rewrite wlp_bind. unfold _4. cbn - [step].
      iPoseProof (IHe (w ▻ ctx.length w) (G[step] ,, x∷ṫy.var ctx.in_zero))
                    as "-#IH". iRevert "IH". clear IHe.
      iApply (@wlp_mono alloc.acc_alloc). iIntros (w1 θ1 (t1 & e1')).
      iIntros "!> HT". rewrite persist_insert. wsimpl.
      iStopProof. constructor. intros ι HT1. pred_unfold.
      rewrite inst_insert in HT1. now constructor.
    - rewrite wlp_bind. unfold _4. cbn.
      iPoseProof (IHe _ (G ,, x∷lift t w)) as "-#IH". iRevert "IH". clear IHe.
      iApply (@wlp_mono alloc.acc_alloc). iIntros (w1 θ1 (t1 & e1')) "!> HT". cbn.
      rewrite persist_insert. wsimpl.
      iStopProof. constructor. intros ι HT1. pred_unfold.
      rewrite inst_insert inst_lift in HT1. now constructor.
    - rewrite wlp_bind. unfold _4.
      iPoseProof (IHe1 w G) as "-#IH". iRevert "IH". clear IHe1.
      iApply (@wlp_mono alloc.acc_alloc). iIntros (w1 r1 (t12 & e1')) "!> HT1".
      rewrite wlp_bind. unfold _4.
      iPoseProof (IHe2 w1 G[r1]) as "-#IH". iRevert "IH". clear IHe2.
      iApply (@wlp_mono alloc.acc_alloc). iIntros (w2 r2 (t2 & e2')) "!> HT2". cbn.
      unfold _4. rewrite Acc.wlp_step_reduce. iIntros (t1). wsimpl.
      iStopProof. constructor. intros ι (HT1 & HT2). pred_unfold.
      econstructor; eauto.
  Qed.

  Lemma completeness_aux {G e t ee} (T : G |-- e ∷ t ~> ee) :
    forall w0 (G0 : Ėnv w0),
      ⊢ liftEnv G _ =ₚ G0 →
      WP (Θ := alloc.acc_alloc) (reconstruct e G0)
          (fun w1 r01 '(t',e') => lift t w1 =ₚ t' /\ₚ Sem.pure ee =ₚ e')%P.
  Proof.
    induction T as [G x t Hres|G|G|G e1 e1' e2 e2' e3 e3' t _ IH1 _ IH2 _ IH3
      |G x t1 t2 e e' _ IH|G x t1 t2 e e' _ IH|G e1 t2 e1' e2 t1 e2' _ IH1 _ IH2];
      intros w0 G0; wsimpl; unfold _4, Worlds.T.

    - constructor. intros ι. pred_unfold.
      intros _ ->.
      rewrite lookup_inst in Hres.
      destruct lookup.
      + injection Hres. cbn. intros <-. cbn. now pred_unfold.
      + discriminate Hres.

    - iIntros "#HeqG".
      rewrite wp_bind. unfold _4.
      iPoseProof (IH1 w0 G0 with "HeqG") as "-#IH". clear IH1. iRevert "IH".
      iApply (@wp_mono alloc.acc_alloc). iIntros (w1 r1 (t1 & e1'')) "!> (#Heq1 & #Heq2)". wsimpl.

      rewrite wp_bind. unfold _4.
      iPoseProof (IH2 w1 G0[r1] with "HeqG") as "-#IH". clear IH2. iRevert "IH".
      iApply (@wp_mono alloc.acc_alloc). iIntros (w2 r2 (t2 & e2'')) "!> (#Heq3 & #Heq4)". wsimpl.

      rewrite wp_bind. unfold _4.
      iPoseProof (IH3 w2 G0 with "HeqG") as "-#IH". clear IH3. iRevert "IH".
      iApply (@wp_mono alloc.acc_alloc). iIntros (w3 r3 (t3 & e3'')) "!> (#Heq5 & #Heq6)". wsimpl.

      iStopProof. constructor. intros ι [_ [(HeqG & Heq1 & Heq2 & Heq3 & Heq4 & Heq5 & Heq6)]].
      pred_unfold. split. auto. split. auto. split. auto.
      cbv [inst Sem.inst_sem Sem.pure Sem.app Sem.fmap] in *.
      now subst.

    - iIntros "#HeqG". rewrite Acc.wp_step_reduce. iExists (lift t1 _). iIntros "!> #Heq1".
      rewrite wp_bind. unfold _4. wsimpl.
      iPoseProof (IH _ (G0 ,, x∷ṫy.var ctx.in_zero)) as "IH". clear IH. wsimpl.
      rewrite <- eqₚ_insert. wsimpl.
      iPoseProof ("IH" with "HeqG Heq1") as "-#IH'"; iClear "IH". iRevert "IH'".
      iApply (@wp_mono alloc.acc_alloc).
      iIntros (w1 r1 (t2' & e1'')) "!> (#Heq2 & #Heq3)"; wsimpl.
      repeat iSplit; auto.
      iStopProof. constructor. intros ι [_ [(HeqG & Heq1 & Heq2 & Heq3)]].
      pred_unfold. cbv [inst Sem.inst_sem Sem.pure Sem.app Sem.fmap] in *. now subst.

    - iIntros "#HeqG".
      rewrite wp_bind. unfold _4.
      iPoseProof (IH _ (G0 ,, x∷lift t1 w0)) as "IH". clear IH. wsimpl.
      rewrite <- eqₚ_insert. wsimpl.
      iPoseProof ("IH" with "HeqG") as "-#IH'"; iClear "IH". iRevert "IH'".
      iApply (@wp_mono alloc.acc_alloc).
      iIntros (w1 r1 (t2' & e'')) "!> (#Heq1 & #Heq2)"; wsimpl.
      iSplit; auto.
      iStopProof. constructor. intros ι [_ [(HeqG & Heq1 & Heq2)]].
      pred_unfold. cbv [inst Sem.inst_sem Sem.pure Sem.app Sem.fmap] in *. now subst.

    - iIntros "#HeqG".
      rewrite wp_bind. unfold _4. wsimpl.
      iPoseProof (IH1 _ G0) as "IH"; clear IH1. wsimpl.
      iPoseProof ("IH" with "HeqG") as "-#IH'"; iClear "IH". iRevert "IH'".
      iApply (@wp_mono alloc.acc_alloc).
      iIntros (w1 r1 (tf & e1'')) "!> (#Heq1 & #Heq2)"; wsimpl.

      rewrite wp_bind. unfold _4.
      iPoseProof (IH2 w1 G0 with "HeqG") as "-#IH"; clear IH2. iRevert "IH".
      iApply (@wp_mono alloc.acc_alloc).
      iIntros (w2 r2 (t1' & e2'')) "!> (#Heq3 & #Heq4)"; wsimpl.
      rewrite Acc.wp_step_reduce.
      iExists (lift t2 w2). unfold _4. rewrite lk_refl. wsimpl.

      iStopProof. constructor. intros ι [_ [(HeqG & Heq1 & Heq2 & Heq3 & Heq4)]].
      pred_unfold. split; auto. cbv [inst Sem.inst_sem Sem.pure Sem.app Sem.fmap] in *. now subst.
  Qed.

  Theorem generator_correctness e :
    forall w (G : Ėnv w) Q (RQ : ProperPost Q),
      WP (Θ := alloc.acc_alloc) (reconstruct e G) Q ⊣⊢ₚ
      ∃ₚ t : Ṫy w, ∃ₚ ee : Sem Exp w, TPB G e t ee /\ₚ T Q (t,ee).
  Proof.
    intros w G Q RQ. unfold T. apply split_bientails. split.
    - iStartProof. rewrite wand_is_impl.
      rewrite wp_impl. iPoseProof (@soundness e w G) as "-#Hsound". iRevert "Hsound".
      iApply (@wlp_mono alloc.acc_alloc). iIntros (w1 θ1 [t e']) "!> HT HQ". wsimpl.
      iStopProof. constructor. intros ι [HT HQ]. pred_unfold.
      exists (lift (inst t ι) _).
      exists (fun _ => inst e' ι). wsimpl. pred_unfold.
      split. apply HT. revert HQ. apply RQ. wsimpl.
    - constructor. intros ι (t & e' & HT & HQ).
      pose proof (fromEntails (completeness_aux HT G) ι (MkEmp _)).
      pred_unfold. specialize (H eq_refl). revert H.
      apply wp_mono. intros w1 θ [?t ?e'] ι1 <- []. pred_unfold.
      revert HQ. apply RQ. wsimpl. f_equal; auto.
  Qed.

  Definition wp_schematic {A} (m : Schematic A) (Q : ⊢ʷ A -> Pred) : Prop :=
    match m with existT w a => exists ι : Assignment w, Q w a ι end.

  Theorem reconstruct_schematic_correct e w t e':
    reconstruct_schematic e = Some (existT w (t,e')) <->
      forall ι : Assignment w, ∅ |-- e ∷ inst t ι ~> inst e' ι.
  Proof.
    pose (fun (w : World) (θ : alloc.acc_alloc ctx.nil w) (te : Prod Ṫy (Sem Exp) w) =>
            ∅ |--ₚ e; fst te ~> snd te) as Q.
    assert (ProperPost Q) as RQ.
    { subst Q. clear. intros w θ1 [t0 e0'] [t1 e1']. wsimpl.
      constructor. intros ι [Heq1 Heq2]. pred_unfold.
      now rewrite !inst_empty. }
    pose proof (@generator_correctness e ctx.nil empty Q RQ).
    pose proof (prenex_correct (Θ := alloc.acc_alloc) (@reconstruct e ctx.nil ∅)).
    rewrite <- H0 in H. clear H0. unfold reconstruct_schematic.
    clear RQ. subst Q. unfold T in H.
    unfold wp_prenex, wp_optiondiamond, wp_diamond in H.
    destruct (prenex (reconstruct e ∅)) as [(w1 & θ1 & C & t1 & e1')|]; cbn.
    - rewrite <- option.bind_eq_some.
      admit.
    - destruct H as [H]. specialize (H env.nil). destruct H as [_ H]. cbn in H.
      split.
      + intros. discriminate.
      + intros HT. exfalso. apply H. clear H. pred_unfold.
        specialize (HT (grounding _)).
        exists (persist t (Sub.lift (grounding _))).
        exists (persist e' (Sub.lift (grounding _))). wsimpl.
        rewrite Sub.inst_lift. rewrite inst_empty. split; auto.
  Admitted.

End Correctness.


  (* (* Lemma completeness e : forall (w0 : World) (G : Env w0) {t ee}, *) *)
  (* (*   (TPB G e t ee) *) *)
  (* (*   ⊢ₚ *) *)
  (* (*   WP w0 (reconstruct e G) *) *)
  (* (*       (fun w1 r01 '(t', ee') => (<{ ee ~ r01 }> =ₚ ee' /\ₚ <{ t ~ r01 }> =ₚ t')%P). *) *)
  (* (* Proof. *) *)
  (* (*   intros. revert w0 G e t ee. apply TPB_ind; cbn. *) *)
  (* (*   - intro w. *) *)
  (* (*     apply forall_r. intros _. *) *)
  (* (*     apply forall_r. intros t. *) *)
  (* (*     apply forall_r. intros ee ι. *) *)
  (* (*     unfold T. cbn. intros _ Ht Hee. *) *)
  (* (*     now rewrite inst_persist_ty, inst_refl. *) *)
  (* (*   - intro w. *) *)
  (* (*     apply forall_r. intros _. *) *)
  (* (*     apply forall_r. intros t. *) *)
  (* (*     apply forall_r. intros ee ι. *) *)
  (* (*     unfold T. cbn. intros _ Ht Hee. *) *)
  (* (*     now rewrite inst_persist_ty, inst_refl. *) *)
  (* (*   - intro w1. *) *)
  (* (*     do 9 (apply forall_r; intros ?). *) *)
  (* (*     do 7 (rewrite <- impl_and_adjoint). *) *)
  (* (*     assert (MASSAGE: forall w (A B C D E F G : Pred w), *) *)
  (* (* bientails (andₚ (andₚ (andₚ (andₚ (andₚ (andₚ A B) C) D) E) F) G) *) *)
  (* (*           (andₚ (andₚ (andₚ (andₚ (andₚ (andₚ A B) C) G) E) F) D)) by admit. *) *)
  (* (*     rewrite MASSAGE. clear MASSAGE. *) *)
  (* (*     rewrite wp_bind. apply impl_and_adjoint. apply wp_monotonic'. *) *)
  (* (*     intros w2 r12 [t1 ee1]. cbn -[step]. unfold Definitions.T, _4. *) *)
  (* (*     rewrite wp_bind. *) *)
  (* (*     rewrite <- impl_and_adjoint. *) *)
  (* (*     rewrite (eqₚ_sym t1). *) *)
  (* (*     assert (MASSAGE: forall w (A B C D : Pred w), *) *)
  (* (*                entails (andₚ A (andₚ B C)) (andₚ C D) <-> entails (andₚ A (andₚ B ⊤ₚ)) D) by admit. *) *)
  (* (*     rewrite (MASSAGE _ _ (eqₚ (persist w1 x4 w2 r12) ee1) (eqₚ (Ty_bool w2) t1) _). *) *)
  (* (*     rewrite and_true_r. *) *)
  (* (*     admit. *) *)
  (* (*   - intros w G s t e' ι. cbn. *) *)
  (* (*     intros _ Heqo Hvar. destruct (resolve s G) eqn:?; cbn; inversion Heqo. *) *)
  (* (*     unfold T. firstorder. now rewrite refl_persist. *) *)
  (* (*   - admit. *) *)
  (* (*   - admit. *) *)
  (* (*   - admit. *) *)
  (* (* Admitted. *) *)

  (* Lemma soundness' e : forall (w0 : World) (G : Env w0), *)
  (*   Trueₚ *)
  (*   ⊢ₚ *)
  (*   WLP w0 (reconstruct e G) *)
  (*       (fun w1 r01 '(t, ee) => TPB <{G ~ r01}> e t ee). *)
  (* Proof. *)
  (*   (* induction e; cbn; intros; subst; unfold T. *) *)
  (*   (* - constructor; constructor. *) *)
  (*   (* - constructor; constructor. *) *)
  (*   (* - rewrite wlp_bind. rewrite IHe1. *) *)
  (*   (*   rewrite <- and_true_l. apply impl_and_adjoint. apply wlp_monotonic'. *) *)
  (*   (*   intros. rewrite ext_true. *) *)
  (*   (*   destruct a. rewrite <- impl_and_adjoint. *) *)
  (*   (*   cbn. rewrite <- impl_and_adjoint. unfold T. rewrite wlp_bind. *) *)
  (*   (*   specialize (IHe2 w1 <{ G ~ r ⊙ refl }>). rewrite IHe2. *) *)
  (*   (*   (* probably doable with some kind of tactic, perhaps change or replace X with Y is easier? *) *) *)
  (*   (*   assert (MASSAGE: forall w (X Y Z : Pred w), bientails (andₚ (andₚ X Y) Z) (andₚ (andₚ Y Z) X)). *) *)
  (*   (*   { intros. now rewrite (and_assoc X _), (and_comm _ X). } *) *)
  (*   (*   rewrite MASSAGE. clear MASSAGE. *) *)
  (*   (*   apply impl_and_adjoint. apply wlp_monotonic'. *) *)
  (*   (*   intros. destruct a. rewrite wlp_bind. *) *)
  (*   (*   rewrite <- impl_and_adjoint. rewrite <- and_true_r. *) *)
  (*   (*   rewrite IHe3. *) *)
  (*   (*   apply impl_and_adjoint. apply wlp_monotonic'. *) *)
  (*   (*   intros. destruct a. cbn. unfold T, _4. clear. *) *)
  (*   (*   rewrite trans_refl_r, trans_refl_r. *) *)
  (*   (*   constructor. *) *)
  (*   (*   intro. unfold Ext. unfold andₚ, implₚ, TPB. intros. *) *)
  (*   (*   destruct H as [[]]. *) *)
  (*   (*   constructor. *) *)
  (*   (*   + rewrite inst_persist_env, ?inst_trans. *) *)
  (*   (*     rewrite inst_persist_env, H2 in H. cbn in H. *) *)
  (*   (*     rewrite persist_trans. *) *)
  (*   (*     exact H. *) *)
  (*   (*   + rewrite inst_persist_env, inst_trans, inst_trans, inst_persist_ty. *) *)
  (*   (*     rewrite inst_persist_env, inst_persist_env in H3. *) *)
  (*   (*     apply H3. *) *)
  (*   (*   + rewrite inst_persist_env, inst_trans, inst_trans. *) *)
  (*   (*     rewrite inst_persist_env, inst_persist_env, inst_trans, <- H1 in H0. *) *)
  (*   (*     apply H0. *) *)
  (*   (* - destruct (resolve s G) eqn:?; cbn; try easy. *) *)
  (*   (*   unfold T. rewrite refl_persist. constructor. constructor. *) *)
  (*   (*   now rewrite resolve_inst, Heqo. *) *)
  (*   (* - rewrite <- Acc.entails_wlp. rewrite ext_true. rewrite IHe. *) *)
  (*   (*   rewrite <- and_true_l. *) *)
  (*   (*   apply impl_and_adjoint. unfold T, _4. rewrite wlp_bind. *) *)
  (*   (*   apply wlp_monotonic'. *) *)
  (*   (*   intros. rewrite ext_true. *) *)
  (*   (*   destruct a. cbn -[step]. unfold T, _4. *) *)
  (*   (*   rewrite trans_refl_r, trans_refl_r. *) *)
  (*   (*   constructor. intro. cbn -[step]. *) *)
  (*   (*   unfold Ext, andₚ, implₚ, TPB. intros. cbn -[step] in *. *) *)
  (*   (*   constructor. rewrite ?inst_persist_env in *. exact H0. *) *)
  (*   (* - rewrite wlp_bind. specialize (IHe w0 ((s, lift t w0) :: G)). rewrite IHe. *) *)
  (*   (*   rewrite <- and_true_l. *) *)
  (*   (*   apply impl_and_adjoint. *) *)
  (*   (*   apply wlp_monotonic'. *) *)
  (*   (*   intros. rewrite ext_true. destruct a. rewrite <- impl_and_adjoint. *) *)
  (*   (*   rewrite and_true_l. cbn in *. unfold T, _4. *) *)
  (*   (*   constructor. intros ι He. cbn in *. rewrite ?inst_persist_env, ?inst_persist_ty, ?trans_refl_r, ?inst_lift in *. now constructor. *) *)
  (*   (* - rewrite <- Acc.entails_wlp, ext_true, IHe2, <- and_true_l. *) *)
  (*   (*   apply impl_and_adjoint. unfold T, _4. rewrite wlp_bind. apply wlp_monotonic'. *) *)
  (*   (*   intros w1 r [t2 e2']. *) *)
  (*   (*   rewrite ext_true, wlp_bind, <- impl_and_adjoint, and_comm, IHe1. *) *)
  (*   (*   apply impl_and_adjoint. apply wlp_monotonic'. *) *)
  (*   (*   intros w2 r12 [t1 e1']. cbn -[step]. unfold T, _4. *) *)
  (*   (*   rewrite ?trans_refl_r. *) *)
  (*   (*   constructor. *) *)
  (*   (*   intros ι He2 He1 Ht1. *) *)
  (*   (*   cbn -[step] in *. *) *)
  (*   (*   rewrite ?inst_persist_ty, ?inst_persist_env, ?inst_trans, ?assoc_persist in *. *) *)
  (*   (*   rewrite Ht1 in He1. econstructor. *) *)
  (*   (*   exact He1. exact He2. *) *)
  (* Admitted. *)

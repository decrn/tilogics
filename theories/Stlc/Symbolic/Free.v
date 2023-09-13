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
From Em Require Import
  Context
  Prelude
  Stlc.Alloc
  Stlc.Instantiation
  Stlc.Persistence
  Stlc.Predicates
  Stlc.Spec
  Stlc.Substitution
  Stlc.Unification
  Stlc.Worlds.

Import ctx.notations.
Import World.notations.

Set Implicit Arguments.

Inductive Free (A : TYPE) (w : World) : Type :=
| Ret (a : A w)
| Fail
| Assertk (t1 t2 : Ṫy w) (k : Free A w)
| Choosek α (k : Free A (w ▻ α)).
#[global] Arguments Ret {A} [w] a.
#[global] Arguments Fail {A w}.
#[global] Arguments Choosek {A} [w] α k.

Section Bind.
  Context {Θ} {reflΘ : Refl Θ} {transΘ : Trans Θ} {stepΘ : Step Θ}.

  #[export] Instance bind_freem  : Bind Θ Free :=
    fun A B =>
      fix bind {w} m f {struct m} :=
      match m with
      | Ret a           => T f a
      | Fail            => Fail
      | Assertk t1 t2 k => Assertk t1 t2 (bind k f)
      | Choosek α k     => Choosek α (bind k (_4 f step))
      end.
End Bind.

Definition assert : ⊢ʷ Ṫy -> Ṫy -> Free Unit :=
  fun w t1 t2 => Assertk t1 t2 (Ret tt).
Definition choose : ⊢ʷ Free Ṫy :=
  fun w =>
    let α := ctx.length w in
    Choosek α (Ret (ṫy.var ctx.in_zero)).
#[global] Arguments choose {w}.

Section PrenexConversion.

  Import option.notations.

  Definition prenex {A} :
    ⊢ʷ Free A -> Option (Diamond alloc.acc_alloc (Prod (List (Prod Ṫy Ṫy)) A)) :=
    fix pr {w} m {struct m} :=
    match m with
    | Ret a => Some (existT w (refl, (List.nil, a)))
    | Fail => None
    | Assertk t1 t2 m =>
        '(existT w1 (r1, (cs, a))) <- pr m;;
        let t1' := persist t1 r1 in
        let t2' := persist t2 r1 in
        let c   := (t1', t2') in
        Some (existT w1 (r1, (cons c cs, a)))
    | Choosek α m =>
        '(existT w1 (r1, csa)) <- pr m ;;
        Some (existT w1 (step ⊙ r1, csa))
    end.

End PrenexConversion.

Section WithPredicates.

  Import World.notations.
  Import Pred Pred.notations.
  Import (hints) Pred Pred.Acc Sub.
  Import iris.bi.interface.
  Import iris.proofmode.tactics.
  Import Pred Pred.notations Pred.proofmode.
  Import (hints) Sub.

  Section WithAcc.

    Context {Θ} {reflΘ : Refl Θ} {lkreflΘ : LkRefl Θ}
      {transΘ : Trans Θ} {lktransΘ : LkTrans Θ} {stepΘ : Step Θ}.

    Definition WP {A} : ⊢ʷ Free A -> Box Θ (A -> Pred) -> Pred :=
      fix WP (w : World) (m : Free A w) (POST : Box Θ (A -> Pred) w) {struct m} :=
        match m with
        | Ret a => POST _ refl a
        | Fail => ⊥ₚ
        | Assertk t1 t2 k => t1 =ₚ t2 /\ₚ WP w k POST
        | Choosek α k =>
            Acc.wp step (WP (w ▻ α) k (fun w1 r01 => _4 POST step r01))
            (* ∃ₚ t : Ṫy w, *)
            (*  Ext (WP (w ▻ α) k (fun w1 r01 => _4 POST step r01)) (reduce (Θ := Sub) α t) *)
        end%P.

    Definition WLP {A} : ⊢ʷ Free A -> Box Θ (A -> Pred) -> Pred :=
      fix WLP (w : World) (m : Free A w) (POST : Box Θ (A -> Pred) w) {struct m} :=
        match m with
        | Ret a => POST _ refl a
        | Fail => ⊤ₚ
        | Assertk t1 t2 k => t1 =ₚ t2 ->ₚ WLP w k POST
        | Choosek α k =>
            (* ∀ₚ t : Ty w, *)
            (*   Ext (WLP (w ▻ α) k (fun w1 r01 => _4 POST step r01)) (reduce (R := Sub) α t) *)
            Acc.wlp step (WLP (w ▻ α) k (fun w1 r01 => _4 POST step r01))
        end%P.

    Lemma wp_mono {A w0} (m : Free A w0) (P Q : Box Θ (A -> Pred) w0) :
      (∀ w1 (θ : Θ w0 w1) (a : A w1), Acc.wlp θ (P w1 θ a → Q w1 θ a)) ⊢
      (WP m P -∗ WP m Q).
    Proof.
      induction m; cbn; iIntros "#PQ".
      - iSpecialize ("PQ" $! w (refl (Refl := reflΘ)) a); auto.
        now rewrite Acc.wlp_refl wand_is_impl.
      - easy.
      - iIntros "[#Heq HP]". iSplit; [auto|]. iRevert "HP".
        now iApply IHm.
      - rewrite wand_is_impl. iApply Acc.wp_mono. iModIntro.
        rewrite <- wand_is_impl. iApply IHm.
        iIntros (w1 θ1 a1) "!>". rewrite <- ext_trans.
        unfold _4.
        rewrite ?ext_forall.
        iSpecialize ("PQ" $! w1).
        rewrite ?ext_forall.
        iSpecialize ("PQ" $! (step ⊙ θ1)).
        rewrite ?ext_forall.
        iSpecialize ("PQ" $! a1).
        Unshelve. all: eauto.
        now rewrite Acc.ext_wlp.
    Qed.

    Lemma wlp_mono {A w0} (m : Free A w0) (P Q : Box Θ (A -> Pred) w0) :
      (∀ w1 (θ : Θ w0 w1) (a : A w1), Acc.wlp θ (P w1 θ a → Q w1 θ a)) ⊢
      (WLP m P -∗ WLP m Q).
    Proof.
      induction m; cbn; iIntros "#PQ".
      - iSpecialize ("PQ" $! w (refl (Refl := reflΘ)) a); auto.
        now rewrite Acc.wlp_refl wand_is_impl.
      - easy.
      - iIntros "HP #Heq". rewrite <- wand_is_impl.
        iSpecialize ("HP" with "Heq"). iRevert "HP".
        now iApply IHm.
      - rewrite wand_is_impl. iApply Acc.wlp_mono. iModIntro.
        rewrite <- wand_is_impl. iApply IHm.
        iIntros (w1 θ1 a1) "!>". rewrite <- ext_trans.
        unfold _4.
        rewrite ?ext_forall.
        iSpecialize ("PQ" $! w1).
        rewrite ?ext_forall.
        iSpecialize ("PQ" $! (step ⊙ θ1)).
        rewrite ?ext_forall.
        iSpecialize ("PQ" $! a1).
        Unshelve. all: eauto.
        now rewrite Acc.ext_wlp.
    Qed.

    #[export] Instance proper_wp_entails {A : TYPE} {w : World} (m : Free A w):
      Proper
        (forall_relation
           (fun w1 => pointwise_relation (Θ w w1)
                        (pointwise_relation (A w1) entails)) ==>
           entails) (@WP A w m).
    Proof.
      intros P Q PQ. unfold pointwise_relation, forall_relation in PQ.
      iStartProof. iApply wp_mono. iIntros (w1 θ1 a1) "!>".
      rewrite <- wand_is_impl. iApply PQ.
    Qed.

    #[export] Instance proper_wp_bientails {A : TYPE} {w : World} (m : Free A w):
      Proper
        (forall_relation
           (fun w1 => pointwise_relation (Θ w w1)
                        (pointwise_relation (A w1) (⊣⊢ₚ))) ==>
           (⊣⊢ₚ)) (@WP A w m).
    Proof.
      intros P Q PQ. unfold pointwise_relation, forall_relation in PQ.
      apply split_bientails; split; apply proper_wp_entails; intros w1 θ1 a1;
      specialize (PQ w1 θ1 a1); now apply split_bientails in PQ.
    Qed.

    #[export] Instance proper_wlp_entails {A : TYPE} {w : World} (m : Free A w):
      Proper
        (forall_relation
           (fun w1 => pointwise_relation (Θ w w1)
                        (pointwise_relation (A w1) entails)) ==>
           entails) (@WLP A w m).
    Proof.
      intros P Q PQ. unfold pointwise_relation, forall_relation in PQ.
      iStartProof. iApply wlp_mono. iIntros (w1 θ1 a1) "!>".
      rewrite <- wand_is_impl. iApply PQ.
    Qed.

    #[export] Instance proper_wlp_bientails {A : TYPE} {w : World} (m : Free A w):
      Proper
        (forall_relation
           (fun w1 => pointwise_relation (Θ w w1)
                        (pointwise_relation (A w1) (⊣⊢ₚ))) ==>
           (⊣⊢ₚ)) (@WLP A w m).
    Proof.
      intros P Q PQ. unfold pointwise_relation, forall_relation in PQ.
      apply split_bientails; split; apply proper_wlp_entails; intros w1 θ1 a1;
      specialize (PQ w1 θ1 a1); now apply split_bientails in PQ.
    Qed.

    Lemma wp_monotonic' {A w0} (m : Free A w0) (R : Pred w0) (P Q : Box Θ (A -> Pred) w0) :
      (forall w1 (θ : Θ w0 w1) (a : A w1),
          Ext R θ ⊢ₚ P w1 θ a ->ₚ Q w1 θ a) ->
      R ⊢ₚ WP m P ->ₚ WP m Q.
    Proof. Admitted.

    Lemma wlp_monotonic' {A w0} (m : Free A w0) (R : Pred w0) (P Q : Box Θ (A -> Pred) w0) :
      (forall w1 (θ : Θ w0 w1) (a : A w1),
          Ext R θ ⊢ₚ P w1 θ a ->ₚ Q w1 θ a) ->
      R ⊢ₚ WLP m P ->ₚ WLP m Q.
    Proof. Admitted.

    Lemma wp_frame2 {A w} (m : Free A w) (P : Box Θ (A -> Pred) w) (Q : Pred w) :
      WP m P /\ₚ Q ⊣⊢ₚ WP m (fun _ θ a => P _ θ a /\ₚ Ext Q θ)%P.
    Proof. Admitted.

    Lemma wp_bind {refltransθ : ReflTrans Θ}
      {A B w0} (m : Free A w0) (f : Box Θ (A -> Free B) w0) :
      forall (Q : Box Θ (B -> Pred) w0),
        WP (bind m f) Q ⊣⊢ₚ
        WP m (fun w1 θ1 a => WP (f _ θ1 a) (_4 Q θ1)).
    Proof.
      intros. unfold _4. induction m; cbn; try (firstorder; fail).
      - apply split_bientails; split; iApply wp_mono; iIntros (w1 θ b1) "!>";
          rewrite trans_refl_l; auto.
      - apply Acc.proper_wp_bientails. rewrite IHm. unfold _4.
        apply proper_wp_bientails. intros w1 θ1 a1.
        apply proper_wp_bientails. intros w2 θ2 b2.
        now rewrite trans_assoc.
    Qed.

    Lemma wlp_bind  {refltransθ : ReflTrans Θ}
      {A B w1} (m : Free A w1) (f : Box Θ (A -> Free B) w1) :
      forall (Q : Box Θ (B -> Pred) w1),
        WLP (bind m f) Q ⊣⊢ₚ
        WLP m (fun w1 θ1 a => WLP (f _ θ1 a) (_4 Q θ1)).
    Proof.
      intros. unfold _4. induction m; cbn; try (firstorder; fail).
      - apply split_bientails; split; iApply wlp_mono; iIntros (w1 θ b1) "!>";
          rewrite trans_refl_l; auto.
      - apply Acc.proper_wlp_bientails. rewrite IHm. unfold _4.
        apply proper_wlp_bientails. intros w1 θ1 a1.
        apply proper_wlp_bientails. intros w2 θ2 b2.
        now rewrite trans_assoc.
    Qed.

    Lemma wp_impl {A w} (m : Free A w) (P : Box Θ (A -> Pred) w) (Q : Pred w) :
      (WP m P ->ₚ Q) ⊣⊢ₚ WLP m (fun w1 r01 a1 => P w1 r01 a1 ->ₚ Ext Q r01)%P.
    Proof.
      induction m; cbn; unfold _4, Basics.impl.
      - now rewrite ext_refl.
      - apply impl_false_l.
      - rewrite impl_and. now rewrite IHm.
      - rewrite Acc.wp_impl. apply Acc.proper_wlp_bientails. rewrite IHm. clear IHm.
        apply proper_wlp_bientails. iIntros (w1 θ1 a1). now rewrite ext_trans.
    Qed.

    #[local] Existing Instance instpred_prod_ty.

    Fixpoint incl_alloc {w0 w1} (θ : Alloc w0 w1) : Θ w0 w1 :=
      match θ with
      | alloc.refl => refl
      | alloc.fresh θ' => step ⊙ incl_alloc θ'
      end.

    Definition wp_prenex {A} :
      ⊢ʷ Option (Diamond alloc.acc_alloc (List (Ṫy * Ṫy) * A)) -> Box Θ (A -> Pred) -> Pred :=
      fun w0 o Q => wp_optiondiamond o (fun w1 θ '(C,a) => instpred C /\ₚ Q w1 (incl_alloc θ) a)%P.

    Definition wlp_prenex {A} :
      ⊢ʷ Option (Diamond alloc.acc_alloc (List (Ṫy * Ṫy) * A)) -> Box Θ (A -> Pred) -> Pred :=
      fun w0 o Q => wlp_optiondiamond o (fun w1 θ '(C,a) => instpred C ->ₚ Q w1 (incl_alloc θ) a)%P.

    Lemma prenex_correct {A w} (m : Free A w) (Q : Box Θ (A -> Pred) w) :
      wp_prenex (prenex m) Q ⊣⊢ₚ WP m Q.
    Proof.
      induction m; cbn - [reduce step].
      - rewrite Acc.wp_refl. rewrite and_true_l. reflexivity.
      - reflexivity.
      - destruct (prenex m) as [(w' & r & C & a)|]; cbn.
        + rewrite <- IHm.
          rewrite Acc.and_wp_r.
          apply Acc.proper_wp_bientails.
          now rewrite ext_eq and_assoc.
        + rewrite <- IHm. now rewrite and_false_r.
      - destruct (prenex m) as [(w' & r & C & a)|]; cbn - [reduce step].
        + change (alloc.fresh ?r) with (step ⊙ r). rewrite Acc.wp_trans.
          rewrite (Acc.wp_step_reduce (Θ := alloc.acc_alloc)).
          rewrite <- (Acc.wp_step_reduce (Θ := Θ)).
          apply Acc.proper_wp_bientails.
          rewrite <- IHm. cbn - [reduce step Sub.of].
          apply Acc.proper_wp_bientails.
          apply proper_and_bientails; auto.
        + rewrite <- IHm. now rewrite Acc.wp_false.
    Qed.

    Lemma prenex_correct' {A w} (m : Free A w) (Q : Box Θ (A -> Pred) w) :
      wlp_prenex (prenex m) Q ⊣⊢ₚ WLP m Q.
    Proof.
      induction m; cbn - [reduce step].
      - rewrite Acc.wlp_refl. rewrite impl_true_l. reflexivity.
      - reflexivity.
      - rewrite <- IHm. clear IHm. unfold wlp_prenex.
        rewrite wlp_optiondiamond_bind'.
        destruct (prenex m) as [(w' & r & C & a)|]; cbn.
        + rewrite Acc.wlp_frame. apply Acc.proper_wlp_bientails.
          rewrite <- bi.impl_curry, ext_eq.
          reflexivity.
        + rewrite impl_true_r. reflexivity.
      - rewrite <- IHm. clear IHm. unfold wlp_prenex.
        rewrite wlp_optiondiamond_bind'.
        destruct (prenex m) as [(w' & r & C & a)|]; cbn.
        + change (alloc.fresh ?r) with (step ⊙ r). rewrite Acc.wlp_trans.
          rewrite (Acc.wlp_step_reduce (Θ := alloc.acc_alloc)).
          rewrite <- (Acc.wlp_step_reduce (Θ := Θ)).
          reflexivity.
        + now rewrite Acc.wlp_true.
    Qed.

  End WithAcc.

  Definition wp_schematic {A} (m : Schematic A) (Q : ⊢ʷ A -> Pred) : Prop :=
    match m with existT w a => exists ι : Assignment w, Q w a ι end.

  Definition solvefree {A} {persA : Persistence.Persistent A} (m : Free A ctx.nil) :
    option (Schematic A) := option.bind (prenex m) solve_schematic.

  (* Lemma solve_equiv {A} {persA : Persistent A} *)
  (*   (m : Diamond Alloc _ ctx.nil) (Q : Box Alloc (A -> Pred) [ctx]) : *)
  (*   (* (RQ : ProperPost Q) : *) *)
  (*   wp_optiondiamond (solve m) Q ⊣⊢ₚ wp_diamond m Q. *)
  (* Proof. *)
  (*   rewrite <- prenex_correct. unfold solvefree. *)
  (*   unfold wp_prenex, wp_optiondiamond. *)
  (*   destruct (prenex m) as [(w1 & r1 & C & a)|]; cbn; [|easy]. *)
  (*   pose proof (solvelist_complete C) as Hcompl. *)
  (*   pose proof (solvelist_sound C) as Hsound. *)
  (*   destruct solvelist as [(w2 & r2 & [])|]; cbn in *. *)
  (*   - apply split_bientails. split. *)
  (*     + destruct Hsound as [Hsound]. constructor. *)
  (*       intros ι0 (ι2 & Heq & HQ); pred_unfold; subst. exists (inst r2 ι2). *)
  (*       specialize (Hsound (inst r2 ι2) I ι2 eq_refl). hnf in Hsound. *)
  (*       unfold andₚ. repeat split. *)
  (*       * destruct (env.view (inst r1 (inst r2 ι2))). *)
  (*         destruct (env.view (inst alloc.nil_l ι2)). *)
  (*         reflexivity. *)
  (*       * assumption. *)
  (*       * admit. *)
  (*         (* epose proof (RQ w1 r1 _ a (inst r2 ι2)) as H1. *) *)
  (*         (* epose proof (RQ w2 alloc.nil_l _ (persist _ a _ r2) ι2) as H2. *) *)
  (*         (* cbn in H1, H2. *) *)
  (*     + destruct Hcompl as [Hcompl]. constructor. *)
  (*       intros ι0 (ι1 & Heq1 & HC & HQ). *)
  (*       specialize (Hcompl ι1 HC). destruct Hcompl as (ι2 & Heq2 & _). *)
  (*       exists ι2. split. subst. *)
  (*       * destruct (env.view (inst r1 (inst r2 ι2))). *)
  (*         destruct (env.view (inst alloc.nil_l ι2)). *)
  (*         reflexivity. *)
  (*       * clear - HQ. admit. *)
  (*   - apply split_bientails. split. firstorder. *)
  (*     destruct Hcompl as [Hcompl]. constructor. *)
  (*     intros ι (ι1 & Heq & HC & HQ). apply (Hcompl ι1 HC). *)
  (* Admitted. *)

End WithPredicates.

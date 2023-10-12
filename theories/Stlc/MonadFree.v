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
From iris Require Import
  proofmode.tactics.
From Em Require Import
  Prelude
  Stlc.Alloc
  Stlc.Instantiation
  Stlc.MonadInterface
  Stlc.Persistence
  Stlc.Predicates
  Stlc.Spec
  Stlc.Substitution
  Stlc.Worlds.

Import Pred Pred.notations Pred.Acc Sub Pred.proofmode world.notations.

#[local] Set Implicit Arguments.

Inductive Free (A : TYPE) (w : World) : Type :=
| Ret (a : A w)
| Fail
| Assertk (t1 t2 : Ṫy w) (k : Free A w)
| Choosek α (k : Free A (w ▻ α)).
#[global] Arguments Ret {A} [w] a.
#[global] Arguments Fail {A w}.
#[global] Arguments Choosek {A} [w] α k.

#[export] Instance pure_free : Pure Free :=
  fun A w a => Ret a.

#[export] Instance bind_free `{reflΘ : Refl Θ, transΘ : Trans Θ, stepΘ : Step Θ} :
  Bind Θ Free :=
  fun A B =>
    fix bind {w} m f {struct m} :=
    match m with
    | Ret a           => f _ refl a
    | Fail            => Fail
    | Assertk t1 t2 k => Assertk t1 t2 (bind k f)
    | Choosek α k     => Choosek α (bind k (_4 f step))
    end.

#[export] Instance tcm_free : TypeCheckM Free :=
  {| assert w τ1 τ2 := Assertk τ1 τ2 (Ret tt);
     pick w := let α := world.fresh w in
               Choosek α (Ret (ṫy.var world.in_zero));
     fail A w := Fail;
  |}.

Section Logic.

  Context {Θ} {reflΘ : Refl Θ} {lkreflΘ : LkRefl Θ}
    {transΘ : Trans Θ} {lktransΘ : LkTrans Θ}
    {stepΘ : Step Θ} {lkstepΘ : LkStep Θ}
    {refltransθ : ReflTrans Θ}.

  #[export] Instance wp_free : WeakestPre Θ Free :=
    fun A =>
      fix WP (w : World) (m : Free A w) (POST : Box Θ (A ⇢ Pred) w) {struct m} :=
      match m with
      | Ret a => POST _ refl a
      | Fail => ⊥ₚ
      | Assertk t1 t2 k => t1 =ₚ t2 /\ₚ WP w k POST
      | Choosek α k =>
          Acc.wp step (WP (w ▻ α) k (fun w1 r01 => _4 POST step r01))
      end%P.

  #[export] Instance wlp_free : WeakestLiberalPre Θ Free :=
    fun A =>
      fix WLP (w : World) (m : Free A w) (POST : Box Θ (A ⇢ Pred) w) {struct m} :=
      match m with
      | Ret a => POST _ refl a
      | Fail => ⊤ₚ
      | Assertk t1 t2 k => t1 =ₚ t2 ->ₚ WLP w k POST
      | Choosek α k =>
          Acc.wlp step (WLP (w ▻ α) k (fun w1 r01 => _4 POST step r01))
      end%P.

  Lemma wp_free_mono [A w0] (m : Free A w0) (P Q : Box Θ (A ⇢ Pred) w0) :
    (∀ w1 (θ : Θ w0 w1) (a : A w1), Acc.wlp θ (P w1 θ a -∗ Q w1 θ a)) ⊢
    (WP m P -∗ WP m Q).
  Proof.
    induction m; cbn; iIntros "#PQ"; unfold _4.
    - iSpecialize ("PQ" $! w (refl (Refl := reflΘ)) a); auto.
      now rewrite Acc.wlp_refl.
    - easy.
    - iIntros "[#Heq HP]". iSplit; [auto|]. iRevert "HP". now iApply IHm.
    - iApply Acc.wp_mono. iModIntro. iApply IHm.
      iIntros (w1 θ1 a1) "!>". rewrite <- persist_pred_trans.
      rewrite persist_forall. iSpecialize ("PQ" $! w1).
      rewrite persist_forall. iSpecialize ("PQ" $! (step ⊙ θ1)).
      rewrite persist_forall. iSpecialize ("PQ" $! a1).
      Unshelve. all: auto.
      now rewrite Acc.persist_wlp.
  Qed.

  Lemma wlp_free_mono [A w0] (m : Free A w0) (P Q : Box Θ (A ⇢ Pred) w0) :
    (∀ w1 (θ : Θ w0 w1) (a : A w1), Acc.wlp θ (P w1 θ a -∗ Q w1 θ a)) ⊢
    (WLP m P -∗ WLP m Q).
  Proof.
    induction m; cbn; iIntros "#PQ"; unfold _4.
    - iSpecialize ("PQ" $! w (refl (Refl := reflΘ)) a); auto.
      now rewrite Acc.wlp_refl.
    - easy.
    - iIntros "HP #Heq". rewrite <- wand_is_impl.
      iSpecialize ("HP" with "Heq"). iRevert "HP". now iApply IHm.
    - iApply Acc.wlp_mono. iModIntro. iApply IHm.
      iIntros (w1 θ1 a1) "!>". rewrite <- persist_pred_trans.
      rewrite persist_forall. iSpecialize ("PQ" $! w1).
      rewrite persist_forall. iSpecialize ("PQ" $! (step ⊙ θ1)).
      rewrite persist_forall. iSpecialize ("PQ" $! a1).
      Unshelve. all: eauto.
      now rewrite Acc.persist_wlp.
  Qed.

  Section ProperInstances.

    #[local] Notation "∀ x , P" :=
    (@forall_relation _ _ (fun x => P%signature))
      (at level 200, x binder, right associativity) : signature_scope.
    #[local] Notation "A → P" :=
      (@pointwise_relation A _ P%signature) : signature_scope.

    #[export] Instance proper_wp_entails {A w} (m : Free A w) :
      Proper ((∀ w1, Θ w w1 → A w1 → entails) ==> entails) (WP m).
    Proof.
      intros P Q PQ. iApply wp_free_mono. iIntros (w1 θ1 a1) "!>".
      iApply PQ.
    Qed.

    #[export] Instance proper_wp_bientails {A w} (m : Free A w) :
      Proper ((∀ w1, Θ w w1 → A w1 → (⊣⊢ₚ)) ==> (⊣⊢ₚ)) (WP m).
    Proof.
      intros P Q PQ. unfold pointwise_relation, forall_relation in PQ.
      apply split_bientails; split; apply proper_wp_entails; intros w1 θ1 a1;
        specialize (PQ w1 θ1 a1); now apply split_bientails in PQ.
    Qed.

    #[export] Instance proper_wlp_entails {A w} (m : Free A w) :
      Proper ((∀ w1, Θ w w1 → A w1 → entails) ==> entails) (WLP m).
    Proof.
      intros P Q PQ. iApply wlp_free_mono. iIntros (w1 θ1 a1) "!>".
      iApply PQ.
    Qed.

    #[export] Instance proper_wlp_bientails {A w} (m : Free A w):
      Proper ((∀ w1, Θ w w1 → A w1 → (⊣⊢ₚ)) ==> (⊣⊢ₚ)) (WLP m).
    Proof.
      intros P Q PQ. unfold pointwise_relation, forall_relation in PQ.
      apply split_bientails; split; apply proper_wlp_entails; intros w1 θ1 a1;
      specialize (PQ w1 θ1 a1); now apply split_bientails in PQ.
    Qed.

  End ProperInstances.

  #[export] Instance tcmlogic_free : TypeCheckLogicM Θ Free.
  Proof.
    constructor; intros; predsimpl; cbn; unfold _4;
      auto using wp_free_mono, wlp_free_mono.
    - induction m; cbn; try (firstorder; fail).
      + apply proper_wp_bientails. intros w1 θ1 b1.
        now rewrite trans_refl_l.
      + apply Acc.proper_wp_bientails. rewrite IHm. unfold _4.
        apply proper_wp_bientails. intros w1 θ1 a1.
        apply proper_wp_bientails. intros w2 θ2 b2.
        now rewrite trans_assoc.
    - induction m; predsimpl; try (firstorder; fail).
      + apply proper_wlp_bientails. intros w1 θ1 b1. now rewrite trans_refl_l.
      + rewrite IHm.
        apply proper_wlp_bientails. intros w1 θ1 a1.
        apply proper_wlp_bientails. intros w2 θ2 b2.
        now rewrite trans_assoc.
    - induction m.
      + predsimpl.
      + predsimpl.
      + predsimpl. now rewrite IHm.
      + rewrite Acc.wp_impl. apply Acc.proper_wlp_bientails. rewrite IHm.
        apply proper_wlp_bientails. intros w1 θ1 a1.
        now rewrite <- persist_pred_trans.
  Qed.

End Logic.

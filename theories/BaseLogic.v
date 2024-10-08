(******************************************************************************)
(* Copyright (c) 2023 Steven Keuchel                                          *)
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

From Coq Require Import Classes.Morphisms Classes.Morphisms_Prop
  Classes.RelationClasses Relations.Relation_Definitions Strings.String.
From iris Require Import bi.derived_laws proofmode.tactics.
From stdpp Require Import base.

From Em Require Export Environment Open Instantiation Substitution Worlds.
From Em Require Import Prefix Spec Sub.Parallel.

Import world.notations.

#[local] Set Implicit Arguments.
#[local] Arguments step : simpl never.
#[local] Arguments thick : simpl never.

#[local] Notation "Q [ θ ]" := (_4 Q θ)
  (at level 7, left associativity, format "Q [ θ ]") : box_scope.
#[local] Notation "P [ θ ]" := (subst P θ)
  (at level 7, left associativity, format "P [ θ ]") : bi_scope.

Module Pred.

  Definition Pred (w : World) : Type := Assignment w -> Prop.
  Bind Scope bi_scope with Pred.

  Section Definitions.

    Definition oeq {T : OType} {A : Type} {instTA : Inst T A} : ⊧ T ↠ T ↠ Pred :=
      fun w t1 t2 ι => inst t1 ι = inst t2 ι.
    #[global] Arguments oeq {T A _} [w] _ _ _/.
    Definition otyping_decl : ⊧ OEnv ↠ Const Exp ↠ OTy ↠ OExp ↠ Pred :=
      fun w G e t ee ι => inst G ι |-- e ∷ inst t ι ~> inst ee ι.
    #[global] Arguments otyping_decl [w] G e t ee ι/.

    #[export] Instance subst_pred : Subst Pred :=
      fun Θ w1 P w2 θ ι2 => P (inst θ ι2).
    #[global] Arguments subst_pred Θ [w] _ [w1] _ _ /.

  End Definitions.

  Section RewriteRelations.

    Context {w : World}.

    Record bientails (P Q : Pred w) : Prop :=
      MkBientails { fromBientails : forall ι, P ι <-> Q ι }.
    Record entails (P Q : Pred w) : Prop :=
      MkEntails { fromEntails : forall ι, P ι -> Q ι }.

    #[export] Instance pred_equiv : Equiv (Pred w) := bientails.
    #[export] Instance pred_equivalence : Equivalence (≡@{Pred w}).
    Proof. firstorder. Qed.

    #[export] Instance preorder_entails : RelationClasses.PreOrder entails.
    Proof. firstorder. Qed.
    #[export] Instance subrelation_bientails_entails :
      subrelation (≡@{Pred w}) entails.
    Proof. firstorder. Qed.
    #[export] Instance subrelation_bientails_flip_entails :
      subrelation (≡@{Pred w}) (flip entails).
    Proof. firstorder. Qed.

    (* #[export] Instance proper_bientails : *)
    (*   Proper (bientails ==> bientails ==> iff) bientails. *)
    (* Proof. intuition. Qed. *)
    #[export] Instance proper_entails_bientails :
      Proper ((≡@{Pred w}) ==> (≡@{Pred w}) ==> iff) entails.
    Proof. firstorder. Qed.
    #[export] Instance proper_entails_entails :
      Proper (entails --> entails ==> impl) entails.
    Proof. firstorder. Qed.

  End RewriteRelations.
  #[global] Arguments bientails {w} (_ _)%bi_scope.
  #[global] Arguments entails {w} (_ _)%bi_scope.

  Module Import proofmode.

    Variant empty {w} (ι : Assignment w) : Prop :=
      MkEmpty : empty ι.
    Variant sep {w} (P Q : Pred w) (ι : Assignment w) : Prop :=
      MkSep : P ι -> Q ι -> sep P Q ι.
    Variant wand {w} (P Q : Pred w) (ι : Assignment w) : Prop :=
      MkWand : (P ι -> Q ι) -> wand P Q ι.
    Variant persistently {w} (P : Pred w) (ι : Assignment w) : Prop :=
      MkPersistently : P ι -> persistently P ι.

    #[export] Instance ofe_dist_pred {w} : Dist (Pred w) := discrete_dist.

    (* Iris defines [bi_later_mixin_id] for BI algebras without later. However,
       the identity function as later still causes some later-specific
       typeclasses to be picked. We just define our own trivial modality and
       mixin to avoid that. *)
    Variant later {w} (P : Pred w) (ι : Assignment w) : Prop :=
      MkLater : P ι → later P ι.

    Canonical bi_pred {w : World} : bi.
    Proof.
      refine
        {| bi_car := Pred w;
           bi_entails := entails;
           bi_emp := empty;
           bi_pure P _ := P;
           bi_and P Q ι := P ι ∧ Q ι;
           bi_or P Q ι := P ι ∨ Q ι;
           bi_impl P Q ι := P ι → Q ι;
           bi_forall A f ι := ∀ a, f a ι;
           bi_exist A f ι := ∃ a, f a ι;
           bi_sep := sep;
           bi_wand := wand;
           bi_persistently := persistently;
           bi_later := later;
        |}.
      all: abstract firstorder.
    Defined.

    #[export] Instance persistent_pred {w} {P : Pred w} : Persistent P.
    Proof. constructor. intros ι HP. constructor. exact HP. Qed.

    #[export] Instance affine_pred {w} : BiAffine (@bi_pred w) | 0.
    Proof. firstorder. Qed.
    #[export] Hint Immediate affine_pred : core.

    Export iris.bi.derived_laws.

  End proofmode.

  Module Import notations.

    Notation "⊤" := (@bi_pure (@bi_pred _) True) : bi_scope.
    Notation "⊥" := (@bi_pure (@bi_pred _) False) : bi_scope.
    Infix "≈" := oeq (at level 70, no associativity) : bi_scope.
    Notation "G |--ₚ E ; T ~> EE" :=
      (otyping_decl G E T EE) (at level 70, no associativity) : bi_scope.

  End notations.

  Lemma bientails_unfold [w] (P Q : Pred w) :
    (P ⊣⊢ Q) ↔ ∀ ι, P ι ↔ Q ι.
  Proof. firstorder. Qed.
  Lemma entails_unfold [w] (P Q : Pred w) :
    (P ⊢ Q) ↔ ∀ ι, P ι → Q ι.
  Proof. firstorder. Qed.
  Lemma sep_unfold w (P Q : Pred w) :
    ∀ ι, bi_sep P Q ι ↔ (P ι ∧ Q ι).
  Proof. firstorder. Qed.
  Lemma wand_unfold w (P Q : Pred w) :
    ∀ ι, bi_wand P Q ι ↔ (P ι → Q ι).
  Proof. firstorder. Qed.
  Lemma intuitionistically_unfold w (P : Pred w) :
    ∀ ι, bi_intuitionistically P ι ↔ P ι.
  Proof. firstorder. Qed.

  Create HintDb pred_unfold.
  #[export] Hint Rewrite bientails_unfold entails_unfold sep_unfold wand_unfold
    intuitionistically_unfold (@inst_subst OEnv Env _ _ _)
    (@inst_subst OExp Exp _ _ _) (@inst_subst OTy Ty _ _ _)
    (@inst_lift OEnv Env _ _ _) (@inst_lift OExp Exp _ _ _)
    (@inst_lift OTy Ty _ _ _) (@inst_thin Par _ Par.lk_thin_par)
    @inst_refl @inst_trans @inst_insert @Open.inst_pure
    @oexp.inst_var @oexp.inst_true @oexp.inst_false @oexp.inst_ifte
    @oexp.inst_absu @oexp.inst_abst @oexp.inst_app : pred_unfold.

  Ltac punfold_connectives :=
    change (@bi_and (@bi_pred _) ?P ?Q ?ι) with (P ι ∧ Q ι) in *;
    change (@bi_or (@bi_pred _) ?P ?Q ?ι) with (P ι ∨ Q ι) in *;
    change (@bi_impl (@bi_pred _) ?P ?Q ?ι) with (P ι → Q ι) in *;
    change (@bi_iff (@bi_pred _) ?P ?Q ?ι) with (iff (P ι) (Q ι)) in *;
    change (@bi_pure (@bi_pred _) ?P _) with P in *;
    change (@bi_forall (@bi_pred _) ?A ?P) with (fun ι => ∀ a : A, P a ι) in *;
    change (@bi_exist (@bi_pred _) ?A ?P) with (fun ι => ∃ a : A, P a ι) in *;
    change (@subst Pred subst_pred _ _ ?P _ ?θ ?ι) with (P (inst θ ι)) in *;
    try progress (cbn beta).

  (* A tactic that unfold all the predicates to expose the underlying
      definitions. This is mainly used to finish proofs. *)
  Ltac pred_unfold :=
    repeat
      (punfold_connectives;
       try rewrite_db pred_unfold; auto 1 with typeclass_instances;
       cbn [oeq otyping_decl inst inst_ty inst_env] in *;
       try
         match goal with
         | |- forall ι : Assignment _, _ =>
             let ι := fresh "ι" in
             intro ι; pred_unfold;
             first [clear ι | revert ι]
         | |- @bi_emp_valid (@bi_pred _) _ => constructor; intros ι _; cbn
         | |- @bi_entails (@bi_pred _) _ _ => constructor; intros ι; cbn
         | |- context[@inst ?AT ?A ?I ?w ?x ?ι] =>
             is_var x; generalize (@inst AT A I w x ι);
             clear x; intro x; subst
         end).

  Section Lemmas.

    Create HintDb obligation.
    #[local] Hint Rewrite @inst_refl @inst_trans : obligation.

    #[local] Ltac obligation :=
      cbv [Proper flip respectful pointwise_relation forall_relation];
      repeat (autorewrite with obligation in *; cbn in *; intros; subst; pred_unfold);
      repeat
        (match goal with
         | H: _ ⊢ _ |- _ => destruct H as [H]
         | H: _ ⊣⊢ _ |- _ => destruct H as [H]
         | H: forall (H : ?A), _, a : ?A |- _ =>
           specialize (H a); autorewrite with obligation in H; cbn in H
         | |- (forall _ : ?A, _) <-> (forall _ : ?A, _) =>
             apply all_iff_morphism; intro; autorewrite with obligation; cbn
         | |- (exists _ : ?A, _) <-> (exists _ : ?A, _) =>
             apply ex_iff_morphism; intro; autorewrite with obligation; cbn
         end);
      try easy; try (intuition; fail); try (intuition congruence; fail).
    #[local] Obligation Tactic := obligation.

    #[local] Hint Rewrite <- @tactics.forall_and_distr : obligation.

    #[export] Instance proper_subst_bientails {Θ w} :
      Proper ((⊣⊢) ==> forall_relation (fun _ => eq ==> (⊣⊢)))
      (@subst Pred Pred.subst_pred Θ w).
    Proof. obligation. Qed.

    Lemma split_bientails {w} (P Q : Pred w) : (P ⊣⊢ Q) <-> (P ⊢ Q) ∧ (Q ⊢ P).
    Proof. obligation. Qed.
    Lemma impl_and_adjoint {w} (P Q R : Pred w) : (P ∧ Q ⊢ R) <-> (P ⊢ Q → R).
    Proof. obligation. Qed.
    Lemma and_true_l {w} (P : Pred w) : ⊤ ∧ P ⊣⊢ P.
    Proof. obligation. Qed.
    Lemma and_true_r {w} (P : Pred w) : P ∧ ⊤ ⊣⊢ P.
    Proof. obligation. Qed.
    Lemma and_false_l {w} (P : Pred w) : ⊥ ∧ P ⊣⊢ ⊥.
    Proof. obligation. Qed.
    Lemma and_false_r {w} (P : Pred w) : P ∧ ⊥ ⊣⊢ ⊥.
    Proof. obligation. Qed.
    Lemma impl_true_l {w} (P : Pred w) : (⊤ → P) ⊣⊢ P.
    Proof. obligation. Qed.
    Lemma impl_true_r {w} (P : Pred w) : (P → ⊤) ⊣⊢ ⊤.
    Proof. obligation. Qed.
    Lemma impl_false_l {w} (P : Pred w) : (⊥ → P) ⊣⊢ ⊤.
    Proof. obligation. Qed.
    (* Lemma false_l {w} (P : Pred w) : ⊥ ⊢ P. *)
    (* Proof. obligation. Qed. *)
    (* Lemma true_r {w} (P : Pred w) : P ⊢ ⊤. *)
    (* Proof. obligation. Qed. *)
    (* Lemma impl_forget {w} (P Q R : Pred w) : (P ⊢ R) → (P ⊢ (Q → R)). *)
    (* Proof. obligation. Qed. *)
    Lemma impl_and [w] (P Q R : Pred w) : (P ∧ Q → R) ⊣⊢ (P → Q → R).
    Proof. obligation. Qed.
    (* Lemma forall_l {I : Type} {w} (P : I -> Pred w) Q : *)
    (*   (∃ x : I, P x ⊢ Q) -> (∀ x : I, P x) ⊢ Q. *)
    (* Proof. obligation. firstorder. Qed. *)
    (* Lemma forall_r {I : Type} {w} P (Q : I -> Pred w) : *)
    (*   (P ⊢ (∀ x : I, Q x)) <-> (∀ x : I, (P ⊢ Q x)). *)
    (* Proof. obligation. firstorder. Qed. *)

    Lemma exists_l {I : Type} {w} (P : I -> Pred w) (Q : Pred w) :
      (∀ x : I, P x ⊢ Q) -> (∃ x : I, P x) ⊢ Q.
    Proof. obligation; firstorder. Qed.
    Lemma exists_r {I : Type} {w} P (Q : I -> Pred w) :
      (∃ x : I, P ⊢ Q x) -> P ⊢ (∃ x : I, Q x).
    Proof. obligation; firstorder. Qed.
    #[global] Arguments exists_r {I w P Q} _.

    Lemma wand_is_impl [w] (P Q : Pred w) : (P -∗ Q) ⊣⊢ (P → Q).
    Proof. obligation. Qed.

    Lemma pApply {w} {P Q R : Pred w} : (P ⊢ Q) -> (Q ⊢ R) -> (P ⊢ R).
    Proof. now transitivity Q. Qed.

    Lemma pApply_r {w} {P Q R : Pred w} : (Q ⊢ R) → (P ⊢ Q) → (P ⊢ R).
    Proof. now transitivity Q. Qed.

    Section Eq.

      Context {T A} {instTA : Inst T A}.

      Lemma oeq_intro {w} (t : T w) : ⊢ t ≈ t.
      Proof. obligation. Qed.

      Lemma oeq_refl {w} (t : T w) : t ≈ t ⊣⊢ ⊤.
      Proof. obligation. Qed.

      Lemma oeq_sym {w} (s t : T w) : s ≈ t ⊣⊢ t ≈ s.
      Proof. obligation. Qed.

      Lemma oeq_trans {w} (s t u : T w) : s ≈ t ∧ t ≈ u ⊢ s ≈ u.
      Proof. obligation. Qed.

    End Eq.
    #[global] Arguments oeq_trans {T A _ w} s t u.

    Lemma oeq_ty_noconfusion {w} (t1 t2 : OTy w) :
      t1 ≈ t2 ⊣⊢
      match t1 , t2 with
      | oty.evar  _      , _                => t1 ≈ t2
      | _                , oty.evar _       => t1 ≈ t2
      | oty.bool         , oty.bool         => True
      | oty.func t11 t12 , oty.func t21 t22 => t11 ≈ t21 ∧ t12 ≈ t22
      | _                , _                => False
      end.
    Proof. destruct t1, t2; obligation. Qed.

    Lemma oeq_pair
      {AT BT : OType} {A B : Type} {instA : Inst AT A} {instB : Inst BT B}
      [w] (a1 a2 : AT w) (b1 b2 : BT w) :
      (a1,b1) ≈ (a2,b2)  ⊣⊢  a1 ≈ a2 ∧ b1 ≈ b2.
    Proof.
      pred_unfold. intros ι; cbn. split.
      - now injection 1.
      - intros []. now f_equal.
    Qed.

    Section Subst.

      Lemma subst_eq {T : OType} {substT : Subst T}
        {A : Type} {instTA : Inst T A} {instSubstTA : InstSubst T A}
        {Θ : SUB} {w0 w1} (θ : Θ w0 w1) (t1 t2 : T w0) :
        (t1 ≈ t2)[θ] ⊣⊢ t1[θ] ≈ t2[θ].
      Proof.
        pred_unfold. unfold subst, subst_pred. intros ι.
        now rewrite !inst_subst.
      Qed.

      Context {Θ : SUB}.

      (* We could define a SubstLaws instance for the Pred type, but that
         requires functional extensionality. Instead, we provide similar
         lemmas that use bientailment instead of Leibniz equality and thus
         avoid functional extensionality. *)
      Lemma subst_pred_refl `{lkReflΘ : LkRefl Θ} [w] (P : Pred w) :
        P[refl] ⊣⊢ P.
      Proof. obligation. Qed.
      Lemma subst_pred_trans `{lktransΘ : LkTrans Θ}
        {w0 w1 w2} (θ1 : Θ w0 w1) (θ2 : Θ w1 w2) (P : Pred w0) :
        P[θ1 ⊙ θ2] ⊣⊢ P[θ1][θ2].
      Proof. obligation. Qed.
      Lemma subst_and {w0 w1} (θ : Θ w0 w1) (P Q : Pred w0) :
        (P ∧ Q)[θ] ⊣⊢ P[θ] ∧ Q[θ].
      Proof. obligation. Qed.
      Lemma subst_impl {w0 w1} (θ : Θ w0 w1) (P Q : Pred w0) :
        (P → Q)[θ] ⊣⊢ (P[θ] → Q[θ]).
      Proof. obligation. Qed.
      Lemma subst_wand {w0 w1} (θ : Θ w0 w1) (P Q : Pred w0) :
        (P -∗ Q)[θ] ⊣⊢ (P[θ] -∗ Q[θ]).
      Proof. obligation. Qed.
      Lemma subst_false {w0 w1} (θ : Θ w0 w1) :
        ⊥[θ] ⊣⊢ ⊥.
      Proof. obligation. Qed.
      Lemma subst_true {w0 w1} (θ : Θ w0 w1) :
        ⊤[θ] ⊣⊢ ⊤.
      Proof. obligation. Qed.
      Lemma subst_forall [A] [w0 w1] (θ : Θ w0 w1) (Q : A -> Pred w0) :
        (∀ a : A, Q a)[θ] ⊣⊢ (∀ a : A, (Q a)[θ]).
      Proof. obligation. Qed.
      Lemma subst_exists [A] [w0 w1] (θ : Θ w0 w1) (Q : A -> Pred w0) :
        (∃ a : A, Q a)[θ] ⊣⊢ (∃ a : A, (Q a)[θ]).
      Proof. obligation. Qed.

      Lemma subst_typing {w0 w1} (θ : Θ w0 w1) G (e : Exp) (t : OTy w0) (ee : OExp w0) :
        (G |--ₚ e; t ~> ee)[θ] ⊣⊢ G[θ] |--ₚ e; t[θ] ~> ee[θ].
      Proof. obligation. Qed.

    End Subst.

  End Lemmas.

  Module Sub.
    Import (hints) Par.
    Section WithSubstitution.
      Context {Θ : SUB}.

      Definition wp {w0 w1} (θ : Θ w0 w1) (Q : Pred w1) : Pred w0 :=
        fun ι0 => ∃ (ι1 : Assignment w1), inst θ ι1 = ι0 ∧ Q ι1.
      Definition wlp {w0 w1} (θ : Θ w0 w1) (Q : Pred w1) : Pred w0 :=
        fun ι0 => ∀ (ι1 : Assignment w1), inst θ ι1 = ι0 → Q ι1.

      #[global] Arguments wp {_ _} _ _ ι0/.
      #[global] Arguments wlp {_ _} _ _ ι0/.

      #[export] Instance proper_wp_bientails {w0 w1} (θ : Θ w0 w1) :
        Proper ((⊣⊢) ==> (⊣⊢)) (wp θ).
      Proof. firstorder. Qed.

      #[export] Instance proper_wp_entails {w0 w1} (θ : Θ w0 w1) :
        Proper ((⊢) ==> (⊢)) (wp θ).
      Proof. firstorder. Qed.

      #[export] Instance proper_wlp_bientails {w0 w1} (θ : Θ w0 w1) :
        Proper ((⊣⊢) ==> (⊣⊢)) (wlp θ).
      Proof. firstorder. Qed.

      #[export] Instance proper_wlp_entails {w0 w1} (θ : Θ w0 w1) :
        Proper ((⊢) ==> (⊢)) (wlp θ).
      Proof. firstorder. Qed.

      Lemma wp_refl {reflΘ : Refl Θ} {lkreflΘ : LkRefl Θ}
        {w} (Q : Pred w) : wp refl Q ⊣⊢ Q.
      Proof.
        unfold wp; pred_unfold. intros ι; split.
        - intros (ι' & Heq & HQ). now subst.
        - intros HQ. exists ι. easy.
      Qed.

      Lemma wp_trans {transR : Trans Θ} {lktransΘ : LkTrans Θ}
        {w0 w1 w2} (θ1 : Θ w0 w1) (θ2 : Θ w1 w2) Q :
        wp (θ1 ⊙ θ2) Q ⊣⊢ wp θ1 (wp θ2 Q).
      Proof.
        unfold wp; pred_unfold. intros ι; split.
        - intros (ι2 & Heq & HQ). eauto.
        - intros (ι1 & Heq1 & ι2 & Heq2 & HQ). subst. eauto.
      Qed.

      Lemma wp_false {w0 w1} (θ : Θ w0 w1) :
        wp θ ⊥ ⊣⊢ ⊥.
      Proof. firstorder. Qed.

      Lemma and_wp_l {w0 w1} (θ : Θ w0 w1) P Q :
        wp θ P ∧ Q ⊣⊢ wp θ (P ∧ Q[θ]).
      Proof.
        unfold wp; pred_unfold. split.
        - intros [(ι1 & <- & HP) HQ]. eauto.
        - intros (ι1 & <- & HP & HQ). eauto.
      Qed.

      Lemma and_wp_r {w0 w1} (θ : Θ w0 w1) (P : Pred w0) (Q : Pred w1) :
        P ∧ wp θ Q ⊣⊢ wp θ (P[θ] ∧ Q).
      Proof. now rewrite bi.and_comm and_wp_l bi.and_comm. Qed.

      Lemma wp_thick {thickΘ : Thick Θ} {lkThickΘ : LkThick Θ}
        {w α} (αIn : world.In α w) (t : OTy (w - α)) (Q : Pred (w - α)) :
        wp (thick α t) Q ⊣⊢ oty.evar αIn ≈ t[thin (Θ := Par) α] ∧ Q[thin (Θ := Par) α].
      Proof.
        unfold wp; pred_unfold. intros ι. split.
        - intros (ι1 & Heq & HQ). subst.
          now rewrite inst_thick env.remove_insert env.lookup_insert.
        - intros [Heq HQ]. exists (env.remove α ι αIn).
          now rewrite inst_thick -Heq env.insert_remove.
      Qed.

      Lemma wlp_refl {reflΘ : Refl Θ} {lkreflΘ : LkRefl Θ}
        {w} (Q : Pred w) : wlp refl Q ⊣⊢ Q.
      Proof.
        unfold wlp; pred_unfold. intros ι. split.
        - intros HQ. auto.
        - intros HQ ? <-. auto.
      Qed.

      Lemma wlp_trans {transR : Trans Θ} {lktransΘ : LkTrans Θ}
        {w0 w1 w2} (θ1 : Θ w0 w1) (θ2 : Θ w1 w2) Q :
        wlp (θ1 ⊙ θ2) Q ⊣⊢ wlp θ1 (wlp θ2 Q).
      Proof.
        unfold wlp; pred_unfold. intros ι. split.
        - intros HQ ι1 Heq1 ι2 Heq2. subst; auto.
        - intros HQ ι2 Heq. subst; eauto.
      Qed.

      Lemma wlp_true {w0 w1} (θ : Θ w0 w1) :
        wlp θ ⊤ ⊣⊢ ⊤.
      Proof. firstorder. Qed.

      (* Lemma wlp_and {w0 w1} (θ : Θ w0 w1) P Q : *)
      (*   wlp θ P ∧ wlp θ Q ⊣⊢ wlp θ (P ∧ Q). *)
      (* Proof. firstorder. Qed. *)

      (* Lemma wp_or {w0 w1} (θ : Θ w0 w1) P Q : *)
      (*   wp θ P ∨ wp θ Q ⊣⊢ wp θ (P ∨ Q). *)
      (* Proof. firstorder. Qed. *)

      Lemma wp_mono {w0 w1} (θ : Θ w0 w1) P Q :
        wlp θ (P -∗ Q) ⊢ wp θ P -∗ wp θ Q.
      Proof. firstorder. Qed.

      Lemma wlp_mono {w0 w1} (θ : Θ w0 w1) P Q :
        wlp θ (P -∗ Q) ⊢ wlp θ P -∗ wlp θ Q.
      Proof. firstorder. Qed.

      Lemma entails_wlp {w0 w1} (θ : Θ w0 w1) P Q :
        (P[θ] ⊢ Q) ↔ (P ⊢ wlp θ Q).
      Proof.
        unfold wlp; pred_unfold. split; intros HPQ.
        - intros ι0 HP ι1 <-. revert HP. apply HPQ.
        - intros ι1 HP. now apply (HPQ (inst θ ι1)).
      Qed.

      Lemma entails_wp {w0 w1} (θ : Θ w0 w1) P Q :
        (P ⊢ Q[θ]) ↔ (wp θ P ⊢ Q).
      Proof.
        unfold wp; pred_unfold. split; intros HPQ.
        - intros ι0 (ι1 & <- & HP). now apply HPQ.
        - intros ι1 HP. apply (HPQ (inst θ ι1)). exists ι1. split; auto.
      Qed.

      Lemma wp_impl {w0 w1} (θ1 : Θ w0 w1) (P : Pred _) (Q : Pred _) :
        (wp θ1 P → Q) ⊣⊢ wlp θ1 (P → Q[θ1]).
      Proof.
        unfold wp, wlp; pred_unfold. intros ι0; split.
        - intros H ι1 <- HP. apply H. now exists ι1.
        - intros HPQ (ι1 & <- & HP). now apply HPQ.
      Qed.

      Lemma subst_wlp {w0 w1} {θ : Θ w0 w1} (P : Pred w1) :
        (wlp θ P)[θ] ⊢ P.
      Proof. firstorder. Qed.

      Lemma subst_wp {w0 w1} {θ : Θ w0 w1} (P : Pred w1) :
        P ⊢ (wp θ P)[θ].
      Proof. firstorder. Qed.

      Lemma wlp_frame {w0 w1} (θ : Θ w0 w1) (P : Pred _) (Q : Pred _) :
        (P → wlp θ Q) ⊣⊢ wlp θ (P[θ] → Q).
      Proof.
        unfold wlp; pred_unfold. intros ι; split.
        - intros H ι1 <- HP. now apply (H HP).
        - intros H HP ι1 <-. apply H; auto.
      Qed.

    End WithSubstitution.
    (* #[global] Opaque wp. *)
    (* #[global] Opaque wlp. *)

    Lemma intro_wp_step' {Θ} {stepΘ : Step Θ} {lkStepΘ : LkStep Θ}
      {w α} (P : Pred w) (Q : Pred (w ، α)) (t : Ty) :
      (P[step] ⊢ lift t ≈ oty.evar world.in_zero → Q) →
      (P ⊢ wp (step (Θ := Θ)) Q).
    Proof.
      pred_unfold. intros H ι HP. set (ι1 := env.snoc ι α t). exists ι1.
      specialize (H ι1). rewrite inst_step in H |- *; cbn in *. intuition.
    Qed.

    (* Better for iris proof mode. *)
    Lemma intro_wp_step {Θ} {stepΘ : Step Θ} {lkStepΘ : LkStep Θ}
      t {w α} (Q : Pred (w ، α)) :
      wlp step (lift t ≈ oty.evar world.in_zero → Q) ⊢ wp (step (Θ := Θ)) Q.
    Proof. apply (intro_wp_step' t). now rewrite subst_wlp. Qed.

    (* Lemma wp_split  {Θ : SUB} [w0 w1] (θ : Θ w0 w1) P : *)
    (*   wp θ ⊤ ∧ wlp θ P ⊢ wp θ P. *)
    (* Proof. now rewrite and_wp_l subst_wlp and_true_l. Qed. *)

    Lemma wp_hmap `{LkHMap Θ1 Θ2} [w0 w1] (θ : Θ1 w0 w1) P :
      wp (hmap θ) P ⊣⊢ wp θ P.
    Proof.
      constructor. intros ι0; cbn. apply ex_iff_morphism.
      intro ι1. now rewrite inst_hmap.
    Qed.

    Lemma wlp_hmap `{LkHMap Θ1 Θ2} [w0 w1] (θ : Θ1 w0 w1) P :
      wlp (hmap θ) P ⊣⊢ wlp θ P.
    Proof.
      constructor. intros ι0; cbn. apply all_iff_morphism.
      intro ι1. now rewrite inst_hmap.
    Qed.

  End Sub.

  Section InstPred.

    (* A type class for things that can be interpreted as a predicate. *)
    Class InstPred (A : OType) :=
      instpred : ⊧ A ↠ Pred.
    #[global] Arguments instpred {_ _ _}.

    (* #[export] Instance instpred_option {A} `{ipA : InstPred A} : *)
    (*   InstPred (Option A) := *)
    (*   fun w o => wp_option o instpred. *)
    #[export] Instance instpred_list {A} `{ipA : InstPred A} :
      InstPred (List A) :=
      fun w =>
        fix ip xs {struct xs} :=
        match xs with
        | nil       => ⊤
        | cons y ys => instpred y ∧ ip ys
        end%I.
    #[local] Instance instpred_prod_ty : InstPred (OTy * OTy) :=
      fun w '(t1,t2) => oeq t1 t2.
    #[export] Instance instpred_unit : InstPred Unit :=
      fun w _ => ⊤%I.
    #[global] Arguments instpred_unit [w] _ /.

    Lemma instpred_list_app {A} `{ipA : InstPred A} [w] (xs ys : List A w) :
      instpred (xs ++ ys) ⊣⊢ instpred xs ∧ instpred ys.
    Proof.
      induction xs; cbn.
      - now rewrite and_true_l.
      - rewrite -bi.and_assoc. now apply bi.and_proper.
    Qed.

    Class InstPredSubst A {ipA : InstPred A} {subA : Subst A} :=
      instpred_subst [Θ : SUB] {w0 w1} (θ : Θ w0 w1) (a : A w0) :
        instpred a[θ] ⊣⊢ (instpred a)[θ].
    #[global] Arguments InstPredSubst _ {_ _}.

    #[export] Instance instpred_subst_list `{InstPredSubst A} :
      InstPredSubst (List A).
    Proof.
      intros Θ w0 w1 θ xs. unfold subst, subst_list.
      induction xs; cbn; [easy|]. now rewrite instpred_subst IHxs.
    Qed.

    #[local] Instance instpred_subst_prod_ty : InstPredSubst (OTy * OTy).
    Proof. intros Θ w0 w1 θ [τ1 τ2]; cbn. now rewrite subst_eq. Qed.

  End InstPred.

  Lemma pno_cycle {w} (t1 t2 : OTy w) (Hsub : oty.OTy_subterm t1 t2) :
    t1 ≈ t2 ⊢ ⊥.
  Proof.
    constructor. intros ι Heq. apply (inst_subterm ι) in Hsub.
    rewrite <- Heq in Hsub. now apply ty.no_cycle in Hsub.
  Qed.

  Lemma oeq_insert {w} (G1 G2 : OEnv w) (x : string) (t1 t2 : OTy w) :
    G1 ≈ G2 ∧ t1 ≈ t2 ⊢
    insert (M := OEnv w) x t1 G1 ≈ insert (M := OEnv w) x t2 G2.
  Proof. pred_unfold. intros []. now f_equal. Qed.

  Lemma oeq_func {w} (s1 s2 t1 t2 : OTy w) :
    oty.func s1 s2 ≈ oty.func t1 t2 ⊣⊢ (s1 ≈ t1) ∧ (s2 ≈ t2).
  Proof. now rewrite oeq_ty_noconfusion. Qed.

  #[export] Instance params_tpb : Params (@otyping_decl) 1 := {}.
  #[export] Instance params_ifte : Params (@oexp.ifte) 1 := {}.
  #[export] Instance params_oeq : Params (@oeq) 4 := {}.
  #[export] Instance params_subst : Params (@subst) 4 := {}.

  Definition PBox {Θ} : ⊧ Box Θ Pred ↠ Pred :=
    fun w Q => (∀ w' (θ : Θ w w'), Sub.wlp θ (Q w' θ))%I.
  Notation "◼ Q" := (PBox Q%B) (at level 6, right associativity, format "◼ Q").

  Section PBoxModality.

    (* We instantiate the iris modality elimination machinery for the ◼ modality.
       That means every time we have a hypothesis with that modality at the
       head, we can eliminate it. Eliminating the modality from ◼P will simply
       use P at the current world w, which is accessible as witnessed y refl. *)
    #[export] Instance elimpbox `{LkRefl Θ} (p : bool)
      {w} (P : ◻Pred w) (Q : Pred w) :
      ElimModal True p true ◼P (P w refl) Q Q.
    Proof.
      intros _. iIntros "[H1 H2]". iApply "H2".
      iPoseProof (bi.intuitionistically_if_elim with "H1") as "#HBox".
      iModIntro. iStopProof. pred_unfold. intros ι HP. apply HP, inst_refl.
    Qed.

    (* Substitution distributes over ◼. *)
    Lemma subst_pbox `{LkTrans Θ} [w] (Q : ◻Pred w) [w1] (θ1 : Θ w w1) :
      (◼Q)[θ1] ⊢ ◼(Q[θ1]).
    Proof.
      constructor; intros ι1 HQ w2 θ2 ι2 <-.
      apply HQ. now rewrite inst_trans.
    Qed.

    #[export] Instance elimsubstpbox (Θ : SUB) (p : bool)
      {w} (P : ◻Pred w) [w1] (θ1 : Θ w w1) (Q : Pred w1) :
      ElimModal True p true ◼P[θ1] (P w1 θ1) Q Q.
    Proof.
      intros _. iIntros "[H1 H2]". iApply "H2".
      iPoseProof (bi.intuitionistically_if_elim with "H1") as "#HBox".
      iModIntro. iStopProof. pred_unfold. intros ι HP. now apply HP.
    Qed.

  End PBoxModality.

  Section IntoSubst.

    Context {Θ : SUB}.

    (* We use the [IntoSubst] type class to perform logic programming that
       will automatically push substitutions down. The idea is that [y] is
       equivalent to [x] with the substitution [θ] applied. *)
    Class IntoSubst `{Inst T A, Subst T}
      [w0 w1] (θ : Θ w0 w1) (x : T w0) (y : T w1) : Prop :=
      into_subst : ⊢ x[θ] ≈ y.

    (* The default instance (with lower priority) simply applies [θ] to [t]. *)
    #[export] Instance into_subst_default `{Inst T A, Subst T}
      [w0 w1] (θ : Θ w0 w1) (t : T w0) : IntoSubst θ t (subst t θ) | 10.
    Proof. easy. Qed.

    #[export] Instance into_subst_subst `{LkTrans Θ, Inst T A, SubstLaws T}
      [w0 w1 w2] (θ1 : Θ w0 w1) (θ2 : Θ w1 w2) (t : T w0) :
      IntoSubst θ2 (subst t θ1) (subst t (θ1 ⊙ θ2)) | 0.
    Proof. unfold IntoSubst. now rewrite subst_trans. Qed.

    #[export] Instance into_subst_lift {T A} `{Inst T A, SubstLift T A}
      [w0 w1] (θ : Θ w0 w1) (a : A) : IntoSubst θ (lift a) (lift a) | 0.
    Proof. unfold IntoSubst. now rewrite subst_lift. Qed.

    #[export] Instance into_subst_insert
      [w0 w1] (θ : Θ w0 w1) (G0 : OEnv w0) x (τ0 : OTy w0) G1 τ1
      (HG : IntoSubst θ G0 G1) (Hτ : IntoSubst θ τ0 τ1) :
      IntoSubst θ (G0 ,, x ∷ τ0) (G1 ,, x ∷ τ1) | 0.
    Proof.
      unfold IntoSubst in *. rewrite subst_insert.
      iApply oeq_insert. now iSplit.
    Qed.

  End IntoSubst.
  #[global] Hint Mode IntoSubst + + + + + + + + - - : typeclass_instances.

  Section IntoSubstPred.

    Context {Θ : SUB} [w1 w2] (θ : Θ w1 w2).

    (* We use the [IntoSubstPred] type class to perform logic programming that
       will automatically push substitutions down into predicates. The idea is
       that the substitution [θ] applied to [P] is stronger than [Q]. [P] should
       be chosen as weak as possible though. *)
    Class IntoSubstPred (P : Pred w1) (Q : Pred w2) : Prop :=
      into_substpred : P[θ] ⊢ Q.

    (* The default instance (with lower priority) simply applies [θ] to [t]. *)
    #[export] Instance into_substpred_default (P : Pred w1) :
      IntoSubstPred P P[θ] | 10.
    Proof. easy. Qed.

    #[export] Instance into_substpred_substpred `{LkTrans Θ} [w0] (θ' : Θ w0 w1)
      (P : Pred w0) : IntoSubstPred P[θ'] P[θ' ⊙ θ] | 0.
    Proof. unfold IntoSubstPred. now rewrite subst_pred_trans. Qed.

    #[export] Instance into_substpred_typing (G1 : OEnv w1) (e : Exp)
      (τ1 : OTy w1) (ee1 : OExp w1) G2 τ2 ee2 (HG : IntoSubst θ G1 G2)
      (Hτ : IntoSubst θ τ1 τ2) (Hee : IntoSubst θ ee1 ee2) :
      IntoSubstPred (G1 |--ₚ e; τ1 ~> ee1)%I (G2 |--ₚ e; τ2 ~> ee2)%I.
    Proof.
      unfold IntoSubst, IntoSubstPred in *. rewrite subst_typing.
      destruct HG as [HG], Hτ as [Hτ], Hee as [Hee]. constructor.
      intros ι. cbn. now rewrite ?HG ?Hτ ?Hee.
    Qed.

    #[export] Instance into_substpred_eq `{InstSubst T A} (x1 x2 : T w1)
      (y1 y2 : T w2) (Hxy1 : IntoSubst θ x1 y1) (Hxy2 : IntoSubst θ x2 y2) :
      IntoSubstPred (x1 ≈ x2)%I (y1 ≈ y2)%I | 0.
    Proof.
      unfold IntoSubst, IntoSubstPred in *. rewrite subst_eq.
      destruct Hxy1 as [Hxy1], Hxy2 as [Hxy2]. constructor.
      intros ι. cbn. now rewrite ?Hxy1 ?Hxy2.
    Qed.

    #[export] Instance into_substpred_wlp (P : Pred w2) :
      IntoSubstPred (Sub.wlp θ P) P.
    Proof. apply Sub.subst_wlp. Qed.

  End IntoSubstPred.
  #[global] Hint Mode IntoSubstPred + + + + - - : typeclass_instances.

  Section WlpModality.

    Context {Θ : SUB} [w0 w1] (θ : Θ w0 w1).

    (* We instantiate the iris modality introduction machinery for the wlp
       modality. The effect of introducing [wlp θ] is to run the substitution
       [θ] over all hypotheses and eliminate [wlp θ] from the head of the
       goal. *)
    Class IntoWlp (P : Pred w0) (Q : Pred w1) :=
      into_wlp : P ⊢ Sub.wlp θ Q.

    #[export] Instance into_wlp_default (P : Pred w0) Q
      (H : IntoSubstPred θ P Q) : IntoWlp P Q | 10.
    Proof. apply Sub.entails_wlp, H. Qed.

    Definition modality_wlp_mixin :
      modality_mixin (Sub.wlp θ)
        (MIEnvTransform IntoWlp)
        (MIEnvTransform IntoWlp).
    Proof. firstorder. Qed.

    Definition modality_wlp : modality bi_pred bi_pred :=
      Modality _ (modality_wlp_mixin).

    #[export] Instance from_modal_wlp P :
      FromModal True modality_wlp (Sub.wlp θ P) (Sub.wlp θ P) P.
    Proof. firstorder. Qed.

  End WlpModality.

  #[global] Arguments IntoWlp {Θ} [w0 w1] θ P Q.
  #[global] Arguments into_wlp {Θ} [w0 w1] θ P Q {_}.
  #[global] Hint Mode IntoWlp + + + + - - : typeclass_instances.

  Import (hints) Par.

  Create HintDb predsimpl.
  #[export] Hint Rewrite (@subst_eq OEnv _ _ _ _) (@subst_eq OTy _ _ _ _)
    (@subst_refl OEnv _ _) (@subst_refl OTy _ _) (@subst_trans OEnv _ _)
    (@subst_trans OTy _ _) @Sub.wlp_refl @Sub.wlp_trans @Sub.wlp_true
    @Sub.wp_false @Sub.wp_refl @Sub.wp_trans @and_false_l @and_false_r
    @and_true_l @and_true_r @oeq_func @oeq_refl @impl_and @impl_false_l
    @impl_true_l @impl_true_r @lk_refl @lk_step @lk_trans @subst_and @subst_false
    @subst_pred_refl @subst_pred_trans @subst_typing @subst_true @trans_refl_r
    : predsimpl.
  Ltac predsimpl :=
    repeat
      (try (progress cbn); unfold _4;
       change_no_check (@gmap.gmap string _ _ (OTy ?w)) with (OEnv w) in *;
       repeat
         match goal with
         | |- Sub.wp ?θ _ ⊣⊢ Sub.wp ?θ _ => apply Sub.proper_wp_bientails
         | |- Sub.wlp ?θ _ ⊣⊢ Sub.wlp ?θ _ => apply Sub.proper_wlp_bientails
         end;
       try easy; repeat rewrite_db predsimpl; auto 1 with typeclass_instances;
       repeat
         match goal with
         | |- context[@subst ?A ?I ?Θ ?w0 ?x ?w1 ?θ] =>
             is_var x; generalize (@subst A I Θ w0 x w1 θ); clear x; intros x;
             try (clear w0 θ)
         | |- context[@lk ?Θ (?w0 ، ?α) ?w1 ?θ ?α world.in_zero] =>
             is_var θ;
             generalize (@lk Θ (w0 ، α) w1 θ α world.in_zero);
             clear θ w0; intros ?t
         end).

End Pred.
Export Pred (Pred).

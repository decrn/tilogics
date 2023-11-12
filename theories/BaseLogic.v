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
From iris Require bi.derived_connectives bi.interface proofmode.tactics.
From stdpp Require Import base.

From Em Require Export Environment Open Prelude Instantiation Persistence Worlds.
From Em Require Import Prefix Spec Sub.Parallel.

Import world.notations.

#[local] Set Implicit Arguments.
#[local] Arguments step : simpl never.
#[local] Arguments thick : simpl never.

#[local] Notation "Q [ θ ]" :=
  (fun _ θ' => Q _ (θ ⊙ θ'))
    (at level 8, left associativity,
      format "Q [ θ ]") : box_scope.

Declare Scope pred_scope.
Delimit Scope pred_scope with P.

#[local] Notation "P [ θ ]" :=
  (persist P θ)
    (at level 8, left associativity,
      format "P [ θ ]") : pred_scope.

Module Pred.


  Definition Pred (w : World) : Type :=
    Assignment w -> Prop.
  Bind Scope pred_scope with Pred.

  Section Definitions.

    Definition eqₚ {T : OType} {A : Type} {instTA : Inst T A} :
      ⊧ T ⇢ T ⇢ Pred :=
      fun w t1 t2 ι => inst t1 ι = inst t2 ι.
    #[global] Arguments eqₚ {T A _} [w] _ _ _/.

    Definition TPB : ⊧ OEnv ⇢ Const Exp ⇢ OTy ⇢ OExp ⇢ Pred :=
      fun w G e t ee ι => inst G ι |-- e ∷ inst t ι ~> inst ee ι.
    #[global] Arguments TPB [w] G e t ee ι/.

    #[export] Instance persist_pred : Persistent Pred :=
      fun Θ w1 P w2 θ ι2 => P (inst θ ι2).
    #[global] Arguments persist_pred Θ [w] _ [w1] _ _ /.

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
      subrelation (≡@{Pred w}) (Basics.flip entails).
    Proof. firstorder. Qed.

    (* #[export] Instance proper_bientails : *)
    (*   Proper (bientails ==> bientails ==> iff) bientails. *)
    (* Proof. intuition. Qed. *)
    #[export] Instance proper_entails_bientails :
      Proper ((≡@{Pred w}) ==> (≡@{Pred w}) ==> iff) entails.
    Proof. firstorder. Qed.
    #[export] Instance proper_entails_entails :
      Proper (Basics.flip entails ==> entails ==> Basics.impl) entails.
    Proof. firstorder. Qed.

  End RewriteRelations.
  #[global] Arguments bientails {w} (_ _)%P.
  #[global] Arguments entails {w} (_ _)%P.

  Module Import proofmode.

    Import iris.bi.interface.

    Variant empₚ {w} (ι : Assignment w) : Prop :=
      MkEmp : empₚ ι.
    Variant sepₚ {w} (P Q : Pred w) (ι : Assignment w) : Prop :=
      MkSep : P ι -> Q ι -> sepₚ P Q ι.
    Variant wandₚ {w} (P Q : Pred w) (ι : Assignment w) : Prop :=
      MkWand : (P ι -> Q ι) -> wandₚ P Q ι.
    Variant persistently {w} (P : Pred w) (ι : Assignment w) : Prop :=
      MkPersistently : P ι -> persistently P ι.

    #[export] Instance ofe_dist_pred {w} : ofe.Dist (Pred w) :=
      ofe.discrete_dist.

    (* Iris defines [bi_later_mixin_id] for BI algebras without later. However,
       the identity function as later still causes some later-specific
       typeclasses to be picked. We just define our own trivial modality and
       mixin to avoid that. *)
    Variant later {w} (P : Pred w) (ι : Assignment w) : Prop :=
      MkLater : P ι -> later P ι.

    Canonical bi_pred {w : World} : bi.
    Proof.
      refine
        {| bi_car := Pred w;
           bi_entails := entails;
           bi_emp := empₚ;
           bi_pure P _ := P;
           bi_and P Q ι := P ι /\ Q ι;
           bi_or P Q ι := P ι \/ Q ι;
           bi_impl P Q ι := P ι -> Q ι;
           bi_forall A f ι := forall a, f a ι;
           bi_exist A f ι := exists a, f a ι;
           bi_sep := sepₚ;
           bi_wand := wandₚ;
           bi_persistently := persistently;
           bi_later := later;
        |}.
      all: abstract firstorder.
    Defined.

    #[export] Instance persistent_pred {w} {P : Pred w} :
      derived_connectives.Persistent P.
    Proof. constructor. intros ι HP. constructor. exact HP. Qed.

    #[export] Instance affine_pred {w} {P : Pred w} :
      derived_connectives.Affine P.
    Proof. constructor. intros ι HP. constructor. Qed.

  End proofmode.

  Module Import notations.

    Import iris.bi.interface.
    Import iris.bi.derived_connectives.

    Notation "P ⊣⊢ₚ Q" :=
      (@equiv (bi_car (@bi_pred _)) (@pred_equiv _) P%P Q%P)
        (at level 95).
    Notation "(⊣⊢ₚ)" :=
      (@equiv (bi_car (@bi_pred _)) (@pred_equiv _))
        (only parsing).

    Notation "P ⊢ₚ Q" := (@bi_entails (@bi_pred _) P%P Q%P) (at level 95).
    Notation "(⊢ₚ)" := (@bi_entails (@bi_pred _)) (only parsing).

    Notation "⊤ₚ" := (@bi_pure (@bi_pred _) True) : pred_scope.
    Notation "⊥ₚ" := (@bi_pure (@bi_pred _) False) : pred_scope.
    Notation "P <->ₚ Q" := (@bi_iff (@bi_pred _) P%P Q%P) (at level 94) : pred_scope.
    Notation "P ->ₚ Q"  := (@bi_impl (@bi_pred _) P%P Q%P) (at level 94, right associativity) : pred_scope.
    Notation "P /\ₚ Q"  := (@bi_and (@bi_pred _) P%P Q%P) (at level 80, right associativity) : pred_scope.
    Notation "P \/ₚ Q"  := (@bi_or (@bi_pred _) P%P Q%P) (at level 85, right associativity) : pred_scope.

    Infix "=ₚ" := eqₚ (at level 70, no associativity) : pred_scope.

    Notation "∀ₚ x .. y , P" :=
      (@bi_forall (@bi_pred _) _ (fun x => .. (@bi_forall (@bi_pred _) _ (fun y => P%P)) ..))
      (at level 200, x binder, y binder, right associativity,
        format "'[ ' '[ ' ∀ₚ  x .. y ']' ,  '/' P ']'") : pred_scope.
    Notation "∃ₚ x .. y , P" :=
      (@bi_exist (@bi_pred _) _ (fun x => .. (@bi_exist (@bi_pred _) _ (fun y => P%P)) ..))
      (at level 200, x binder, y binder, right associativity,
        format "'[ ' '[ ' ∃ₚ  x .. y ']' ,  '/' P ']'") : pred_scope.

    Notation "G |--ₚ E ; T ~> EE" :=
      (TPB G E T EE) (at level 70, no associativity) : pred_scope.

  End notations.

  Lemma bientails_unfold [w] (P Q : Pred w) :
    (P ⊣⊢ₚ Q) <-> forall ι, P ι <-> Q ι.
  Proof. firstorder. Qed.
  Lemma entails_unfold [w] (P Q : Pred w) :
    (P ⊢ₚ Q) <-> forall ι, P ι -> Q ι.
  Proof. firstorder. Qed.
  Lemma sep_unfold w (P Q : Pred w) :
    ∀ ι, interface.bi_sep P Q ι ↔ (P ι /\ Q ι).
  Proof. firstorder. Qed.
  Lemma wand_unfold w (P Q : Pred w) :
    ∀ ι, interface.bi_wand P Q ι ↔ (P ι → Q ι).
  Proof. firstorder. Qed.
  Lemma intuitionistically_unfold w (P : Pred w) :
    ∀ ι, @derived_connectives.bi_intuitionistically _ P ι <-> P ι.
  Proof. firstorder. Qed.

  Create HintDb punfold.
  #[export] Hint Rewrite bientails_unfold entails_unfold sep_unfold wand_unfold
    intuitionistically_unfold
    (@inst_persist OEnv Env _ _ _)
    (@inst_persist OExp Exp _ _ _)
    (@inst_persist OTy Ty _ _ _)
    (@inst_lift OEnv Env _ _ _)
    (@inst_lift OExp Exp _ _ _)
    (@inst_lift OTy Ty _ _ _)
    (@inst_thin Par _ Par.lk_thin_par)
    @inst_refl @inst_trans @inst_insert
    @Open.inst_pure
    @oexp.inst_var @oexp.inst_true @oexp.inst_false @oexp.inst_ifte @oexp.inst_absu
    @oexp.inst_abst @oexp.inst_app : punfold.

  Ltac punfold_connectives :=
    change (@interface.bi_and (@bi_pred _) ?P ?Q ?ι) with (P ι /\ Q ι) in *;
    change (@interface.bi_or (@bi_pred _) ?P ?Q ?ι) with (P ι \/ Q ι) in *;
    change (@interface.bi_impl (@bi_pred _) ?P ?Q ?ι) with (P ι -> Q ι) in *;
    change (@derived_connectives.bi_iff (@bi_pred _) ?P ?Q ?ι) with (iff (P ι) (Q ι)) in *;
    change (@interface.bi_pure (@bi_pred _) ?P _) with P in *;
    change (@interface.bi_forall (@bi_pred _) ?A ?P) with (fun ι => forall a : A, P a ι) in *;
    change (@interface.bi_exist (@bi_pred _) ?A ?P) with (fun ι => exists a : A, P a ι) in *;
    change (@persist Pred persist_pred _ _ ?P _ ?θ ?ι) with (P (inst θ ι)) in *;
    try progress (cbn beta).

  Ltac pred_unfold :=
    repeat
      (punfold_connectives;
       try rewrite_db punfold; auto 1 with typeclass_instances;
       cbn [eqₚ TPB inst inst_ty inst_env] in *;
       (* repeat rewrite ?inst_persist, ?inst_lift, ?inst_refl, ?inst_trans, *)
       (*   ?inst_insert, ?oexp.inst_var, ?oexp.inst_true, ?oexp.inst_false, *)
       (*   ?oexp.inst_absu, ?oexp.inst_abst, ?oexp.inst_app, ?oexp.inst_ifte in *; *)
       try
         match goal with
         | |- forall ι : Assignment _, _ =>
             let ι := fresh "ι" in
             intro ι; pred_unfold;
             first [clear ι | revert ι]
         | |- @interface.bi_emp_valid (@bi_pred _) _ => constructor; intros ι _; cbn
         | |- @interface.bi_entails (@bi_pred _) _ _ => constructor; intros ι; cbn
         (* | H: context[@inst ?AT ?A ?I ?w ?x ?ι] |- _ => *)
         (*     is_var x; generalize (@inst AT A I w x ι); *)
         (*     clear x; intro x; subst *)
         | |- context[@inst ?AT ?A ?I ?w ?x ?ι] =>
             is_var x; generalize (@inst AT A I w x ι);
             clear x; intro x; subst
         end).

  Section Lemmas.

    Import iris.bi.interface.

    Create HintDb obligation.
    #[local] Hint Rewrite @inst_refl @inst_trans : obligation.

    #[local] Ltac obligation :=
      cbv [Proper flip respectful pointwise_relation forall_relation];
      repeat (autorewrite with obligation in *; cbn in *; intros; subst; pred_unfold);
      repeat
        (match goal with
         | H: _ ⊢ₚ _ |- _ => destruct H as [H]
         | H: _ ⊣⊢ₚ _ |- _ => destruct H as [H]
         | H: forall (H : ?A), _, a : ?A |- _ =>
           specialize (H a); autorewrite with obligation in H; cbn in H
         | |- (forall _ : ?A, _) <-> (forall _ : ?A, _) =>
             apply all_iff_morphism; intro; autorewrite with obligation; cbn
         | |- (exists _ : ?A, _) <-> (exists _ : ?A, _) =>
             apply ex_iff_morphism; intro; autorewrite with obligation; cbn
         (* | |- _ ⊣⊢ₚ _ => constructor; cbn; intros *)
         (* | |- _ ⊢ₚ _ => constructor; cbn; intros *)
         end);
      try easy; try (intuition; fail); try (intuition congruence; fail).
    #[local] Obligation Tactic := obligation.

    #[local] Hint Rewrite <- @tactics.forall_and_distr : obligation.

    #[export] Instance proper_persist_bientails {Θ w} :
      Proper ((⊣⊢ₚ) ==> forall_relation (fun _ => eq ==> (⊣⊢ₚ)))
      (@persist Pred persist_pred Θ w).
    Proof. obligation. Qed.

    Lemma split_bientails {w} (P Q : Pred w) :
      (P ⊣⊢ₚ Q) <-> (P ⊢ₚ Q) /\ (Q ⊢ₚ P).
    Proof. obligation. Qed.
    Lemma impl_and_adjoint {w} (P Q R : Pred w) : (P /\ₚ Q ⊢ₚ R) <-> (P ⊢ₚ Q ->ₚ R).
    Proof. obligation. Qed.
    Lemma and_comm {w} (P Q : Pred w) : P /\ₚ Q  ⊣⊢ₚ  Q /\ₚ P.
    Proof. obligation. Qed.
    Lemma and_assoc {w} (P Q R : Pred w) : (P /\ₚ Q) /\ₚ R  ⊣⊢ₚ  P /\ₚ (Q /\ₚ R).
    Proof. obligation. Qed.
    Lemma and_true_l {w} (P : Pred w) : ⊤ₚ /\ₚ P ⊣⊢ₚ P.
    Proof. obligation. Qed.
    Lemma and_true_r {w} (P : Pred w) : P /\ₚ ⊤ₚ ⊣⊢ₚ P.
    Proof. obligation. Qed.
    Lemma and_false_l {w} (P : Pred w) : ⊥ₚ /\ₚ P ⊣⊢ₚ ⊥ₚ.
    Proof. obligation. Qed.
    Lemma and_false_r {w} (P : Pred w) : P /\ₚ ⊥ₚ ⊣⊢ₚ ⊥ₚ.
    Proof. obligation. Qed.
    Lemma impl_true_l {w} (P : Pred w) : ⊤ₚ ->ₚ P ⊣⊢ₚ P.
    Proof. obligation. Qed.
    Lemma impl_true_r {w} (P : Pred w) : P ->ₚ ⊤ₚ ⊣⊢ₚ ⊤ₚ.
    Proof. obligation. Qed.
    Lemma impl_false_l {w} (P : Pred w) : ⊥ₚ ->ₚ P ⊣⊢ₚ ⊤ₚ.
    Proof. obligation. Qed.
    (* Lemma false_l {w} (P : Pred w) : ⊥ₚ ⊢ₚ P. *)
    (* Proof. obligation. Qed. *)
    (* Lemma true_r {w} (P : Pred w) : P ⊢ₚ ⊤ₚ. *)
    (* Proof. obligation. Qed. *)
    (* Lemma impl_forget {w} (P Q R : Pred w) : P ⊢ₚ R -> P ⊢ₚ (Q ->ₚ R). *)
    (* Proof. obligation. Qed. *)
    Lemma impl_and [w] (P Q R : Pred w) : ((P /\ₚ Q) ->ₚ R) ⊣⊢ₚ (P ->ₚ Q ->ₚ R).
    Proof. obligation. Qed.

    (* Lemma forall_l {I : Type} {w} (P : I -> Pred w) Q : *)
    (*   (exists x : I, P x ⊢ₚ Q) -> (∀ x : I, P x)%I ⊢ₚ Q. *)
    (* Proof. obligation. firstorder. Qed. *)
    (* Lemma forall_r {I : Type} {w} P (Q : I -> Pred w) : *)
    (*   (P ⊢ₚ (∀ₚ x : I, Q x)) <-> (forall x : I, P ⊢ₚ Q x). *)
    (* Proof. obligation. firstorder. Qed. *)

    Lemma exists_l {I : Type} {w} (P : I -> Pred w) (Q : Pred w) :
      (forall x : I, P x ⊢ₚ Q) -> (∃ₚ x : I, P x) ⊢ₚ Q.
    Proof. obligation; firstorder. Qed.
    Lemma exists_r {I : Type} {w} P (Q : I -> Pred w) :
      (exists x : I, P ⊢ₚ Q x) -> P ⊢ₚ (∃ₚ x : I, Q x).
    Proof. obligation; firstorder. Qed.
    #[global] Arguments exists_r {I w P Q} _.

    Lemma wand_is_impl [w] (P Q : Pred w) :
      (P -∗ Q)%I ⊣⊢ₚ (P ->ₚ Q).
    Proof. obligation. Qed.

    Lemma pApply {w} {P Q R : Pred w} :
      P ⊢ₚ Q -> Q ⊢ₚ R -> P ⊢ₚ R.
    Proof. now transitivity Q. Qed.

    Lemma pApply_r {w} {P Q R : Pred w} :
      Q ⊢ₚ R -> P ⊢ₚ Q -> P ⊢ₚ R.
    Proof. now transitivity Q. Qed.

    Section Eq.

      Context {T A} {instTA : Inst T A}.

      Lemma eqₚ_intro {w} (t : T w) : ⊢ (t =ₚ t)%P.
      Proof. obligation. Qed.

      Lemma eqₚ_refl {w} (t : T w) : t =ₚ t ⊣⊢ₚ ⊤ₚ.
      Proof. obligation. Qed.

      Lemma eqₚ_sym {w} (s t : T w) : s =ₚ t ⊣⊢ₚ t =ₚ s.
      Proof. obligation. Qed.

      Lemma eqₚ_trans {w} (s t u : T w) : s =ₚ t /\ₚ t =ₚ u ⊢ₚ s =ₚ u.
      Proof. obligation. Qed.

    End Eq.
    #[global] Arguments eqₚ_trans {T A _ w} s t u.

    Lemma peq_ty_noconfusion {w} (t1 t2 : OTy w) :
      t1 =ₚ t2 ⊣⊢ₚ
      match t1 , t2 with
      | oty.evar  _      , _                => t1 =ₚ t2
      | _                , oty.evar _       => t1 =ₚ t2
      | oty.bool         , oty.bool         => ⊤ₚ
      | oty.func t11 t12 , oty.func t21 t22 => t11 =ₚ t21 /\ₚ t12 =ₚ t22
      | _                , _                => ⊥ₚ
      end.
    Proof. destruct t1, t2; obligation. Qed.

    Lemma eq_pair
      {AT BT : OType} {A B : Type} {instA : Inst AT A} {instB : Inst BT B}
      [w] (a1 a2 : AT w) (b1 b2 : BT w) :
      (a1,b1) =ₚ (a2,b2) ⊣⊢ₚ ((a1 =ₚ a2) /\ₚ (b1 =ₚ b2)).
    Proof.
      pred_unfold. intros ι; cbn. split.
      - now injection 1.
      - intros []. now f_equal.
    Qed.

    Section Persist.

      Lemma persist_eq {T : OType} {persR : Persistence.Persistent T}
        {A : Type} {instTA : Inst T A} {instPersistTA : InstPersist T A}
        {Θ : SUB} {w0 w1} (θ : Θ w0 w1) (t1 t2 : T w0) :
        persist (t1 =ₚ t2) θ ⊣⊢ₚ persist t1 θ =ₚ persist t2 θ.
      Proof.
        pred_unfold. unfold persist, persist_pred. intros ι.
        now rewrite !inst_persist.
      Qed.

      Context {Θ : SUB}.

      (* We could define a PersistLaws instance for the Pred type, but that's
         requires functional extensionality. Instead, we provide similar
         lemmas that use bientailment instead of Leibniz equality and thus
         avoid functional extensionality. *)
      Lemma persist_pred_refl `{lkReflΘ : LkRefl Θ} [w] (P : Pred w) :
        persist P refl ⊣⊢ₚ P.
      Proof. obligation. Qed.
      Lemma persist_pred_trans `{lktransΘ : LkTrans Θ}
        {w0 w1 w2} (θ1 : Θ w0 w1) (θ2 : Θ w1 w2) (P : Pred w0) :
        persist P (θ1 ⊙ θ2) ⊣⊢ₚ persist (persist P θ1) θ2.
      Proof. obligation. Qed.
      Lemma persist_and {w0 w1} (θ : Θ w0 w1) (P Q : Pred w0) :
        persist (P /\ₚ Q) θ ⊣⊢ₚ persist P θ /\ₚ persist Q θ.
      Proof. obligation. Qed.
      Lemma persist_impl {w0 w1} (θ : Θ w0 w1) (P Q : Pred w0) :
        persist (P ->ₚ Q) θ ⊣⊢ₚ (persist P θ ->ₚ persist Q θ).
      Proof. obligation. Qed.
      Lemma persist_wand {w0 w1} (θ : Θ w0 w1) (P Q : Pred w0) :
        persist (interface.bi_wand P Q) θ ⊣⊢ₚ interface.bi_wand (persist P θ) (persist Q θ).
      Proof. obligation. Qed.
      Lemma persist_false {w0 w1} (θ : Θ w0 w1) :
        persist ⊥ₚ θ ⊣⊢ₚ ⊥ₚ.
      Proof. obligation. Qed.
      Lemma persist_true {w0 w1} (θ : Θ w0 w1) :
        persist ⊤ₚ θ ⊣⊢ₚ ⊤ₚ.
      Proof. obligation. Qed.
      Lemma persist_forall [A] [w0 w1] (θ : Θ w0 w1) (Q : A -> Pred w0) :
        persist (∀ₚ a : A, Q a) θ ⊣⊢ₚ (∀ₚ a : A, persist (Q a) θ).
      Proof. obligation. Qed.
      Lemma persist_exists [A] [w0 w1] (θ : Θ w0 w1) (Q : A -> Pred w0) :
        persist (∃ₚ a : A, Q a) θ ⊣⊢ₚ (∃ₚ a : A, persist (Q a) θ).
      Proof. obligation. Qed.

      Lemma persist_tpb {w0 w1} (θ : Θ w0 w1) G (e : Exp) (t : OTy w0) (ee : OExp w0) :
        persist (G |--ₚ e; t ~> ee) θ ⊣⊢ₚ
        persist G θ |--ₚ e; persist t θ ~> persist ee θ.
      Proof. obligation. Qed.

    End Persist.

  End Lemmas.

  Module Sub.
    Import (hints) Par.
    Section WithSubstitution.
      Context {Θ : SUB}.

      Definition wp {w0 w1} (θ : Θ w0 w1) (Q : Pred w1) : Pred w0 :=
        fun ι0 => exists (ι1 : Assignment w1), inst θ ι1 = ι0 /\ Q ι1.
      Definition wlp {w0 w1} (θ : Θ w0 w1) (Q : Pred w1) : Pred w0 :=
        fun ι0 => forall (ι1 : Assignment w1), inst θ ι1 = ι0 -> Q ι1.

      #[global] Arguments wp {_ _} _ _ ι0/.
      #[global] Arguments wlp {_ _} _ _ ι0/.

      #[export] Instance proper_wp_bientails {w0 w1} (θ : Θ w0 w1) :
        Proper ((⊣⊢ₚ) ==> (⊣⊢ₚ)) (wp θ).
      Proof. firstorder. Qed.

      #[export] Instance proper_wp_entails {w0 w1} (θ : Θ w0 w1) :
        Proper ((⊢ₚ) ==> (⊢ₚ)) (wp θ).
      Proof. firstorder. Qed.

      #[export] Instance proper_wlp_bientails {w0 w1} (θ : Θ w0 w1) :
        Proper ((⊣⊢ₚ) ==> (⊣⊢ₚ)) (wlp θ).
      Proof. firstorder. Qed.

      #[export] Instance proper_wlp_entails {w0 w1} (θ : Θ w0 w1) :
        Proper ((⊢ₚ) ==> (⊢ₚ)) (wlp θ).
      Proof. firstorder. Qed.

      Lemma wp_refl {reflΘ : Refl Θ} {lkreflΘ : LkRefl Θ}
        {w} (Q : Pred w) : wp refl Q ⊣⊢ₚ Q.
      Proof.
        unfold wp; pred_unfold. intros ι; split.
        - intros (ι' & Heq & HQ). now subst.
        - intros HQ. exists ι. easy.
      Qed.

      Lemma wp_trans {transR : Trans Θ} {lktransΘ : LkTrans Θ}
        {w0 w1 w2} (θ1 : Θ w0 w1) (θ2 : Θ w1 w2) Q :
        wp (θ1 ⊙ θ2) Q ⊣⊢ₚ wp θ1 (wp θ2 Q).
      Proof.
        unfold wp; pred_unfold. intros ι; split.
        - intros (ι2 & Heq & HQ). eauto.
        - intros (ι1 & Heq1 & ι2 & Heq2 & HQ). subst. eauto.
      Qed.

      Lemma wp_false {w0 w1} (θ : Θ w0 w1) :
        wp θ ⊥ₚ ⊣⊢ₚ ⊥ₚ.
      Proof. firstorder. Qed.

      Lemma and_wp_l {w0 w1} (θ : Θ w0 w1) P Q :
        wp θ P /\ₚ Q ⊣⊢ₚ wp θ (P /\ₚ persist Q θ).
      Proof.
        unfold wp; pred_unfold. split.
        - intros [(ι1 & <- & HP) HQ]. eauto.
        - intros (ι1 & <- & HP & HQ). eauto.
      Qed.

      Lemma and_wp_r {w0 w1} (θ : Θ w0 w1) (P : Pred w0) (Q : Pred w1) :
        P /\ₚ wp θ Q ⊣⊢ₚ wp θ (persist P θ /\ₚ Q).
      Proof. now rewrite and_comm, and_wp_l, and_comm. Qed.

      Lemma wp_thick {thickΘ : Thick Θ} {lkThickΘ : LkThick Θ}
        {w α} (αIn : world.In α w) (t : OTy (w - α)) (Q : Pred (w - α)) :
        wp (thick α t) Q ⊣⊢ₚ oty.evar αIn =ₚ persist t (thin (Θ := Par) α) /\ₚ persist Q (thin (Θ := Par) α).
      Proof.
        unfold wp; pred_unfold. intros ι. split.
        - intros (ι1 & Heq & HQ). subst.
          now rewrite inst_thick, env.remove_insert, env.lookup_insert.
        - intros [Heq HQ]. exists (env.remove α ι αIn).
          now rewrite inst_thick, <- Heq, env.insert_remove.
      Qed.

      Lemma wlp_refl {reflΘ : Refl Θ} {lkreflΘ : LkRefl Θ}
        {w} (Q : Pred w) : wlp refl Q ⊣⊢ₚ Q.
      Proof.
        unfold wlp; pred_unfold. intros ι. split.
        - intros HQ. auto.
        - intros HQ ? <-. auto.
      Qed.

      Lemma wlp_trans {transR : Trans Θ} {lktransΘ : LkTrans Θ}
        {w0 w1 w2} (θ1 : Θ w0 w1) (θ2 : Θ w1 w2) Q :
        wlp (θ1 ⊙ θ2) Q ⊣⊢ₚ wlp θ1 (wlp θ2 Q).
      Proof.
        unfold wlp; pred_unfold. intros ι. split.
        - intros HQ ι1 Heq1 ι2 Heq2. subst; auto.
        - intros HQ ι2 Heq. subst; eauto.
      Qed.

      Lemma wlp_true {w0 w1} (θ : Θ w0 w1) :
        wlp θ ⊤ₚ ⊣⊢ₚ ⊤ₚ.
      Proof. firstorder. Qed.

      Lemma wlp_and {w0 w1} (θ : Θ w0 w1) P Q :
        wlp θ P /\ₚ wlp θ Q ⊣⊢ₚ wlp θ (P /\ₚ Q).
      Proof. firstorder. Qed.

      Lemma wp_or {w0 w1} (θ : Θ w0 w1) P Q :
        wp θ P \/ₚ wp θ Q ⊣⊢ₚ wp θ (P \/ₚ Q).
      Proof. firstorder. Qed.

      Lemma wp_mono {w0 w1} (θ : Θ w0 w1) P Q:
        wlp θ (interface.bi_wand P Q) ⊢ₚ interface.bi_wand (wp θ P) (wp θ Q).
      Proof. firstorder. Qed.

      Lemma wlp_mono {w0 w1} (θ : Θ w0 w1) P Q :
        wlp θ (interface.bi_wand P Q) ⊢ₚ interface.bi_wand (wlp θ P) (wlp θ Q).
      Proof. firstorder. Qed.

      Lemma entails_wlp {w0 w1} (θ : Θ w0 w1) P Q :
        (persist P θ ⊢ₚ Q) <-> (P ⊢ₚ wlp θ Q).
      Proof.
        unfold wlp; pred_unfold. split; intros HPQ.
        - intros ι0 HP ι1 <-. revert HP. apply HPQ.
        - intros ι1 HP. now apply (HPQ (inst θ ι1)).
      Qed.

      Lemma entails_wp {w0 w1} (θ : Θ w0 w1) P Q :
        (P ⊢ₚ persist Q θ) <-> (wp θ P ⊢ₚ Q).
      Proof.
        unfold wp; pred_unfold. split; intros HPQ.
        - intros ι0 (ι1 & <- & HP). now apply HPQ.
        - intros ι1 HP. apply (HPQ (inst θ ι1)).
          exists ι1. split; auto.
      Qed.

      Lemma wp_impl {w0 w1} (θ1 : Θ w0 w1) (P : Pred _) (Q : Pred _) :
        (wp θ1 P ->ₚ Q) ⊣⊢ₚ wlp θ1 (P ->ₚ persist Q θ1).
      Proof.
        unfold wp, wlp; pred_unfold. intros ι0; split.
        - intros H ι1 <- HP. apply H. now exists ι1.
        - intros HPQ (ι1 & <- & HP). now apply HPQ.
      Qed.

      Lemma persist_wlp {w0 w1} {θ : Θ w0 w1} (P : Pred w1) :
        persist (wlp θ P) θ ⊢ₚ P.
      Proof. firstorder. Qed.

      Lemma persist_wp {w0 w1} {θ : Θ w0 w1} (P : Pred w1) :
        P ⊢ₚ persist (wp θ P) θ.
      Proof. firstorder. Qed.

      Lemma wlp_frame {w0 w1} (θ : Θ w0 w1) (P : Pred _) (Q : Pred _) :
        P ->ₚ wlp θ Q ⊣⊢ₚ wlp θ (persist P θ ->ₚ Q).
      Proof.
        unfold wlp; pred_unfold. intros ι; split.
        - intros H ι1 <- HP. now apply (H HP).
        - intros H HP ι1 <-. apply H; auto.
      Qed.

    End WithSubstitution.
    (* #[global] Opaque wp. *)
    (* #[global] Opaque wlp. *)

    (* Lemma proper_wp_step {Θ1 Θ2 : SUB} {stepΘ1 : Step Θ1} {stepΘ2 : Step Θ2} *)
    (*   {lkStepΘ1 : LkStep Θ1} {lkStepΘ2 : LkStep Θ2} *)
    (*   {w α} : *)
    (*   forall P Q : Pred (world.snoc w α), *)
    (*     P ⊣⊢ₚ Q -> wp (step (Θ := Θ1)) P ⊣⊢ₚ wp (step (Θ := Θ2)) Q. *)
    (* Proof. *)
    (*   intros P Q [PQ]. constructor. intros ι. apply base.exist_proper. *)
    (*   intros ι2. now rewrite !inst_step, PQ. *)
    (* Qed. *)

    Lemma intro_wp_step' {Θ} {stepΘ : Step Θ} {lkStepΘ : LkStep Θ}
      {w α} (P : Pred w) (Q : Pred (world.snoc w α)) (t : Ty) :
      (persist P step ⊢ₚ lift t =ₚ @oty.evar _ α world.in_zero ->ₚ Q) ->
      (P ⊢ₚ wp (step (Θ := Θ)) Q).
    Proof.
      pred_unfold. intros H ι HP. set (ι1 := env.snoc ι α t).
      exists ι1. specialize (H ι1). rewrite inst_step in *; cbn in *.
      intuition.
    Qed.

    (* Better for iris proof mode. *)
    Lemma intro_wp_step {Θ} {stepΘ : Step Θ} {lkStepΘ : LkStep Θ}
      t {w α} (Q : Pred (world.snoc w α)) :
      wlp step (lift t =ₚ oty.evar world.in_zero ->ₚ Q) ⊢ₚ wp (step (Θ := Θ)) Q.
    Proof. apply (intro_wp_step' t). now rewrite persist_wlp. Qed.

    Lemma wp_split  {Θ : SUB} [w0 w1] (θ : Θ w0 w1) P :
      wp θ ⊤ₚ /\ₚ wlp θ P ⊢ₚ wp θ P.
    Proof. now rewrite and_wp_l, persist_wlp, and_true_l. Qed.

    Lemma wp_hmap `{LkHMap Θ1 Θ2} [w0 w1] (θ : Θ1 w0 w1) P :
      wp (hmap θ) P ⊣⊢ₚ wp θ P.
    Proof.
      constructor. intros ι0; cbn. apply ex_iff_morphism.
      intro ι1. now rewrite inst_hmap.
    Qed.

    Lemma wlp_hmap `{LkHMap Θ1 Θ2} [w0 w1] (θ : Θ1 w0 w1) P :
      wlp (hmap θ) P ⊣⊢ₚ wlp θ P.
    Proof.
      constructor. intros ι0; cbn. apply all_iff_morphism.
      intro ι1. now rewrite inst_hmap.
    Qed.

  End Sub.

  Definition PBox {Θ} : ⊧ Box Θ Pred ⇢ Pred :=
    fun w Q => (∀ₚ w' (θ : Θ w w'), Sub.wlp θ (Q w' θ))%P.
  Notation "◼ Q" :=
    (PBox Q%B)
      (at level 9, right associativity, format "◼ Q").

  Section InstPred.
    Import iris.bi.derived_laws.
    Import iris.bi.interface.
    Import Persistence.
    (* A type class for things that can be interpreted as a predicate. *)
    Class InstPred (A : OType) :=
      instpred : ⊧ A ⇢ Pred.
    #[global] Arguments instpred {_ _ _}.

    (* #[export] Instance instpred_option {A} `{ipA : InstPred A} : *)
    (*   InstPred (Option A) := *)
    (*   fun w o => wp_option o instpred. *)
    #[export] Instance instpred_list {A} `{ipA : InstPred A} :
      InstPred (List A) :=
      fun w =>
        fix ip xs {struct xs} :=
        match xs with
        | nil       => ⊤ₚ
        | cons y ys => instpred y /\ₚ ip ys
        end%P.
    #[local] Instance instpred_prod_ty : InstPred (OTy * OTy) :=
      fun w '(t1,t2) => eqₚ t1 t2.
    #[export] Instance instpred_unit : InstPred Unit :=
      fun w _ => ⊤ₚ%P.
    #[global] Arguments instpred_unit [w] _ /.

    Lemma instpred_list_app {A} `{ipA : InstPred A} [w] (xs ys : List A w) :
      instpred (xs ++ ys) ⊣⊢ₚ instpred xs /\ₚ instpred ys.
    Proof.
      induction xs; cbn.
      - now rewrite and_true_l.
      - rewrite Pred.and_assoc. now apply bi.and_proper.
    Qed.

    Class InstPredPersist A {ipA : InstPred A} {persA : Persistent A} :=
      instpred_persist [Θ : SUB] {w0 w1} (θ : Θ w0 w1) (a : A w0) :
        instpred (persist a θ) ⊣⊢ₚ persist (instpred a) θ.
    #[global] Arguments InstPredPersist _ {_ _}.

    #[export] Instance instpred_persist_list `{InstPredPersist A} :
      InstPredPersist (List A).
    Proof.
      intros Θ w0 w1 θ xs. unfold persist, persistent_list.
      induction xs; cbn; [easy|]. now rewrite instpred_persist IHxs.
    Qed.

    #[local] Instance instpred_persist_prod_ty : InstPredPersist (OTy * OTy).
    Proof. intros Θ w0 w1 θ [τ1 τ2]; cbn. now rewrite persist_eq. Qed.

  End InstPred.

  Lemma pno_cycle {w} (t1 t2 : OTy w) (Hsub : oty.OTy_subterm t1 t2) :
    t1 =ₚ t2 ⊢ₚ ⊥ₚ.
  Proof.
    constructor. intros ι Heq. apply (inst_subterm ι) in Hsub.
    rewrite <- Heq in Hsub. now apply ty.no_cycle in Hsub.
  Qed.

  Lemma eqₚ_insert {w} (G1 G2 : OEnv w) (x : string) (t1 t2 : OTy w) :
    G1 =ₚ G2 /\ₚ t1 =ₚ t2 ⊢ₚ
    insert (M := OEnv w) x t1 G1 =ₚ insert (M := OEnv w) x t2 G2.
  Proof. pred_unfold. intros []. now f_equal. Qed.

  Lemma eq_func {w} (s1 s2 t1 t2 : OTy w) :
    oty.func s1 s2 =ₚ oty.func t1 t2 ⊣⊢ₚ (s1 =ₚ t1) /\ₚ (s2 =ₚ t2).
  Proof. now rewrite peq_ty_noconfusion. Qed.

  #[export] Instance params_tpb : Params (@TPB) 1 := {}.
  #[export] Instance params_ifte : Params (@oexp.ifte) 1 := {}.
  #[export] Instance params_eqₚ : Params (@eqₚ) 4 := {}.
  #[export] Instance params_persist : Params (@persist) 4 := {}.

  Section PBoxModality.
    Import iris.proofmode.tactics.

    #[export] Instance elimpbox `{LkRefl Θ} (p : bool)
      {w} (P : ◻Pred w) (Q : Pred w) :
      ElimModal True p true ◼P (P w refl) Q Q.
    Proof.
      intros _. unfold PBox. cbn. iIntros "[#H1 H2]". iApply "H2".
      destruct p; cbn; iSpecialize ("H1" $! w (refl (Refl := reflΘ)));
        now erewrite Sub.wlp_refl.
    Qed.

    Lemma persist_pbox `{LkTrans Θ} [w] (Q : ◻Pred w) [w1] (θ1 : Θ w w1) :
      (◼Q)[θ1] ⊢ₚ ◼(Q[θ1]).
    Proof.
      constructor; intros ι1 HQ w2 θ2 ι2 <-.
      apply HQ. now rewrite inst_trans.
    Qed.

  End PBoxModality.

  Section IntoPersist.

    Context {Θ : SUB}.

    Class IntoPersist `{Inst T A, Persistent T}
      [w0 w1] (θ : Θ w0 w1) (x : T w0) (y : T w1) : Prop :=
      into_persist : forall ι : Assignment w1, inst (persist x θ) ι = inst y ι.

    #[export] Instance into_persist_default `{Inst T A, Persistence.Persistent T}
      [w0 w1] (θ : Θ w0 w1) (t : T w0) : IntoPersist θ t (persist t θ) | 10.
    Proof. easy. Qed.

    (* #[export] Instance into_persist_persist `{LkTrans Θ, InstPersist T A} *)
    (*   [w0 w1 w2] (θ1 : Θ w0 w1) (θ2 : Θ w1 w2) (t : T w0) : *)
    (*   IntoPersist θ2 (persist t θ1) (persist t (trans θ1 θ2)) | 0. *)
    (* Proof. intros ι. now rewrite !inst_persist, inst_trans. Qed. *)

    #[export] Instance into_persist_lift {T A} {instTA : Inst T A} {liftTA : Lift T A}
      {persT : Persistent T} {instLiftTA : InstLift T A} {instPersTA : InstPersist T A}
      [w0 w1] (θ : Θ w0 w1) (a : A) :
      IntoPersist θ (lift a) (lift a) | 0.
    Proof. intros ι. now rewrite inst_persist, !inst_lift. Qed.

    #[export] Instance into_persist_insert
      [w0 w1] (θ : Θ w0 w1) (G0 : OEnv w0) x (τ0 : OTy w0) G1 τ1
      (HG : IntoPersist θ G0 G1) (Hτ : IntoPersist θ τ0 τ1) :
      IntoPersist θ (G0 ,, x ∷ τ0) (G1 ,, x ∷ τ1) | 0.
    Proof.
      intros ι1. specialize (HG ι1). specialize (Hτ ι1).
      change_no_check (@gmap.gmap string _ _ (OTy ?w)) with (OEnv w).
      rewrite persist_insert, !inst_insert. now f_equal.
    Qed.

  End IntoPersist.

  Section WlpModality.

    Import iris.proofmode.tactics.

    Context {Θ : SUB} [w0 w1] (θ : Θ w0 w1).

    Class IntoWlp (P : Pred w0) (Q : Pred w1) :=
      into_wlp : P ⊢ Sub.wlp θ Q.

    #[export] Instance into_wlp_default (P : Pred w0) :
      IntoWlp P (persist P θ) | 10.
    Proof. unfold IntoWlp. now apply Sub.entails_wlp. Qed.

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

    #[export] Instance into_wlp_pbox `{LkTrans Θ} (P : ◻Pred w0) :
      IntoWlp ◼P ◼(fun _ θ2 => P _ (θ ⊙ θ2)) | 0.
    Proof. unfold IntoWlp. iIntros "H !>". now rewrite persist_pbox. Qed.

    #[export] Instance into_wlp_tpb (G1 : OEnv w0) (e : Exp) (τ1 : OTy w0)
      (ee1 : OExp w0) G2 τ2 ee2 (HG : IntoPersist θ G1 G2)
      (Hτ : IntoPersist θ τ1 τ2) (Hee : IntoPersist θ ee1 ee2) :
      IntoWlp (TPB G1 e τ1 ee1) (TPB G2 e τ2 ee2) | 0.
    Proof.
      constructor. intros ι0 HT ι1 <-. pred_unfold.
      specialize (HG ι1). specialize (Hτ ι1). specialize (Hee ι1).
      rewrite !inst_persist in HG, Hτ, Hee. congruence.
    Qed.

    #[export] Instance into_wlp_eqp `{InstPersist T A}
      (x1 x2 : T w0) (y1 y2 : T w1) (Hxy1 : IntoPersist θ x1 y1) (Hxy2 :IntoPersist θ x2 y2) :
      IntoWlp (eqₚ x1 x2) (eqₚ y1 y2) | 0.
    Proof.
      constructor. pred_unfold. intros ι0 Heq ι1 ?Heq; cbn.
      specialize (Hxy1 ι1). specialize (Hxy2 ι1).
      rewrite !inst_persist in Hxy1, Hxy2. congruence.
    Qed.

    #[export] Instance into_wlp_wlp (P : Pred w1) :
      IntoWlp (Sub.wlp θ P) P | 0.
    Proof. unfold IntoWlp. reflexivity. Qed.

  End WlpModality.

  #[global] Arguments IntoWlp {Θ} [w0 w1] θ P Q.
  #[global] Arguments into_wlp {Θ} [w0 w1] θ P Q {_}.
  #[global] Hint Mode IntoWlp + + + + - - : typeclass_instances.

  Import (hints) Par.

  Create HintDb predsimpl.
  #[export] Hint Rewrite
    (@persist_eq OEnv _ _ _ _)
    (@persist_eq OTy _ _ _ _)
    (@persist_refl OEnv _ _)
    (@persist_refl OTy _ _)
    (@persist_trans OEnv _ _)
    (@persist_trans OTy _ _)
    @Sub.wlp_refl
    @Sub.wlp_trans
    @Sub.wlp_true
    @Sub.wp_false
    @Sub.wp_refl
    @Sub.wp_trans
    @and_false_l
    @and_false_r
    @and_true_l
    @and_true_r
    @eq_func
    @eqₚ_refl
    @impl_and
    @impl_false_l
    @impl_true_l
    @impl_true_r
    @lk_refl
    @lk_step
    @lk_trans
    @persist_and
    @persist_false
    @persist_pred_refl
    @persist_pred_trans
    @persist_tpb
    @persist_true
    @trans_refl_r
    : predsimpl.

  Ltac predsimpl :=
    repeat
      (try (progress cbn); unfold _4;
       change_no_check (@gmap.gmap string _ _ (OTy ?w)) with (OEnv w) in *;
       repeat
         match goal with
         | |- Sub.wp ?θ _ ⊣⊢ₚ Sub.wp ?θ _ =>
             apply Sub.proper_wp_bientails
         | |- Sub.wlp ?θ _ ⊣⊢ₚ Sub.wlp ?θ _ =>
             apply Sub.proper_wlp_bientails
         end;
       try easy;
       repeat rewrite_db predsimpl;
       auto 1 with typeclass_instances;
       repeat
         match goal with
         | |- context[@persist ?A ?I ?Θ ?w0 ?x ?w1 ?θ] =>
             is_var x; generalize (@persist A I Θ w0 x w1 θ); clear x; intros x;
             try (clear w0 θ)
         | |- context[@lk ?Θ (world.snoc ?w0 ?α) ?w1 ?θ ?α world.in_zero] =>
             is_var θ;
             generalize (@lk Θ (world.snoc w0 α) w1 θ α world.in_zero);
             clear θ w0; intros ?t
         end).

End Pred.
Export Pred (Pred).

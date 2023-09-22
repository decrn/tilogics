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

From Coq Require Import
  Classes.Morphisms
  Classes.Morphisms_Prop
  Classes.RelationClasses
  Relations.Relation_Definitions
  Strings.String.
From iris Require
  bi.derived_connectives
  bi.interface
  proofmode.tactics.
From Em Require Import
  Context
  Environment
  Prelude
  Stlc.Alloc
  Stlc.Instantiation
  Stlc.Persistence
  Stlc.Sem
  Stlc.Spec
  Stlc.Substitution
  Stlc.Worlds.

#[local] Set Implicit Arguments.
#[local] Arguments step : simpl never.
#[local] Arguments thick : simpl never.

Module Pred.
  #[local] Notation Ėxp := (Sem Exp).

  Declare Scope pred_scope.
  Delimit Scope pred_scope with P.

  Definition Pred (w : World) : Type :=
    Assignment w -> Prop.
  Bind Scope pred_scope with Pred.

  Section RewriteRelations.

    Import iris.bi.interface.

    Context {w : World}.

    Record bientails (P Q : Pred w) : Prop :=
      MkBientails
        { fromBientails : forall ι, P ι <-> Q ι }.
    Record entails (P Q : Pred w) : Prop :=
      MkEntails
        { fromEntails : forall ι, P ι -> Q ι }.

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

  Section Definitions.
    Import World.notations.

    Definition Falseₚ : ⊢ʷ Pred :=
      fun w _ => Logic.False.
    Definition Trueₚ : ⊢ʷ Pred :=
      fun w _ => Logic.True.
    Definition iffₚ : ⊢ʷ Pred -> Pred -> Pred :=
      fun w P Q ι => P ι <-> Q ι.
    Definition implₚ : ⊢ʷ Pred -> Pred -> Pred :=
      fun w P Q ι => P ι -> Q ι.
    Definition andₚ : ⊢ʷ Pred -> Pred -> Pred :=
      fun w P Q ι => P ι /\ Q ι.
    Definition orₚ : ⊢ʷ Pred -> Pred -> Pred :=
      fun w P Q ι => P ι \/ Q ι.
    #[global] Arguments andₚ {_} (_ _)%P _/.
    #[global] Arguments orₚ {_} (_ _)%P _/.
    #[global] Arguments iffₚ {_} (_ _)%P _/.
    #[global] Arguments implₚ {_} (_ _)%P _/.
    #[global] Arguments Trueₚ {_} _/.
    #[global] Arguments Falseₚ {_} _/.

    Definition eqₚ {T : TYPE} {A : Type} {instTA : Inst T A} :
      ⊢ʷ T -> T -> Pred :=
      fun w t1 t2 ι => inst t1 ι = inst t2 ι.
    #[global] Arguments eqₚ {T A _} [w] _ _ _/.

    (* #[universes(polymorphic)]  *)Definition Forall {I : Type} {w} :
      (I -> Pred w) -> Pred w := fun A ι => forall i : I, A i ι.
    (* #[universes(polymorphic)]  *)Definition Exists {I : Type} {w} :
      (I -> Pred w) -> Pred w := fun A ι => exists i : I, A i ι.
    #[global] Arguments Forall {I w} A%P ι/.
    #[global] Arguments Exists {I w} A%P ι/.

    Definition TPB : ⊢ʷ Ėnv -> Const Exp -> Ṫy -> Ėxp -> Pred :=
      fun w G e t ee ι => inst G ι |-- e ∷ inst t ι ~> inst ee ι.
    #[global] Arguments TPB [w] G e t ee ι/.

    #[export] Instance persist_pred : Persistent Pred :=
      fun Θ w1 P w2 θ ι2 => P (inst θ ι2).
    #[global] Arguments persist_pred Θ [w] _ [w1] _ _ /.

  End Definitions.

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

    Definition bimixin_pred {w : World} :
      BiMixin entails empₚ (fun P _ => P) andₚ orₚ implₚ
        (fun A => @Pred.Forall A w) (fun A => @Pred.Exists A w)
        sepₚ wandₚ persistently.
    Proof. firstorder. Qed.

    (* Iris defines [bi_later_mixin_id] for BI algebras without later. However,
       the identity function as later still causes some later-specific
       typeclasses to be picked. We just define our own trivial modality and
       mixin to avoid that. *)
    Variant later {w} (P : Pred w) (ι : Assignment w) : Prop :=
      MkLater : P ι -> later P ι.

    Definition bilatermixin_pred {w} :
      BiLaterMixin entails (fun P _ => P) orₚ implₚ
        (fun A => @Pred.Forall A w) (fun A => @Pred.Exists A w)
        sepₚ persistently later.
    Proof. firstorder. Qed.

    Canonical bi_pred {w : World} : bi :=
      {| bi_car            := Pred w;
         bi_bi_mixin       := bimixin_pred;
         bi_bi_later_mixin := bilatermixin_pred;
      |}.

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

    Infix "⊢ₚ" := (entails) (at level 95).

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

    Notation "'Fun' x => b" :=
      (fun w ζ x => b%P w ζ)
        (x binder, at level 100, only parsing) : pred_scope.

    Notation "G |--ₚ E ; T ~> EE" :=
      (TPB G E T EE) (at level 70, no associativity) : pred_scope.

  End notations.

  Ltac pred_unfold :=
    repeat
      (change (@interface.bi_and (@bi_pred ?w)) with (@andₚ w) in *;
       change (@interface.bi_or (@bi_pred ?w)) with (@orₚ w) in *;
       change (@interface.bi_impl (@bi_pred ?w)) with (@implₚ w) in *;
       change (@derived_connectives.bi_iff (@bi_pred ?w)) with (@iffₚ w) in *;
       change (@interface.bi_pure (@bi_pred ?w)) with (fun (P : Prop) (ι : Assignment w) => P) in *;
       change (@interface.bi_forall (@bi_pred ?w)) with (fun A => @Forall A w) in *;
       change (@interface.bi_exist (@bi_pred ?w)) with (fun A => @Exists A w) in *;
       change (@persist Pred persist_pred _ _ ?P _ ?θ ?ι) with (P (inst θ ι)) in *;
       cbn [andₚ orₚ implₚ iffₚ Forall Exists eqₚ TPB inst inst_ty inst_env] in *
      );
    rewrite ?inst_persist, ?inst_lift in *;
    repeat
      match goal with
      | H: context[@inst ?AT ?A ?I ?w ?x ?ι] |- _ =>
          is_var x; generalize dependent x; intro x;
          generalize (@inst AT A I w x ι);
          clear x; intro x; intros; subst
      | |- context[@inst ?AT ?A ?I ?w ?x ?ι] =>
          is_var x; generalize dependent x; intro x;
          generalize (@inst AT A I w x ι);
          clear x; intro x; intros; subst
      end.

  Section Lemmas.

    Import iris.bi.interface.
    Import stdpp.base.

    Create HintDb obligation.
    #[local] Hint Rewrite @inst_refl @inst_trans : obligation.

    #[local] Ltac obligation :=
      cbv [Proper flip respectful pointwise_relation forall_relation];
      repeat (autorewrite with obligation in *; cbn in *; intros; subst; pred_unfold);
      repeat
        (match goal with
         (* | H: _ ⊢ₚ _ |- _ => destruct H as [H] *)
         (* | H: _ ⊣⊢ₚ _ |- _ => destruct H as [H] *)
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

    Lemma entails_in [w] (P Q : Pred w) :
      (P ⊢ₚ Q) <-> forall ι, P ι -> Q ι.
    Proof. split; [intros []|]; obligation. Qed.
    Lemma equiv_in [w] (P Q : Pred w) :
      (P ⊣⊢ₚ Q) <-> forall ι, P ι <-> Q ι.
    Proof. split; [intros []|]; obligation. Qed.

    #[local] Hint Rewrite entails_in equiv_in : obligation.
    #[local] Hint Rewrite <- @Prelude.forall_and_compat : obligation.

    #[export,program] Instance proper_iff {w} :
      Proper ((⊣⊢ₚ) ==> (⊣⊢ₚ) ==> (⊣⊢ₚ)) (@iffₚ w).
    #[export,program] Instance proper_impl_bientails {w} :
      Proper ((⊣⊢ₚ) ==> (⊣⊢ₚ) ==> (⊣⊢ₚ)) (@implₚ w).
    #[export,program] Instance proper_impl_entails {w} :
      Proper (entails --> entails ==> entails) (@implₚ w).
    #[export,program] Instance proper_and_bientails {w} :
      Proper ((⊣⊢ₚ) ==> (⊣⊢ₚ) ==> (⊣⊢ₚ)) (@andₚ w).
    #[export,program] Instance proper_and_entails {w} :
      Proper (entails ==> entails ==> entails) (@andₚ w).
    #[export,program] Instance proper_or_bientails {w} :
      Proper ((⊣⊢ₚ) ==> (⊣⊢ₚ) ==> (⊣⊢ₚ)) (@orₚ w).
    #[export,program] Instance proper_or_entails {w} :
      Proper (entails ==> entails ==> entails) (@orₚ w).
    #[export,program] Instance proper_forall_bientails {I w} :
      Proper (pointwise_relation I (⊣⊢ₚ) ==> (⊣⊢ₚ)) (@Pred.Forall I w).
    #[export,program] Instance proper_exists_bientails {I w} :
      Proper (pointwise_relation I (⊣⊢ₚ) ==> (⊣⊢ₚ)) (@Pred.Exists I w).
    #[export,program] Instance proper_persist_bientails {Θ w} :
      Proper ((⊣⊢ₚ) ==> forall_relation (fun _ => eq ==> (⊣⊢ₚ)))
        (@persist Pred persist_pred Θ w).
    #[export,program] Instance proper_persist_entails {Θ w} :
      Proper (entails ==> forall_relation (fun _ => eq ==> entails))
        (@persist Pred persist_pred Θ w).
    #[export,program] Instance proper_persist_flip_entails {Θ w} :
      Proper (entails --> forall_relation (fun _ => eq ==> Basics.flip entails))
        (@persist Pred persist_pred Θ w).

    Lemma split_bientails {w} (P Q : Pred w) :
      (P ⊣⊢ₚ Q) <-> (P ⊢ₚ Q) /\ (Q ⊢ₚ P).
    Proof. obligation. Qed.
    Lemma and_left1 {w} {P Q R : Pred w} : P ⊢ₚ R -> P /\ₚ Q ⊢ₚ R.
    Proof. obligation. Qed.
    Lemma and_left2 {w} {P Q R : Pred w} : Q ⊢ₚ R -> P /\ₚ Q ⊢ₚ R.
    Proof. obligation. Qed.
    Lemma and_right {w} {P Q R : Pred w} : P ⊢ₚ Q -> P ⊢ₚ R -> P ⊢ₚ Q /\ₚ R.
    Proof. obligation. Qed.
    Lemma or_right1 {w} {P Q : Pred w} : P ⊢ₚ P \/ₚ Q.
    Proof. obligation. Qed.
    Lemma or_right2 {w} {P Q : Pred w} : Q ⊢ₚ P \/ₚ Q.
    Proof. obligation. Qed.
    Lemma or_left {w} {P Q R : Pred w} : P ⊢ₚ R -> Q ⊢ₚ R -> P \/ₚ Q ⊢ₚ R.
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
    Lemma false_l {w} (P : Pred w) : ⊥ₚ ⊢ₚ P.
    Proof. obligation. Qed.
    Lemma true_r {w} (P : Pred w) : P ⊢ₚ ⊤ₚ.
    Proof. obligation. Qed.
    Lemma impl_forget {w} (P Q R : Pred w) : P ⊢ₚ R -> P ⊢ₚ (Q ->ₚ R).
    Proof. obligation. Qed.
    Lemma impl_and [w] (P Q R : Pred w) : ((P /\ₚ Q) ->ₚ R) ⊣⊢ₚ (P ->ₚ Q ->ₚ R).
    Proof. obligation. Qed.

    Lemma forall_l {I : Type} {w} (P : I -> Pred w) Q :
      (exists x : I, P x ⊢ₚ Q) -> (∀ x : I, P x)%I ⊢ₚ Q.
    Proof. obligation. firstorder. Qed.
    Lemma forall_r {I : Type} {w} P (Q : I -> Pred w) :
      (P ⊢ₚ (∀ₚ x : I, Q x)) <-> (forall x : I, P ⊢ₚ Q x).
    Proof. obligation. firstorder. Qed.

    Lemma exists_l {I : Type} {w} (P : I -> Pred w) (Q : Pred w) :
      (forall x : I, P x ⊢ₚ Q) -> (∃ₚ x : I, P x) ⊢ₚ Q.
    Proof. obligation. firstorder. Qed.
    Lemma exists_r {I : Type} {w} P (Q : I -> Pred w) :
      (exists x : I, P ⊢ₚ Q x) -> P ⊢ₚ (∃ₚ x : I, Q x).
    Proof. obligation. firstorder. Qed.
    #[global] Arguments exists_r {I w P Q} _.

    Lemma wand_is_impl [w] (P Q : Pred w) :
      (P -∗ Q)%I ⊣⊢ₚ (P ->ₚ Q).
    Proof. firstorder. Qed.

    Lemma pApply {w} {P Q R : Pred w} :
      P ⊢ₚ Q -> Q ⊢ₚ R -> P ⊢ₚ R.
    Proof. now transitivity Q. Qed.

    Lemma pApply_r {w} {P Q R : Pred w} :
      Q ⊢ₚ R -> P ⊢ₚ Q -> P ⊢ₚ R.
    Proof. now transitivity Q. Qed.

    Section Eq.

      Context {T A} {instTA : Inst T A}.

      Lemma eqₚ_refl {w} (t : T w) : t =ₚ t ⊣⊢ₚ ⊤ₚ.
      Proof. obligation. Qed.

      Lemma eqₚ_sym {w} (s t : T w) : s =ₚ t ⊣⊢ₚ t =ₚ s.
      Proof. obligation. Qed.

      Lemma eqₚ_trans {w} (s t u : T w) : s =ₚ t /\ₚ t =ₚ u ⊢ₚ s =ₚ u.
      Proof. obligation. Qed.

      Lemma eqₚ_subst {w} (s t : T w) Q : s =ₚ t ⊢ₚ Q s ->ₚ Q t.
      Proof. Admitted.

    End Eq.
    #[global] Arguments eqₚ_trans {T A _ w} s t u.

    Lemma peq_ty_noconfusion {w} (t1 t2 : Ṫy w) :
      t1 =ₚ t2 ⊣⊢ₚ
            match t1 , t2 with
            | ṫy.var  _       , _               => t1 =ₚ t2
            | _               , ṫy.var _        => t1 =ₚ t2
            | ṫy.bool         , ṫy.bool         => ⊤ₚ
            | ṫy.func t11 t12 , ṫy.func t21 t22 => t11 =ₚ t21 /\ₚ t12 =ₚ t22
            | _               , _               => ⊥ₚ
            end.
    Proof. destruct t1, t2; obligation. Qed.

    Lemma eq_pair
      {AT BT : TYPE} {A B : Type} {instA : Inst AT A} {instB : Inst BT B}
      [w] (a1 a2 : AT w) (b1 b2 : BT w) :
      (a1,b1) =ₚ (a2,b2) ⊣⊢ₚ ((a1 =ₚ a2) /\ₚ (b1 =ₚ b2)).
    Proof.
      constructor. pred_unfold. intros ι; cbn. split.
      - now injection 1.
      - intros []. now f_equal.
    Qed.

    Section Persist.

      Import World.notations.

      Context {Θ : ACC}.

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
        persist (wandₚ P Q) θ ⊣⊢ₚ wandₚ (persist P θ) (persist Q θ).
      Proof. now rewrite ?wand_is_impl persist_impl. Qed.
      Lemma persist_false {w0 w1} (θ : Θ w0 w1) :
        persist ⊥ₚ θ ⊣⊢ₚ ⊥ₚ.
      Proof. obligation. Qed.
      Lemma persist_true {w0 w1} (θ : Θ w0 w1) :
        persist ⊤ₚ θ ⊣⊢ₚ ⊤ₚ.
      Proof. obligation. Qed.
      Lemma persist_eq {T : TYPE} {persR : Persistence.Persistent T}
        {A : Type} {instTA : Inst T A} {instPersistTA : InstPersist T A}
        {w0 w1} (θ : Θ w0 w1) (t1 t2 : T w0) :
        persist (t1 =ₚ t2) θ ⊣⊢ₚ persist t1 θ =ₚ persist t2 θ.
      Proof.
        constructor. unfold eqₚ, persist, persist_pred. intros ι.
        now rewrite !inst_persist.
      Qed.

      Lemma persist_forall [A] [w0 w1] (θ : Θ w0 w1) (Q : A -> Pred w0) :
        persist (∀ₚ a : A, Q a) θ ⊣⊢ₚ (∀ₚ a : A, persist (Q a) θ).
      Proof. obligation. Qed.
      Lemma persist_exists [A] [w0 w1] (θ : Θ w0 w1) (Q : A -> Pred w0) :
        persist (∃ₚ a : A, Q a) θ ⊣⊢ₚ (∃ₚ a : A, persist (Q a) θ).
      Proof. obligation. Qed.

      Lemma persist_tpb {w0 w1} (θ : Θ w0 w1) G (e : Exp) (t : Ṫy w0) (ee : Ėxp w0) :
        persist (G |--ₚ e; t ~> ee) θ ⊣⊢ₚ
        persist G θ |--ₚ e; persist t θ ~> persist ee θ.
      Proof. obligation. Qed.

    End Persist.

  End Lemmas.

  Section InstPred.
    Import World.notations.
    (* A type class for things that can be interpreted as a predicate. *)
    Class InstPred (A : TYPE) :=
      instpred : ⊢ʷ A -> Pred.

    #[export] Instance instpred_option {A} `{ipA : InstPred A} :
      InstPred (Option A) :=
      fun w o => match o with Some p => instpred p | None => Falseₚ end.
    #[export] Instance instpred_list {A} `{ipA : InstPred A} :
      InstPred (List A) :=
      fun w =>
        fix ip xs {struct xs} :=
        match xs with
        | nil       => Trueₚ
        | cons y ys => andₚ (instpred y) (ip ys)
        end.
    #[local] Instance instpred_prod_ty : InstPred (Ṫy * Ṫy) :=
      fun w '(t1,t2) => eqₚ t1 t2.
  End InstPred.

  Module Acc.
    Import World.notations.
    Import (hints) Sub.
    Section WithAccessibilityRelation.
      Context {Θ : ACC}.

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
        Proper (entails ==> entails) (wp θ).
      Proof. firstorder. Qed.

      #[export] Instance proper_wlp_bientails {w0 w1} (θ : Θ w0 w1) :
        Proper ((⊣⊢ₚ) ==> (⊣⊢ₚ)) (wlp θ).
      Proof. firstorder. Qed.

      #[export] Instance proper_wlp_entails {w0 w1} (θ : Θ w0 w1) :
        Proper (entails ==> entails) (wlp θ).
      Proof. firstorder. Qed.

      Lemma wp_refl {reflΘ : Refl Θ} {lkreflΘ : LkRefl Θ}
        {w} (Q : Pred w) : wp refl Q ⊣⊢ₚ Q.
      Proof.
        constructor. split; cbn.
        - intros (ι' & Heq & HQ). rewrite inst_refl in Heq. now subst.
        - intros HQ. exists ι. split. now rewrite inst_refl. easy.
      Qed.

      Lemma wp_trans {transR : Trans Θ} {lktransΘ : LkTrans Θ}
        {w0 w1 w2} (θ1 : Θ w0 w1) (θ2 : Θ w1 w2) Q :
        wp (θ1 ⊙ θ2) Q ⊣⊢ₚ wp θ1 (wp θ2 Q).
      Proof.
        constructor. split; cbn.
        - intros (ι2 & Heq & HQ). rewrite inst_trans in Heq.
          exists (inst θ2 ι2). split. easy. now exists ι2.
        - intros (ι1 & Heq1 & ι2 & Heq2 & HQ). exists ι2.
          split; [|easy]. rewrite inst_trans. congruence.
      Qed.

      Lemma wp_false {w0 w1} (θ : Θ w0 w1) :
        wp θ ⊥ₚ ⊣⊢ₚ ⊥ₚ.
      Proof. constructor. firstorder. Qed.

      (* Lemma wp_step_thick {stepθ : Step Θ} {w} {x} (Q : Pred (ctx.snoc w x)): *)
      (*   wp (w0:=w) step Q ⊣⊢ₚ (∃ₚ t : Ṫy w, persist Q (thick (αIn := ctx.in_zero) x t)). *)
      (* Proof. *)
      (*   constructor. intros ι; pred_unfold; cbn - [inst thick]. *)
      (*   split. *)
      (*   - intros (ι' & <- & HQ). destruct (env.view ι') as [ι t]. *)
      (*     rewrite inst_step_snoc. exists (lift t _). *)
      (*     rewrite (inst_thick ctx.in_zero (lift t w) ι). *)
      (*     now rewrite inst_lift. *)
      (*   - cbn - [inst thick]. intros (t & HQ). *)
      (*     exists (env.snoc ι _ (inst t ι)). *)
      (*     rewrite inst_step_snoc. *)
      (*     now rewrite (inst_thick ctx.in_zero t ι) in HQ. *)
      (* Qed. *)

      Ltac clean_inst :=
        repeat change_no_check (@inst (Sub ?w0) _ _ ?w1 ?θ1 ?ι1) with
          (@inst (acc Sub w0) _ _ w1 θ1 ι1) in *;
        repeat change_no_check (@inst (Alloc ?w0) _ _ ?w1 ?θ1 ?ι1) with
          (@inst (acc alloc.acc_alloc w0) _ _ w1 θ1 ι1).

      Lemma and_wp_l {w0 w1} (θ : Θ w0 w1) P Q :
        wp θ P /\ₚ Q ⊣⊢ₚ wp θ (P /\ₚ persist Q θ).
      Proof.
        constructor. split; cbn.
        - intros [(ι1 & <- & HP) HQ]. now exists ι1.
        - intros (ι1 & <- & HP & HQ). split; [|easy]. now exists ι1.
      Qed.

      Lemma and_wp_r {w0 w1} (θ : Θ w0 w1) P Q :
        P /\ₚ wp θ Q ⊣⊢ₚ wp θ (persist P θ /\ₚ Q).
      Proof. now rewrite and_comm, and_wp_l, and_comm. Qed.

      Lemma wp_thick {thickΘ : Thick Θ}
        {w α} (αIn : ctx.In α w) (t : Ṫy (ctx.remove αIn)) (Q : Pred (ctx.remove αIn)) :
        wp (thick α t) Q ⊣⊢ₚ ṫy.var αIn =ₚ persist t (thin (Θ := Sub) α) /\ₚ persist Q (thin (Θ := Sub) α).
      Proof.
        constructor. intros ι; pred_unfold; cbn. rewrite inst_thin.
        split.
        - intros (ι1 & Heq & HQ). subst.
          now rewrite inst_thick, env.remove_insert, env.lookup_insert.
        - intros [Heq HQ]. exists (env.remove α ι αIn).
          rewrite inst_thick. rewrite <- Heq. now rewrite env.insert_remove.
      Qed.

      Lemma wlp_refl {reflΘ : Refl Θ} {lkreflΘ : LkRefl Θ}
        {w} (Q : Pred w) : wlp refl Q ⊣⊢ₚ Q.
      Proof.
        constructor. split; cbn.
        - intros HQ. apply HQ. now rewrite inst_refl.
        - intros HQ ? <-. now rewrite inst_refl in HQ.
      Qed.

      Lemma wlp_trans {transR : Trans Θ} {lktransΘ : LkTrans Θ}
        {w0 w1 w2} (θ1 : Θ w0 w1) (θ2 : Θ w1 w2) Q :
        wlp (θ1 ⊙ θ2) Q ⊣⊢ₚ wlp θ1 (wlp θ2 Q).
      Proof.
        constructor. split; cbn.
        - intros HQ ι1 Heq1 ι2 Heq2. apply HQ.
          subst. now rewrite inst_trans.
        - intros HQ ι2 Heq. rewrite inst_trans in Heq.
          now apply (HQ (inst θ2 ι2)).
      Qed.

      Lemma wlp_true {w0 w1} (θ : Θ w0 w1) :
        wlp θ Trueₚ ⊣⊢ₚ Trueₚ.
      Proof. constructor. firstorder. Qed.

      Lemma wlp_and {w0 w1} (θ : Θ w0 w1) P Q :
        wlp θ P /\ₚ wlp θ Q ⊣⊢ₚ wlp θ (P /\ₚ Q).
      Proof. constructor. firstorder. Qed.

      Lemma wp_or {w0 w1} (θ : Θ w0 w1) P Q :
        wp θ P \/ₚ wp θ Q ⊣⊢ₚ wp θ (P \/ₚ Q).
      Proof. constructor. firstorder. Qed.

      Lemma wp_mono {w0 w1} (θ : Θ w0 w1) P Q:
        wlp θ (P ->ₚ Q) ⊢ₚ (wp θ P ->ₚ wp θ Q).
      Proof. constructor. firstorder. Qed.

      Lemma wlp_mono {w0 w1} (θ : Θ w0 w1) P Q :
        wlp θ (P ->ₚ Q) ⊢ₚ wlp θ P ->ₚ wlp θ Q.
      Proof. constructor. firstorder. Qed.

      Lemma entails_wlp {w0 w1} (θ : Θ w0 w1) P Q :
        (persist P θ ⊢ₚ Q) <-> (P ⊢ₚ wlp θ Q).
      Proof.
        split; intros [HPQ]; constructor.
        - intros ι0 HP ι1 <-. revert HP. apply HPQ.
        - intros ι1 HP. now apply (HPQ (inst θ ι1)).
      Qed.

      Lemma entails_wp {w0 w1} (θ : Θ w0 w1) P Q :
        (P ⊢ₚ persist Q θ) <-> (wp θ P ⊢ₚ Q).
      Proof.
        split; intros [HPQ]; constructor.
        - intros ι0 (ι1 & <- & HP). now apply HPQ.
        - intros ι1 HP. apply (HPQ (inst θ ι1)).
          exists ι1. split; auto.
      Qed.

      (* Lemma wlp_thick {thickR : Thick Θ} *)
      (*   {w x} (xIn : ctx.In x w) (t : Ty (ctx.remove xIn)) (Q : Pred (ctx.remove xIn)) : *)
      (*   wlp (thick x t) Q ⊣⊢ₚ Ty_hole xIn =ₚ thin xIn t ->ₚ persist Q (Sub.thin xIn). *)
      (* Proof. *)
      (*   constructor. intros ι; pred_unfold; cbn. *)
      (*   rewrite Sub.subst_thin, inst_persist, Sub.inst_thin. *)
      (*   split; intros HQ. *)
      (*   - specialize (HQ (env.remove x ι xIn)). intros Heq. *)
      (*     rewrite inst_thick in HQ. *)
      (*     rewrite <- Heq in HQ. *)
      (*     rewrite env.insert_remove in HQ. auto. *)
      (*   - intros ι1 Heq. subst. *)
      (*     rewrite inst_thick, env.remove_insert, env.lookup_insert in HQ. *)
      (*     now apply HQ. *)
      (* Qed. *)

      Lemma wlp_step_thick {stepR : Step Θ} {w} {α} (Q : Pred (ctx.snoc w α)):
        wlp (w0:=w) step Q ⊣⊢ₚ (∀ₚ t : Ṫy w, persist Q (thick (αIn := ctx.in_zero) α t)).
      Proof.
        constructor. intros ι; pred_unfold; cbn - [inst thick].
        split.
        - intros HQ t. apply HQ.
          rewrite (inst_thick ctx.in_zero t ι). cbn.
          now rewrite inst_step_snoc.
        - cbn - [inst thick]. intros HQ ι' <-.
          destruct (env.view ι') as [ι t].
          specialize (HQ (lift t _)).
          rewrite inst_step_snoc in HQ.
          rewrite (inst_thick ctx.in_zero (lift t w) ι) in HQ.
          now rewrite inst_lift in HQ.
      Qed.

      Lemma wp_impl {w0 w1} (θ1 : Θ w0 w1) (P : Pred _) (Q : Pred _) :
        (wp θ1 P ->ₚ Q) ⊣⊢ₚ wlp θ1 (P ->ₚ persist Q θ1).
      Proof.
        constructor. intros ι; unfold wp, wlp. pred_unfold.
        split.
        - intros H ι1 <- HP. apply H. now exists ι1.
        - intros HPQ (ι1 & <- & HP). now apply HPQ.
      Qed.

      Lemma persist_wlp {w0 w1} {θ : Θ w0 w1} (P : Pred w1) :
        persist (wlp θ P) θ ⊢ₚ P.
      Proof. constructor. intros ι H. now apply H. Qed.

      Lemma wlp_frame {w0 w1} (θ : Θ w0 w1) (P : Pred _) (Q : Pred _) :
        P ->ₚ wlp θ Q ⊣⊢ₚ wlp θ (persist P θ ->ₚ Q).
      Proof.
        constructor. intros ι.
        split; cbv [wlp interface.bi_impl bi_pred implₚ].
        - intros H ι1 <- HP. now apply (H HP).
        - intros H HP ι1 <-. apply H; auto.
      Qed.

    End WithAccessibilityRelation.
    (* #[global] Opaque wp. *)
    (* #[global] Opaque wlp. *)

    Lemma proper_wp_step {Θ1 Θ2 : ACC} {stepΘ1 : Step Θ1} {stepΘ2 : Step Θ2} {w α} :
      forall P Q : Pred (ctx.snoc w α),
        P ⊣⊢ₚ Q -> wp (step (Θ := Θ1)) P ⊣⊢ₚ wp (step (Θ := Θ2)) Q.
    Proof.
      intros P Q [PQ]. constructor. intros ι. cbn. apply base.exist_proper.
      intros ι2. now rewrite !inst_step, PQ.
    Qed.

    Lemma wp_incl {Θ} {reflΘ : Refl Θ} {transΘ : Trans Θ} {stepΘ : Step Θ}
      {lkReflΘ : LkRefl Θ} {lkTransΘ : LkTrans Θ}
      {w1 w2} (θ : alloc.acc_alloc w1 w2) :
      forall Q, wp θ Q ⊣⊢ₚ wp (alloc.incl (Θ := Θ) θ) Q.
    Proof.
      intros Q. induction θ; cbn.
      - change alloc.refl with (refl (Θ := alloc.acc_alloc) (w := w)).
        now rewrite !wp_refl.
      - change (alloc.fresh ?r) with (step (Θ := alloc.acc_alloc) ⊙ r).
        rewrite !wp_trans. apply proper_wp_step, IHθ.
    Qed.

    Lemma intro_wp_step {Θ} {stepΘ : Step Θ} {w α} (Q : Pred (ctx.snoc w α)) :
      wp (step (Θ := Θ)) Q ⊣⊢ₚ (∃ₚ t : Ṫy _, wlp step (persist t step =ₚ ṫy.var ctx.in_zero ->ₚ Q)).
    Proof.
      constructor. intros ι. pred_unfold. unfold wlp, wp, implₚ, eqₚ. cbn.
      split.
      - intros (ι' & Heq & HQ). subst. destruct (env.view ι').
        exists (lift v _). intros ι' Heq1 Heq2.
        rewrite inst_step_snoc in Heq1. subst.
        rewrite inst_persist, inst_lift in Heq2. subst.
        destruct (env.view ι'). rewrite inst_step_snoc in HQ.
        now cbn in HQ.
      - intros (t & H). exists (env.snoc ι α (inst t ι)).
        rewrite inst_step_snoc. split; [easy|]. apply H.
        + now rewrite inst_step_snoc.
        + now rewrite inst_persist, inst_step_snoc.
    Qed.

  End Acc.

  Lemma pno_cycle {w} (t1 t2 : Ṫy w) (Hsub : ṫy.Ṫy_subterm t1 t2) :
    t1 =ₚ t2 ⊢ₚ ⊥ₚ.
  Proof.
    constructor. intros ι Heq.
    apply (inst_subterm ι) in Hsub. cbn in Hsub.
    rewrite <- Heq in Hsub. now apply ty.no_cycle in Hsub.
  Qed.


  (* A predicate-based induction scheme for the typing relation. *)
  Section InductionScheme.

    Import iris.bi.interface.
    Import World.notations.
    Import Pred.notations.
    Import Pred.proofmode.

    Open Scope pred_scope.

    Context (P : ⊢ʷ Ėnv -> Const Exp -> Ṫy -> Ėxp -> Pred).
    Context
      {pvar : forall w,
        ⊢ ∀ (G : Ėnv w) x t e',
            lookup x G =ₚ Some t →
            e' =ₚ Sem.pure (exp.var x) →
            P G (exp.var x) t e' }
      {ptrue : forall w,
        ⊢ ∀ G : Ėnv w, ∀ t : Ṫy w, ∀ e' : Ėxp w,
            t =ₚ ṫy.bool →
            e' =ₚ (Sem.pure exp.true) →
            P G exp.true t e' }
      {pfalse : forall w,
        ⊢ ∀ G : Ėnv w, ∀ t : Ṫy w, ∀ e' : Ėxp w,
            t =ₚ ṫy.bool →
            e' =ₚ (Sem.pure exp.false) →
            P G exp.false t e' }
      {pif : forall w,
        ⊢ ∀ (G : Ėnv w) (e1 e2 e3 : Exp) (e' e1' e2' e3' : Ėxp w) t,
            (G |--ₚ e1; ṫy.bool ~> e1') →
            (G |--ₚ e2; t ~> e2') →
            (G |--ₚ e3; t ~> e3') →
            P G e1 ṫy.bool e1' →
            P G e2 t e2' →
            P G e3 t e3' →
            e' =ₚ (fun ι0 => exp.ifte (e1' ι0) (e2' ι0) (e3' ι0)) →
            P G (exp.ifte e1 e2 e3) t e' }
      {pabsu : forall w,
        ⊢ ∀ (G : Ėnv w) x t1 t2 t e1 e1' e',
            (G ,, x∷t1 |--ₚ e1; t2 ~> e1') →
            P (G ,, x∷t1) e1 t2 e1' →
            t =ₚ (ṫy.func t1 t2) →
            e' =ₚ (fun ι0 => exp.abst x (inst t1 ι0) (e1' ι0)) →
            P G (exp.absu x e1) t e' }
      {pabst : forall w,
        ⊢ ∀ (G : Ėnv w) x t1 t2 e1 e1' e' t,
            (G ,, x∷lift t1 w |--ₚ e1; t2 ~> e1') →
            P (G ,, x∷lift t1 w) e1 t2 e1' →
            t =ₚ (ṫy.func (lift t1 w) t2) →
            e' =ₚ (fun ι0 => exp.abst x t1 (e1' ι0)) →
            P G (exp.abst x t1 e1) t e' }
      {papp : forall w,
        ⊢ ∀ (G : Ėnv w) e1 t1 e1' e2 t2 e2' e',
            (G |--ₚ e1; ṫy.func t2 t1 ~> e1') →
            (G |--ₚ e2; t2 ~> e2') →
            P G e1 (ṫy.func t2 t1) e1' →
            P G e2 t2 e2' →
            e' =ₚ (fun ι0 => exp.app (e1' ι0) (e2' ι0)) →
            P G (exp.app e1 e2) t1 e' }.

    Lemma TPB_ind w G (e : Exp) (t : Ṫy w) (ee : Ėxp w) :
      (G |--ₚ e; t ~> ee) ⊢ₚ (P G e t ee).
    Proof.
      constructor. intros ι T. hnf in T.
      remember (inst G ι) as G'.
      remember (inst t ι) as t'.
      remember (inst ee ι) as ee'.
      revert HeqG' Heqt' Heqee'. revert G t ee. revert w ι.
      induction T; cbn; intros; subst.
      - apply pvar; cbn; try easy.
        now rewrite lookup_inst in H.
      - apply ptrue; cbn; easy.
      - apply pfalse; cbn; easy.
      - specialize (IHT1 w ι G ṫy.bool (fun _ => e1') eq_refl eq_refl eq_refl).
        specialize (IHT2 w ι G t0      (fun _ => e2') eq_refl eq_refl eq_refl).
        specialize (IHT3 w ι G t0      (fun _ => e3') eq_refl eq_refl eq_refl).
        eapply pif; cbn; eauto; eauto; easy.
      - specialize (IHT w ι (G ,, x∷lift t1 _) (lift t2 _) (fun _ => e')).
        rewrite inst_insert !inst_lift in IHT.
        specialize (IHT eq_refl eq_refl eq_refl).
        eapply pabsu; cbn; eauto;
        change (@inst _ _ (@Sem.inst_sem Exp) _ ?e ?ι) with (e ι) in *;
          cbn; rewrite ?inst_insert ?inst_lift; try easy.
      - specialize (IHT w ι (G ,, x∷lift t1 _) (lift t2 _) (fun _ => e')).
        cbn in IHT. rewrite inst_insert ?inst_lift in IHT.
        specialize (IHT eq_refl eq_refl eq_refl).
        eapply pabst; cbn; eauto;
          cbn; rewrite ?inst_insert ?inst_lift; try easy.
      - specialize (IHT1 w ι G (ṫy.func (lift t2 _) t) (fun _ => e1')). cbn in IHT1.
        rewrite ?inst_lift in IHT1. specialize (IHT1 eq_refl eq_refl eq_refl).
        specialize (IHT2 w ι G (lift t2 _) (fun _ => e2')).
        rewrite ?inst_lift in IHT2. specialize (IHT2 eq_refl eq_refl eq_refl).
        eapply papp; cbn; eauto; rewrite ?inst_lift; easy.
    Abort.

  End InductionScheme.

  Lemma eqₚ_insert {w} (G1 G2 : Ėnv w) (x : string) (t1 t2 : Ṫy w) :
    G1 =ₚ G2 /\ₚ t1 =ₚ t2 ⊢ₚ
    (G1 ,, x ∷ t1) =ₚ (G2 ,, x ∷ t2).
  Proof.
    constructor. intros ι. pred_unfold. intros [].
    rewrite !inst_insert. congruence.
  Qed.

  Lemma eq_func {w} (s1 s2 t1 t2 : Ṫy w) :
    ṫy.func s1 s2 =ₚ ṫy.func t1 t2 ⊣⊢ₚ (s1 =ₚ t1) /\ₚ (s2 =ₚ t2).
  Proof. now rewrite peq_ty_noconfusion. Qed.

  Section Modalities.

    Import Pred.notations.
    Import (hints) Sub.
    Import (* ProgramLogic  *)Pred.proofmode.
    Import iris.proofmode.tactics.
    Open Scope pred_scope.

    Section PersistModality.

      Context {Θ : ACC} [w0 w1] (θ : Θ w0 w1).

      Class IntoPersist (P : Pred w1) (Q : Pred w0) :=
        into_persist : P ⊢ persist Q θ.

      #[export] Instance into_persist_default (P : Pred w0) : IntoPersist (persist P θ) P.
      Proof. unfold IntoPersist. reflexivity. Qed.

      Definition modality_persist_mixin :
        modality_mixin (fun P => persist P θ)
          (MIEnvTransform IntoPersist)
          (MIEnvTransform IntoPersist).
      Proof. firstorder. Qed.

      Definition modality_persist : modality bi_pred bi_pred :=
        Modality _ (modality_persist_mixin).

      #[export] Instance from_modal_persist P :
        FromModal True modality_persist (persist P θ) (persist P θ) P.
      Proof. firstorder. Qed.

    End PersistModality.

    Section AccModality.

      Context {Θ : ACC} [w0 w1] (θ : Θ w0 w1).

      Class IntoAcc (P : Pred w0) (Q : Pred w1) :=
        into_acc : P ⊢ Acc.wlp θ Q.

      #[export] Instance into_acc_default (P : Pred w0) : IntoAcc P (persist P θ).
      Proof. constructor. cbn. intros ι0 HP ι1 <-. apply HP. Qed.

      Definition modality_wlp_mixin :
        modality_mixin (Acc.wlp θ)
          (MIEnvTransform IntoAcc)
          (MIEnvTransform IntoAcc).
      Proof. firstorder. Qed.

      Definition modality_wlp : modality bi_pred bi_pred :=
        Modality _ (modality_wlp_mixin).

      #[export] Instance from_modal_wlp P :
        FromModal True modality_wlp (Acc.wlp θ P) (Acc.wlp θ P) P.
      Proof. firstorder. Qed.

    End AccModality.

    #[global] Arguments IntoAcc {Θ} [w0 w1] θ P Q.
    #[global] Arguments into_acc {Θ} [w0 w1] θ P Q {_}.
    #[global] Hint Mode IntoAcc + + + + - - : typeclass_instances.

  End Modalities.

  Import World.notations.

  Definition wp_diamond {Θ : ACC} {A} :
    ⊢ʷ Diamond Θ A -> Box Θ (A -> Pred) -> Pred :=
    fun w '(existT w1 (θ, a)) Q => Acc.wp θ (Q w1 θ a).

  Definition wlp_diamond {Θ : ACC} {A} :
    ⊢ʷ Diamond Θ A -> Box Θ (A -> Pred) -> Pred :=
    fun w '(existT w1 (θ, a)) Q => Acc.wlp θ (Q w1 θ a).

  Definition wp_option {A w1 w2} :
    Option A w1 -> (A w1 -> Pred w2) -> Pred w2 :=
    fun o Q =>
      match o with
      | Some a => Q a
      | None => Falseₚ
      end.

  Lemma wp_option_bind {A B w1 w2 w3} (o : Option A w1)
    (f : A w1 -> Option B w2) (Q : B w2 -> Pred w3) :
    wp_option (option.bind o f) Q ⊣⊢ₚ wp_option o (fun a => wp_option (f a) Q).
  Proof. constructor; intros ι. now destruct o. Qed.

  Definition wlp_option {A w1 w2} :
    Option A w1 -> (A w1 -> Pred w2) -> Pred w2 :=
    fun o Q =>
      match o with
      | Some a => Q a
      | None => Trueₚ
      end.

  Definition wp_optiondiamond {Θ : ACC} {A} :
    ⊢ʷ DiamondT Θ Option A -> Box Θ (A -> Pred) -> Pred :=
    fun w m Q => wp_option m (fun d => wp_diamond d Q).

  Definition wlp_optiondiamond {Θ : ACC} {A} :
    ⊢ʷ DiamondT Θ Option A -> Box Θ (A -> Pred) -> Pred :=
    fun w m Q => wlp_option m (fun d => wlp_diamond d Q).

  Lemma wp_optiondiamond_bind' {Θ : ACC} {A B w1 w2} (o : Option A w1)
    (f : A w1 -> Option (Diamond Θ B) w2) (Q : Box Θ (B -> Pred) w2) :
    wp_optiondiamond (option.bind o f) Q ⊣⊢ₚ wp_option o (fun a => wp_optiondiamond (f a) Q).
  Proof. constructor; intros ι. now destruct o. Qed.

  Lemma wlp_optiondiamond_bind' {Θ : ACC} {A B w1 w2} (o : Option A w1)
    (f : A w1 -> Option (Diamond Θ B) w2) (Q : Box Θ (B -> Pred) w2) :
    wlp_optiondiamond (option.bind o f) Q ⊣⊢ₚ wlp_option o (fun a => wlp_optiondiamond (f a) Q).
  Proof. constructor; intros ι. now destruct o. Qed.

End Pred.
Export Pred (Pred).

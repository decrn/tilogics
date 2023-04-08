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
  Classes.Morphisms
  Classes.Morphisms_Prop
  Classes.RelationClasses
  Relations.Relation_Definitions.
From iris Require
  bi.derived_connectives
  bi.interface.
From Em Require Import
  Context
  Definitions
  Environment
  Substitution
  STLC.

Set Implicit Arguments.

#[local] Arguments Ty_hole {Σ i} xIn.
#[local] Arguments Ty_bool {Σ}.
#[local] Arguments Ty_func {Σ}.

Module Pred.
  #[local] Notation Expr := (Sem expr).

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

    Definition Ext {R : ACC} {instR : forall w, Inst (R w) (Assignment w)} :
      ⊢ʷ Pred -> Box R Pred := fun w0 p w1 r ι => p (inst r ι).
    #[global] Arguments Ext {_ _} [w] _%P [_] _ ι/.
    #[global] Instance params_ext : Params (@Ext) 6 := {}.

    Definition TPB : ⊢ʷ Env -> Const expr -> Ty -> Expr -> Pred :=
      fun w G e t ee ι => inst G ι |-- e ; inst t ι ~> inst ee ι.
    #[global] Arguments TPB [w] G e t ee ι/.

    (* Definition TPB {w : World} (G : Env w) (e : expr) (t : Ty w) (ee : Expr w) : Pred w := *)
    (*   fun ι => inst G ι |-- e ; inst t ι ~> inst ee ι. *)
    (* #[global] Arguments TPB [w] G e t ee ι/. *)

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
         bi_cofe           := ofe.discrete_cofe _;
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
       cbn [andₚ orₚ implₚ iffₚ Forall Exists Ext eqₚ TPB inst inst_ty inst_env] in *
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

  Definition ProperPost {R} {reflR : Refl R} {instR : forall w : World, Inst (R w) (Assignment w)}
    {AT A} {persA : Definitions.Persistent R AT} {instT : Inst AT A}
    {w} (Q : Box R (Impl AT Pred) w) : Prop :=
    forall w1 (r01 : R w w1) (te0 : AT w) (te1 : AT w1),
      (te1 =ₚ (persist _ te0 _ r01)) ⊢ₚ (Ext (Q w refl te0) r01 <->ₚ Q w1 r01 te1).

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
    #[export,program] Instance proper_bientails_forall {I w} :
      Proper (pointwise_relation I (⊣⊢ₚ) ==> (⊣⊢ₚ)) (@Pred.Forall I w).
    #[export,program] Instance proper_bientails_exists {I w} :
      Proper (pointwise_relation I (⊣⊢ₚ) ==> (⊣⊢ₚ)) (@Pred.Exists I w).
    #[export,program] Instance proper_ext_bientails
      {R : ACC} {instR : forall w, Inst (R w) (Assignment w)} {w} :
      Proper ((⊣⊢ₚ) ==> forall_relation (fun _ => eq ==> (⊣⊢ₚ))) (Ext (R:=R) (w:=w)).
    #[export,program] Instance proper_ext_entails
      {R : ACC} {instR : forall w, Inst (R w) (Assignment w)} {w} :
      Proper (entails ==> forall_relation (fun _ => eq ==> entails)) (Ext (R:=R) (w:=w)).
    #[export,program] Instance proper_ext_flip_entails
      {R : ACC} {instR : forall w, Inst (R w) (Assignment w)} {w} :
      Proper (entails --> forall_relation (fun _ => eq ==> Basics.flip entails)) (Ext (R:=R) (w:=w)).

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

    End Eq.
    #[global] Arguments eqₚ_trans {T A _ w} s t u.

    Lemma peq_ty_noconfusion {w} (t1 t2 : Ty w) :
      t1 =ₚ t2 ⊣⊢ₚ
            match t1 , t2 with
            | Ty_bool         , Ty_bool         => ⊤ₚ
            | Ty_func t11 t12 , Ty_func t21 t22 => t11 =ₚ t21 /\ₚ t12 =ₚ t22
            | Ty_hole _       , _               => t1 =ₚ t2
            | _               , Ty_hole _       => t1 =ₚ t2
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

    Section Ext.

      Import World.notations.

      Context {R : ACC} {instR : forall w, Inst (R w) (Assignment w)}.

      Lemma ext_refl {reflR : Refl R} {instReflR : InstRefl R} [w] (P : Pred w) :
        Ext P refl ⊣⊢ₚ P.
      Proof. obligation. Qed.
      Lemma ext_trans {transR : Trans R}
        {w0 w1 w2} (r1 : R w0 w1) (r2 : R w1 w2) (P : Pred w0) :
        Ext P (r1 ⊙ r2) ⊣⊢ₚ Ext (Ext P r1) r2.
      Proof. obligation. Qed.
      Lemma ext_and {w0 w1} (ζ01 : R w0 w1) (P Q : Pred w0) :
        Ext (P /\ₚ Q) ζ01 ⊣⊢ₚ Ext P ζ01 /\ₚ Ext Q ζ01.
      Proof. obligation. Qed.
      Lemma ext_impl {w0 w1} (ζ01 : R w0 w1) (P Q : Pred w0) :
        Ext (P ->ₚ Q) ζ01 ⊣⊢ₚ (Ext P ζ01 ->ₚ Ext Q ζ01).
      Proof. obligation. Qed.
      Lemma ext_false {w0 w1} (ζ01 : R w0 w1) :
        Ext ⊥ₚ ζ01 ⊣⊢ₚ ⊥ₚ.
      Proof. obligation. Qed.
      Lemma ext_true {w0 w1} (ζ01 : R w0 w1) :
        Ext ⊤ₚ ζ01 ⊣⊢ₚ ⊤ₚ.
      Proof. obligation. Qed.
      Lemma ext_eq {T : TYPE} {persR : Definitions.Persistent R T}
        {A : Type} {instTA : Inst T A}
        {w0 w1} (r : R w0 w1) (t1 t2 : T w0) :
        Ext (t1 =ₚ t2) r ⊣⊢ₚ persist w0 t1 w1 r =ₚ persist w0 t2 w1 r.
      Proof.
        constructor. unfold eqₚ, Ext. intros ι.
        (* now rewrite !inst_persist. *)
      Admitted.

      (* #[universes(polymorphic)]  *)Lemma ext_forall [A] [w1 w2] (r12 : R w1 w2) (Q : A -> Pred w1) :
        Ext (∀ₚ a : A, Q a) r12 ⊣⊢ₚ (∀ₚ a : A, Ext (Q a) r12).
      Proof. obligation. Qed.
      (* #[universes(polymorphic)]  *)Lemma ext_exists [A] [w1 w2] (r12 : R w1 w2) (Q : A -> Pred w1) :
        Ext (∃ₚ a : A, Q a) r12 ⊣⊢ₚ (∃ₚ a : A, Ext (Q a) r12).
      Proof. obligation. Qed.

      Import (hints) Sub.
      Lemma ext_reduce  {w α} (t : Ty w) P Q :
        (Ext P (step (R := Sub)) ⊢ₚ
           Ty_hole ctx.in_zero =ₚ persist w t (ctx.snoc w α) (step (R := Sub)) ->ₚ Q) ->
        P ⊢ₚ Ext Q (reduce (R := Sub) α t).
      Proof.
        rewrite ?entails_in. intros H ι HP. pred_unfold. rewrite inst_reduce.
        specialize (H (env.snoc ι α (inst t ι))).
        rewrite inst_persist inst_step_snoc in H. now apply H.
      Qed.

      Lemma ext_tpb {persRTy : Definitions.Persistent R Ty}
        {w1 w2} (r12 : R w1 w2) G (e : expr) (t : Ty w1) (ee : Expr w1) :
        Ext (G |--ₚ e; t ~> ee) r12 ⊣⊢ₚ
        persist w1 G w2 r12 |--ₚ e; persist w1 t w2 r12 ~> persist w1 ee w2 r12.
      Proof. obligation. Qed.

    End Ext.

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
  End InstPred.

  Module Acc.
    Import World.notations.
    Import (hints) Sub.
    Section WithAccessibilityRelation.
      Context {R : ACC} {instR : forall w, Inst (R w) (Assignment w)}.

      Definition wp {w0 w1} (r01 : R w0 w1) (Q : Pred w1) : Pred w0 :=
        fun ι0 => exists (ι1 : Assignment w1), inst r01 ι1 = ι0 /\ Q ι1.
      Definition wlp {w0 w1} (r01 : R w0 w1) (Q : Pred w1) : Pred w0 :=
        fun ι0 => forall (ι1 : Assignment w1), inst r01 ι1 = ι0 -> Q ι1.

      #[global] Arguments wp {_ _} _ _ ι0/.
      #[global] Arguments wlp {_ _} _ _ ι0/.

      #[export] Instance proper_wp_bientails {w0 w1} (r01 : R w0 w1) :
        Proper (bientails ==> bientails) (@wp w0 w1 r01).
      Proof. firstorder. Qed.

      #[export] Instance proper_wp_entails {w0 w1} (r01 : R w0 w1) :
        Proper (entails ==> entails) (@wp w0 w1 r01).
      Proof. firstorder. Qed.

      #[export] Instance proper_wlp_bientails {w0 w1} (r01 : R w0 w1) :
        Proper (bientails ==> bientails) (@wlp w0 w1 r01).
      Proof. firstorder. Qed.

      #[export] Instance proper_wlp_entails {w0 w1} (r01 : R w0 w1) :
        Proper (entails ==> entails) (@wlp w0 w1 r01).
      Proof. firstorder. Qed.

      Lemma wp_refl {reflR : Refl R} {instReflR : InstRefl R}
        {w} (Q : Pred w) : wp refl Q ⊣⊢ₚ Q.
      Proof.
        constructor. split; cbn.
        - intros (ι' & Heq & HQ). rewrite inst_refl in Heq. now subst.
        - intros HQ. exists ι. split. now rewrite inst_refl. easy.
      Qed.

      Lemma wp_trans {transR : Trans R}
        {w0 w1 w2} (r01 : R w0 w1) (r12 : R w1 w2) Q :
        wp (r01 ⊙ r12) Q ⊣⊢ₚ wp r01 (wp r12 Q).
      Proof.
        constructor. split; cbn.
        - intros (ι2 & Heq & HQ). rewrite inst_trans in Heq.
          exists (inst r12 ι2). split. easy. now exists ι2.
        - intros (ι1 & Heq1 & ι2 & Heq2 & HQ). exists ι2.
          split; [|easy]. rewrite inst_trans. congruence.
      Qed.

      Lemma wp_false {w0 w1} (r01 : R w0 w1) :
        wp r01 ⊥ₚ ⊣⊢ₚ ⊥ₚ.
      Proof. constructor. firstorder. Qed.

      Lemma wp_step {stepR : Step R} {w} {x} (Q : Pred (ctx.snoc w x)):
        wp (w0:=w) step Q ⊣⊢ₚ (∃ₚ t : Ty w, Ext Q (thick (xIn := ctx.in_zero) x t)).
      Proof.
        constructor. intros ι; pred_unfold; cbn - [thick].
        split.
        - intros (ι' & <- & HQ). destruct (env.view ι') as [ι t].
          rewrite inst_step_snoc. exists (lift t _). cbn - [thick].
          rewrite (inst_thick ctx.in_zero (lift t w) ι).
          now rewrite inst_lift.
        - cbn - [thick]. intros (t & HQ).
          exists (env.snoc ι _ (inst t ι)).
          rewrite inst_step_snoc.
          now rewrite (inst_thick ctx.in_zero t ι) in HQ.
      Qed.

      Lemma and_wp_l {w0 w1} (r01 : R w0 w1) P Q :
        wp r01 P /\ₚ Q ⊣⊢ₚ wp r01 (P /\ₚ Ext Q r01).
      Proof.
        constructor. split; cbn.
        - intros [(ι1 & <- & HP) HQ]. now exists ι1.
        - intros (ι1 & <- & HP & HQ). split; [|easy]. now exists ι1.
      Qed.

      Lemma and_wp_r {w0 w1} (r01 : R w0 w1) P Q :
        P /\ₚ wp r01 Q ⊣⊢ₚ wp r01 (Ext P r01 /\ₚ Q).
      Proof. now rewrite and_comm, and_wp_l, and_comm. Qed.

      Lemma wp_reduce {reduceR : Reduce R}
        {w α} (t : Ty w) (Q : Pred w) :
        wp (reduce α t) Q ⊣⊢ₚ
          Ty_hole ctx.in_zero =ₚ (persist _ t _ (step (R := Alloc))) /\ₚ Ext Q (step (R := Alloc)).
      Proof.
        constructor. intros ι; pred_unfold; cbn.
        split.
        - intros (ι1 & Heq & HQ). subst. now rewrite inst_reduce.
        - destruct (env.view ι) as [ι t']. cbn. intros [Heq HQ]. subst.
          exists ι. split; auto. now rewrite inst_reduce.
      Qed.

      Lemma wp_thick {thickR : Thick R} {instThickR : InstThick R}
        {w x} (xIn : ctx.In x w) (t : Ty (ctx.remove xIn)) (Q : Pred (ctx.remove xIn)) :
        wp (thick x t) Q ⊣⊢ₚ Ty_hole xIn =ₚ thin xIn t /\ₚ Ext Q (Sub.thin xIn).
      Proof.
        constructor. intros ι; pred_unfold; cbn.
        rewrite Sub.subst_thin, inst_persist, Sub.inst_thin.
        split.
        - intros (ι1 & Heq & HQ). subst.
          now rewrite inst_thick, env.remove_insert, env.lookup_insert.
        - intros [Heq HQ]. exists (env.remove x ι xIn).
          rewrite inst_thick. rewrite <- Heq. now rewrite env.insert_remove.
      Qed.

      Lemma wlp_refl {reflR : Refl R} {instReflR : InstRefl R}
        {w} (Q : Pred w) : wlp refl Q ⊣⊢ₚ Q.
      Proof.
        constructor. split; cbn.
        - intros HQ. apply HQ. now rewrite inst_refl.
        - intros HQ ? <-. now rewrite inst_refl in HQ.
      Qed.

      Lemma wlp_trans {transR : Trans R}
        {w0 w1 w2} (r01 : R w0 w1) (r12 : R w1 w2) Q :
        wlp (r01 ⊙ r12) Q ⊣⊢ₚ wlp r01 (wlp r12 Q).
      Proof.
        constructor. split; cbn.
        - intros HQ ι1 Heq1 ι2 Heq2. apply HQ.
          subst. now rewrite inst_trans.
        - intros HQ ι2 Heq. rewrite inst_trans in Heq.
          now apply (HQ (inst r12 ι2)).
      Qed.

      Lemma wlp_true {w0 w1} (r01 : R w0 w1) :
        wlp r01 Trueₚ ⊣⊢ₚ Trueₚ.
      Proof. constructor. firstorder. Qed.

      Lemma wlp_impl {w0 w1} (r01 : R w0 w1) P Q :
        wlp r01 (P ->ₚ Q) ⊢ₚ wlp r01 P ->ₚ wlp r01 Q.
      Proof. constructor. firstorder. Qed.

      Lemma wlp_and {w0 w1} (r01 : R w0 w1) P Q :
        wlp r01 P /\ₚ wlp r01 Q ⊢ₚ wlp r01 (P /\ₚ Q).
      Proof. constructor. firstorder. Qed.

      Lemma entails_wlp {w0 w1} (r01 : R w0 w1) P Q :
        (Ext P r01 ⊢ₚ Q) <-> (P ⊢ₚ wlp r01 Q).
      Proof.
        split; intros [HPQ]; constructor.
        - intros ι0 HP ι1 <-. revert HP. apply HPQ.
        - intros ι1 HP. now apply (HPQ (inst r01 ι1)).
      Qed.

      Lemma entails_wp {w0 w1} (r01 : R w0 w1) P Q :
        (P ⊢ₚ Ext Q r01) <-> (wp r01 P ⊢ₚ Q).
      Proof.
        split; intros [HPQ]; constructor.
        - intros ι0 (ι1 & <- & HP). now apply HPQ.
        - intros ι1 HP. apply (HPQ (inst r01 ι1)).
          exists ι1. split; auto.
      Qed.

      Lemma wlp_reduce {reduceR : Reduce R} {w α} (t : Ty w) (Q : Pred w) :
        wlp (reduce α t) Q ⊣⊢ₚ
          Ty_hole ctx.in_zero =ₚ (persist _ t _ (step (R := Alloc))) ->ₚ Ext Q (step (R := Alloc)).
      Proof.
      Admitted.

      Lemma wlp_thick {thickR : Thick R} {instThickR : InstThick R}
        {w x} (xIn : ctx.In x w) (t : Ty (ctx.remove xIn)) (Q : Pred (ctx.remove xIn)) :
        wlp (thick x t) Q ⊣⊢ₚ Ty_hole xIn =ₚ thin xIn t ->ₚ Ext Q (Sub.thin xIn).
      Proof.
        constructor. intros ι; pred_unfold; cbn.
        rewrite Sub.subst_thin, inst_persist, Sub.inst_thin.
        split; intros HQ.
        - specialize (HQ (env.remove x ι xIn)). intros Heq.
          rewrite inst_thick in HQ.
          rewrite <- Heq in HQ.
          rewrite env.insert_remove in HQ. auto.
        - intros ι1 Heq. subst.
          rewrite inst_thick, env.remove_insert, env.lookup_insert in HQ.
          now apply HQ.
      Qed.

      Lemma wlp_step {stepR : Step R} {w} {x} (Q : Pred (ctx.snoc w x)):
        wlp (w0:=w) step Q ⊣⊢ₚ (∀ₚ t : Ty w, Ext Q (thick (xIn := ctx.in_zero) x t)).
      Proof.
        constructor. intros ι; pred_unfold; cbn - [thick].
        split.
        - intros HQ t. apply HQ.
          rewrite (inst_thick ctx.in_zero t ι). cbn.
          now rewrite inst_step_snoc.
        - cbn - [thick]. intros HQ ι' <-.
          destruct (env.view ι') as [ι t].
          specialize (HQ (lift t _)).
          rewrite inst_step_snoc in HQ.
          rewrite (inst_thick ctx.in_zero (lift t w) ι) in HQ.
          now rewrite inst_lift in HQ.
      Qed.

    End WithAccessibilityRelation.
    (* #[global] Opaque wp. *)
    (* #[global] Opaque wlp. *)

  End Acc.

  Lemma pno_cycle {w} (t1 t2 : Ty w) (Hsub : Ty_subterm t1 t2) :
    t1 =ₚ t2 ⊢ₚ ⊥ₚ.
  Proof.
    constructor. intros ι Heq.
    apply (inst_subterm ι) in Hsub. cbn in Hsub.
    rewrite <- Heq in Hsub. now apply ty_no_cycle in Hsub.
  Qed.


  (* A predicate-based induction scheme for the typing relation. *)
  Section InductionScheme.

    Import iris.bi.interface.
    Import World.notations.
    Import Pred.notations.
    Import Pred.proofmode.

    Open Scope pred_scope.

    Context (P : ⊢ʷ Env -> Const expr -> Ty -> Expr -> Pred).
    Context
      {pfalse : forall w,
        ⊢ ∀ G : Env w, ∀ t : Ty w, ∀ e' : Expr w,
            t =ₚ Ty_bool →
            e' =ₚ (S.pure v_false) →
            P G v_false t e' }
      {ptrue : forall w,
        ⊢ ∀ G : Env w, ∀ t : Ty w, ∀ e' : Expr w,
            t =ₚ Ty_bool →
            e' =ₚ (S.pure v_true) →
            P G v_true t e' }
      {pif : forall w,
        ⊢ ∀ (G : Env w) (e1 e2 e3 : expr) (e' e1' e2' e3' : Expr w) t,
            (G |--ₚ e1; Ty_bool ~> e1') →
            (G |--ₚ e2; t ~> e2') →
            (G |--ₚ e3; t ~> e3') →
            P G e1 Ty_bool e1' →
            P G e2 t e2' →
            P G e3 t e3' →
            e' =ₚ (fun ι0 => e_if (e1' ι0) (e2' ι0) (e3' ι0)) →
            P G (e_if e1 e2 e3) t e' }
      {pvar : forall w,
        ⊢ ∀ (G : Env w) x t e',
            resolve x G =ₚ Some t →
            e' =ₚ (fun _ => e_var x) →
            P G (e_var x) t e' }
      {pabsu : forall w,
        ⊢ ∀ (G : Env w) x t1 t2 t e1 e1' e',
            (cons (x, t1) G |--ₚ e1; t2 ~> e1') →
            P (cons (x, t1) G) e1 t2 e1' →
            t =ₚ (Ty_func t1 t2) →
            e' =ₚ (fun ι0 => e_abst x (inst t1 ι0) (e1' ι0)) →
            P G (e_absu x e1) t e' }
      {pabst : forall w,
        ⊢ ∀ (G : Env w) x t1 t2 e1 e1' e' t,
            (cons (x, lift t1 w) G |--ₚ e1; t2 ~> e1') →
            P (cons (x, lift t1 w) G) e1 t2 e1' →
            t =ₚ (Ty_func (lift t1 w) t2) →
            e' =ₚ (fun ι0 => e_abst x t1 (e1' ι0)) →
            P G (e_abst x t1 e1) t e' }
      {papp : forall w,
        ⊢ ∀ (G : Env w) e1 t1 e1' e2 t2 e2' e',
            (G |--ₚ e1; Ty_func t2 t1 ~> e1') →
            (G |--ₚ e2; t2 ~> e2') →
            P G e1 (Ty_func t2 t1) e1' →
            P G e2 t2 e2' →
            e' =ₚ (fun ι0 => e_app (e1' ι0) (e2' ι0)) →
            P G (e_app e1 e2) t1 e' }.

    Lemma TPB_ind w G (e : expr) (t : Ty w) (ee : Expr w) :
      (G |--ₚ e; t ~> ee) ⊢ₚ (P G e t ee).
    Proof.
      constructor. intros ι T. hnf in T.
      remember (inst G ι) as G'.
      remember (inst t ι) as t'.
      remember (inst ee ι) as ee'.
      revert HeqG' Heqt' Heqee'. revert G t ee. revert w ι.
      induction T; cbn; intros; subst.
      - apply pfalse; cbn; easy.
      - apply ptrue; cbn; easy.
      - specialize (IHT1 w ι G Ty_bool (fun _ => cnd') eq_refl eq_refl eq_refl).
        specialize (IHT2 w ι G t0      (fun _ => coq') eq_refl eq_refl eq_refl).
        specialize (IHT3 w ι G t0      (fun _ => alt') eq_refl eq_refl eq_refl).
        eapply pif; cbn; eauto; eauto; easy.
      - apply pvar; cbn; try easy.
        now rewrite resolve_inst in H.
      - specialize (IHT w ι (cons (v, lift vt _) G) (lift t _) (fun _ => e')).
        cbn in IHT. rewrite ?inst_lift in IHT.
        specialize (IHT eq_refl eq_refl eq_refl).
        eapply pabsu; cbn; eauto; rewrite ?inst_lift; try easy.
        change (@inst _ _ (@inst_sem expr) _ ?e ?ι) with (e ι); cbn.
        now rewrite inst_lift.
      - specialize (IHT w ι (cons (v, lift vt _) G) (lift t _) (fun _ => e')).
        cbn in IHT. rewrite ?inst_lift in IHT.
        specialize (IHT eq_refl eq_refl eq_refl).
        eapply pabst; cbn; eauto; rewrite ?inst_lift; easy.
      - specialize (IHT1 w ι G (Ty_func (lift t2 _) t) (fun _ => e1')). cbn in IHT1.
        rewrite ?inst_lift in IHT1. specialize (IHT1 eq_refl eq_refl eq_refl).
        specialize (IHT2 w ι G (lift t2 _) (fun _ => e2')).
        rewrite ?inst_lift in IHT2. specialize (IHT2 eq_refl eq_refl eq_refl).
        eapply papp; cbn; eauto; rewrite ?inst_lift; easy.
    Abort.

  End InductionScheme.

End Pred.
Export Pred (Pred).

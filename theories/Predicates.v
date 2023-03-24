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

    Context {w : World}.

    Definition bientails : relation (Pred w) :=
      fun P Q => forall ι, P ι <-> Q ι.
    Definition entails : relation (Pred w) :=
      fun P Q => forall ι, P ι -> Q ι.

    #[export] Instance equivalence_bientails : Equivalence bientails.
    Proof.
      constructor; unfold Reflexive, Symmetric, Transitive, bientails;
        [ reflexivity | now symmetry | now etransitivity ].
    Qed.
    #[export] Instance preorder_entails : RelationClasses.PreOrder entails.
    Proof. constructor; unfold Reflexive, Transitive, entails; auto. Qed.

    #[export] Instance subrelation_bientails_entails :
      subrelation bientails entails.
    Proof. intros x y xy ι. apply xy. Qed.

    #[export] Instance subrelation_bientails_flip_entails :
      subrelation bientails (Basics.flip entails).
    Proof. intros x y xy ι. apply xy. Qed.

    (* #[export] Instance proper_bientails : *)
    (*   Proper (bientails ==> bientails ==> iff) bientails. *)
    (* Proof. intuition. Qed. *)
    #[export] Instance proper_entails_bientails :
      Proper (bientails ==> bientails ==> iff) entails.
    Proof. unfold Proper, respectful, bientails, entails. intuition. Qed.
    #[export] Instance proper_entails_entails :
      Proper (Basics.flip entails ==> entails ==> Basics.impl) entails.
    Proof. unfold Proper, respectful, Basics.impl, entails. intuition. Qed.

  End RewriteRelations.
  #[global] Arguments bientails {w} (_ _)%P.
  #[global] Arguments entails {w} (_ _)%P.
  #[global] Typeclasses Opaque entails.
  #[global] Typeclasses Opaque bientails.

  Section Definitions.

    Definition Falseₚ : ⊢ Pred :=
      fun w _ => Logic.False.
    Definition Trueₚ : ⊢ Pred :=
      fun w _ => Logic.True.
    Definition iffₚ : ⊢ Pred -> Pred -> Pred :=
      fun w P Q ι => P ι <-> Q ι.
    Definition implₚ : ⊢ Pred -> Pred -> Pred :=
      fun w P Q ι => (P ι -> Q ι)%type.
    Definition andₚ : ⊢ Pred -> Pred -> Pred :=
      fun w P Q ι => (P ι /\ Q ι)%type.
    #[global] Arguments andₚ {_} (_ _)%P _/.
    #[global] Arguments iffₚ {_} (_ _)%P _/.
    #[global] Arguments implₚ {_} (_ _)%P _/.
    #[global] Arguments Trueₚ {_} _/.
    #[global] Arguments Falseₚ {_} _/.

    Definition eqₚ {T : TYPE} {A : Type} {instTA : Inst T A} :
      ⊢ T -> T -> Pred :=
      fun w t1 t2 ι => inst t1 ι = inst t2 ι.
    #[global] Arguments eqₚ {T A _} [w] _ _ _/.

    Definition Forall {I : TYPE} : ⊢ (I -> Pred) -> Pred :=
      fun w A ι => forall i : I w, A i ι.
    Definition Exists {I : TYPE} : ⊢ (I -> Pred) -> Pred :=
      fun w A ι => exists i : I w, A i ι.
    #[global] Arguments Forall {I w} A%P ι/.
    #[global] Arguments Exists {I w} A%P ι/.

    Definition Ext {R : ACC} {instR : forall w, Inst (R w) (Assignment w)} :
      ⊢ Pred -> Box R Pred :=
      fun w0 p w1 r ι => p (inst r ι).
    #[global] Arguments Ext {_ _} [w] _%P [_] _ _/.
    #[global] Instance params_ext : Params (@Ext) 6 := {}.

    Definition TPB : ⊢ Env -> Const expr -> Ty -> Expr -> Pred :=
      fun w G e t ee ι => inst G ι |-- e ; inst t ι ~> inst ee ι.
    #[global] Arguments TPB [w] G e t ee ι/.

  End Definitions.

  Module Import notations.

    Infix "⊣⊢ₚ" := (bientails) (at level 95).
    Infix "⊢ₚ" := (entails) (at level 95).

    Notation "⊤ₚ" := Trueₚ : pred_scope.
    Notation "⊥ₚ" := Falseₚ : pred_scope.
    Infix "<->ₚ"  := (iffₚ) (at level 94) : pred_scope.
    Infix "->ₚ"   := (implₚ) (at level 94, right associativity) : pred_scope.
    Infix "/\ₚ"   := (andₚ) (at level 80, right associativity) : pred_scope.

    Infix "=ₚ" := eqₚ (at level 70, no associativity) : pred_scope.

    Notation "'∀ₚ' x ∶ T , Q" :=
      (@Forall T _ (fun x => Q%P))
        (at level 99, x binder, x at next level, T at level 95,
          right associativity,
          format "'∀ₚ'  x  ∶  T ,  Q")
      : pred_scope.

    Notation "'∀ₚ⁺' x .. y , Q " :=
      (Forall (fun x => .. (Forall (fun y => Q%P)) ..))
        (at level 99, x binder, y binder, right associativity,
        only parsing)
      : pred_scope.

    (* Notation "'∃' x .. y , Q " := *)
    (*     (Exists (fun x => .. (Exists (fun y => Q%P)) ..)) *)
    (*       (at level 94, x binder, y binder, right associativity) *)
    (*     : pred_scope. *)

    Notation "'∃ₚ' x ∶ T , Q" :=
      (@Exists T _ (fun x => Q%P))
        (at level 99, x binder, right associativity,
          format "'∃ₚ'  x  ∶  T ,  Q")
        : pred_scope.

    Notation "'Fun' x => b" :=
      (fun w ζ x => b%P w ζ)
        (x binder, at level 100) : pred_scope.

    Notation "G |--ₚ E ; T ~> EE" :=
      (TPB G E T EE) (at level 70, no associativity) : pred_scope.

  End notations.

  Section Lemmas.

    Create HintDb obligation.
    #[local] Hint Rewrite @inst_refl @inst_trans : obligation.

    #[local] Ltac obligation :=
      unfold Proper, respectful, pointwise_relation, forall_relation,
        entails, bientails;
        cbn; intros; subst;
      try (match goal with
         | |- (forall _ : ?A, _) <-> (forall _ : ?A, _) =>
             apply all_iff_morphism; intro
         | |- (exists _ : ?A, _) <-> (exists _ : ?A, _) =>
             apply ex_iff_morphism; intro
         end);
      autorewrite with obligation;
      try easy; try (intuition; fail); try (intuition congruence; fail).
    #[local] Obligation Tactic := obligation.

    #[export,program] Instance proper_iff {w} :
      Proper (bientails ==> bientails ==> bientails) (@iffₚ w).
    #[export,program] Instance proper_impl_bientails {w} :
      Proper (bientails ==> bientails ==> bientails) (@implₚ w).
    #[export,program] Instance proper_impl_entails {w} :
      Proper (entails --> entails ==> entails) (@implₚ w).
    #[export,program] Instance proper_and_bientails {w} :
      Proper (bientails ==> bientails ==> bientails) (@andₚ w).
    #[export,program] Instance proper_and_entails {w} :
      Proper (entails ==> entails ==> entails) (@andₚ w).
    #[export,program] Instance proper_bientails_forall {I w} :
      Proper (pointwise_relation (I w) bientails ==> bientails) Forall.
    #[export,program] Instance proper_bientails_exists {I w} :
      Proper (pointwise_relation (I w) bientails ==> bientails) Exists.
    #[export,program] Instance proper_ext_bientails
      {R : ACC} {instR : forall w, Inst (R w) (Assignment w)} {w} :
      Proper (bientails ==> forall_relation (fun _ => eq ==> bientails)) (Ext (R:=R) (w:=w)).
    #[export,program] Instance proper_ext_entails
      {R : ACC} {instR : forall w, Inst (R w) (Assignment w)} {w} :
      Proper (entails ==> forall_relation (fun _ => eq ==> entails)) (Ext (R:=R) (w:=w)).

    Lemma split_bientails {w} (P Q : Pred w) :
      (P ⊣⊢ₚ Q) <-> (P ⊢ₚ Q) /\ (Q ⊢ₚ P).
    Proof. obligation. Qed.
    Lemma and_left1 {w} {P Q R : Pred w} : P ⊢ₚ R -> P /\ₚ Q ⊢ₚ R.
    Proof. obligation. Qed.
    Lemma and_left2 {w} {P Q R : Pred w} : Q ⊢ₚ R -> P /\ₚ Q ⊢ₚ R.
    Proof. obligation. Qed.
    Lemma and_right {w} {P Q R : Pred w} : P ⊢ₚ Q -> P ⊢ₚ R -> P ⊢ₚ Q /\ₚ R.
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

    Lemma forall_l {I : TYPE} {w} (P : I w -> Pred w) Q :
      (exists x : I w, P x ⊢ₚ Q) -> (∀ₚ x ∶ I, P x) ⊢ₚ Q.
    Proof. obligation. firstorder. Qed.
    Lemma forall_r {I : TYPE} {w} P (Q : I w -> Pred w) :
      (P ⊢ₚ (∀ₚ x ∶ I, Q x)) <-> (forall x : I w, P ⊢ₚ Q x).
    Proof. obligation. Qed.

    Lemma exists_l {I : TYPE} {w} P (Q : I w -> Pred w) :
      (exists x : I w, P ⊢ₚ Q x) -> P ⊢ₚ (∃ₚ x ∶ I, Q x).
    Proof. obligation. firstorder. Qed.
    Lemma exists_r {I : TYPE} {w} P (Q : I w -> Pred w) :
      (exists x : I w, P ⊢ₚ Q x) -> P ⊢ₚ (∃ₚ x ∶ I, Q x).
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

      Lemma eqₚ_symmetry {w} (s t : T w) : s =ₚ t ⊣⊢ₚ t =ₚ s.
      Proof. obligation. Qed.

    End Eq.

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

    Section Ext.

      Context {R : ACC} {instR : forall w, Inst (R w) (Assignment w)}.

      Lemma ext_refl {reflR : Refl R} {instReflR : InstRefl R} {w} (P : Pred w) :
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
      Lemma ext_eq {T : TYPE} {persR : Persistent R T}
        {A : Type} {instTA : Inst T A}
        {w0 w1} (r : R w0 w1) (t1 t2 : T w0) :
        Ext (t1 =ₚ t2) r ⊣⊢ₚ persist w0 t1 w1 r =ₚ persist w0 t2 w1 r.
      Proof.
        unfold bientails, eqₚ, Ext. intros ι.
        (* now rewrite !inst_persist. *)
      Admitted.

      Lemma ext_forall_const {A} {w1 w2} (r12 : R w1 w2) (Q : A -> Pred w1) :
        Ext (∀ₚ a ∶ Const A, Q a) r12 ⊣⊢ₚ (∀ₚ a ∶ Const A, Ext (Q a) r12).
      Proof. obligation. Qed.
      Lemma ext_tpb {persRTy : Persistent R Ty}
        {w1 w2} (r12 : R w1 w2) G (e : expr) (t : Ty w1) (ee : Expr w1) :
        Ext (G |--ₚ e; t ~> ee) r12 ⊣⊢ₚ
        persist w1 G w2 r12 |--ₚ persist w1 e w2 r12; persist w1 t w2 r12 ~> persist w1 ee w2 r12.
      Proof. obligation. now rewrite inst_persist_ty, inst_persist_env. Qed.

    End Ext.

  End Lemmas.

  (* A type class for things that can be interpreted as a predicate. *)
  Class InstPred (A : TYPE) :=
    instpred : ⊢ A -> Pred.

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

  Module Acc.
    Import (hints) Sub.
    Section WithAccessibilityRelation.
      Context {R : ACC} {instR : forall w, Inst (R w) (Assignment w)}.

      Definition wp {w0 w1} (r01 : R w0 w1) (Q : Pred w1) : Pred w0 :=
        fun ι0 => exists (ι1 : Assignment w1), inst r01 ι1 = ι0 /\ Q ι1.
      Definition wlp {w0 w1} (r01 : R w0 w1) (Q : Pred w1) : Pred w0 :=
        fun ι0 => forall (ι1 : Assignment w1), inst r01 ι1 = ι0 -> Q ι1.

      #[local] Arguments wp {_ _} _ _ _/.
      #[local] Arguments wlp {_ _} _ _ _/.

      #[export] Instance proper_wp_bientails {w0 w1} (r01 : R w0 w1) :
        Proper (bientails ==> bientails) (@wp w0 w1 r01).
      Proof.
        intros p q pq ι. cbn. apply ex_iff_morphism.
        intros ι1. apply and_iff_morphism. easy. apply pq.
      Qed.

      #[export] Instance proper_wp_entails {w0 w1} (r01 : R w0 w1) :
        Proper (entails ==> entails) (@wp w0 w1 r01).
      Proof.
        intros p q pq ι. cbn. intros (ι0 & Heq & HP).
        exists ι0. split. easy. now apply pq.
      Qed.

      #[export] Instance proper_wlp_bientails {w0 w1} (r01 : R w0 w1) :
        Proper (bientails ==> bientails) (@wlp w0 w1 r01).
      Proof.
        intros p q pq ι. cbn. apply all_iff_morphism. intros ι1.
        now apply iff_iff_iff_impl_morphism.
      Qed.

      #[export] Instance proper_wlp_entails {w0 w1} (r01 : R w0 w1) :
        Proper (entails ==> entails) (@wlp w0 w1 r01).
      Proof. intros P Q HPQ ι HP ι0 Heq. now apply HPQ, HP. Qed.

      Lemma wp_refl {reflR : Refl R} {instReflR : InstRefl R}
        {w} (Q : Pred w) : wp refl Q ⊣⊢ₚ Q.
      Proof.
        split; cbn.
        - intros (ι' & Heq & HQ). rewrite inst_refl in Heq. now subst.
        - intros HQ. exists ι. split. now rewrite inst_refl. easy.
      Qed.

      Lemma wp_trans {transR : Trans R}
        {w0 w1 w2} (r01 : R w0 w1) (r12 : R w1 w2) Q :
        wp (r01 ⊙ r12) Q ⊣⊢ₚ wp r01 (wp r12 Q).
      Proof.
        split; cbn.
        - intros (ι2 & Heq & HQ). rewrite inst_trans in Heq.
          exists (inst r12 ι2). split. easy. now exists ι2.
        - intros (ι1 & Heq1 & ι2 & Heq2 & HQ). exists ι2.
          split; [|easy]. rewrite inst_trans. congruence.
      Qed.

      Lemma wp_false {w0 w1} (r01 : R w0 w1) :
        wp r01 ⊥ₚ ⊣⊢ₚ ⊥ₚ.
      Proof. firstorder. Qed.

      Lemma wp_step {stepR : Step R} {w} {x} (Q : Pred (ctx.snoc w x)):
        wp (w0:=w) step Q ⊣⊢ₚ (∃ₚ t ∶ Ty, Ext Q (thick (xIn := ctx.in_zero) x t)).
      Proof.
        intros ι. cbn - [thick]. unfold Exists.
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
        split; cbn.
        - intros [(ι1 & <- & HP) HQ]. now exists ι1.
        - intros (ι1 & <- & HP & HQ). split; [|easy]. now exists ι1.
      Qed.

      Lemma and_wp_r {w0 w1} (r01 : R w0 w1) P Q :
        P /\ₚ wp r01 Q ⊣⊢ₚ wp r01 (Ext P r01 /\ₚ Q).
      Proof. now rewrite and_comm, and_wp_l, and_comm. Qed.

      Lemma wp_thick {thickR : Thick R} {instThickR : InstThick R}
        {w x} (xIn : ctx.In x w) (t : Ty (ctx.remove xIn)) (Q : Pred (ctx.remove xIn)) :
        wp (thick x t) Q ⊣⊢ₚ Ty_hole xIn =ₚ thin xIn t /\ₚ Ext Q (Sub.thin xIn).
      Proof.
        intros ι; cbn. rewrite Sub.subst_thin, inst_persist_ty, Sub.inst_thin.
        split.
        - intros (ι1 & Heq & HQ). subst.
          now rewrite inst_thick, env.remove_insert, env.lookup_insert.
        - intros [Heq HQ]. exists (env.remove x ι xIn).
          now rewrite inst_thick, <- Heq, env.insert_remove.
      Qed.

      Lemma wlp_refl {reflR : Refl R} {instReflR : InstRefl R}
        {w} (Q : Pred w) : wlp refl Q ⊣⊢ₚ Q.
      Proof.
        split; cbn.
        - intros HQ. apply HQ. now rewrite inst_refl.
        - intros HQ ? <-. now rewrite inst_refl in HQ.
      Qed.

      Lemma wlp_trans {transR : Trans R}
        {w0 w1 w2} (r01 : R w0 w1) (r12 : R w1 w2) Q :
        wlp (r01 ⊙ r12) Q ⊣⊢ₚ wlp r01 (wlp r12 Q).
      Proof.
        split; cbn.
        - intros HQ ι1 Heq1 ι2 Heq2. apply HQ.
          subst. now rewrite inst_trans.
        - intros HQ ι2 Heq. rewrite inst_trans in Heq.
          now apply (HQ (inst r12 ι2)).
      Qed.

      Lemma wlp_true {w0 w1} (r01 : R w0 w1) :
        wlp r01 Trueₚ ⊣⊢ₚ Trueₚ.
      Proof. firstorder. Qed.

      Lemma wlp_impl {w0 w1} (r01 : R w0 w1) P Q :
        wlp r01 (P ->ₚ Q) ⊢ₚ wlp r01 P ->ₚ wlp r01 Q.
      Proof. intros ι0. cbn. intros HPQ HP ι1 <-. firstorder. Qed.

      Lemma entails_wlp {w0 w1} (r01 : R w0 w1) P Q :
        (Ext P r01 ⊢ₚ Q) <-> (P ⊢ₚ wlp r01 Q).
      Proof.
        cbv [entails Ext wlp].
        split.
        - intros HPQ ι0 HP ι1 <-. revert HP. apply HPQ.
        - intros HPQ ι1 HP. now apply (HPQ (inst r01 ι1)).
      Qed.

      Lemma entails_wp {w0 w1} (r01 : R w0 w1) P Q :
        (P ⊢ₚ Ext Q r01) <-> (wp r01 P ⊢ₚ Q).
      Proof.
        cbv [entails Ext wp].
        split.
        - intros HPQ ι0 (ι1 & <- & HP). now apply HPQ.
        - intros HPQ ι1 HP. apply (HPQ (inst r01 ι1)).
          exists ι1. split; auto.
      Qed.

      Lemma wlp_thick {thickR : Thick R} {instThickR : InstThick R}
        {w x} (xIn : ctx.In x w) (t : Ty (ctx.remove xIn)) (Q : Pred (ctx.remove xIn)) :
        wlp (thick x t) Q ⊣⊢ₚ Ty_hole xIn =ₚ thin xIn t ->ₚ Ext Q (Sub.thin xIn).
      Proof.
        intros ι; cbn. rewrite Sub.subst_thin, inst_persist_ty, Sub.inst_thin.
        split; intros HQ.
        - specialize (HQ (env.remove x ι xIn)). intros Heq.
          rewrite inst_thick, <- Heq, env.insert_remove in HQ. auto.
        - intros ι1 Heq. subst.
          rewrite inst_thick, env.remove_insert, env.lookup_insert in HQ.
          now apply HQ.
      Qed.

      Lemma wlp_step {stepR : Step R} {w} {x} (Q : Pred (ctx.snoc w x)):
        wlp (w0:=w) step Q ⊣⊢ₚ (∀ₚ t ∶ Ty, Ext Q (thick (xIn := ctx.in_zero) x t)).
      Proof.
        intros ι. cbn - [thick]. unfold Forall.
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

  Lemma pno_cycle {w} (t1 t2 : Ty w) :
    Ty_subterm t1 t2 ->
    t1 =ₚ t2  ⊢ₚ  ⊥ₚ.
  Proof.
    intros Hsub ι Heq.
    apply (inst_subterm ι) in Hsub. cbn in Hsub.
    rewrite <- Heq in Hsub. now apply ty_no_cycle in Hsub.
  Qed.

  (* A predicate-based induction scheme for the typing relation. *)
  Section InductionScheme.

    Context (P : ⊢ Env -> Const expr -> Ty -> Expr -> Pred).
    Context
      {pfalse : forall w,
          entails (w := w) Trueₚ
         (∀ₚ G ∶ Env, ∀ₚ t ∶ Ty, ∀ₚ e' ∶ Expr,
             t =ₚ Ty_bool ->ₚ
             e' =ₚ (S.pure v_false) ->ₚ
             P G v_false t e')%P }
      {ptrue : forall w, entails Trueₚ (w := w)
         (∀ₚ G ∶ Env, ∀ₚ t ∶ Ty, ∀ₚ e' ∶ Expr,
             t =ₚ Ty_bool ->ₚ
             e' =ₚ (S.pure v_true) ->ₚ
             P G v_true t e')%P }
      {pif : forall w, entails Trueₚ (w := w)
         (∀ₚ⁺ G e1 e2 e3 e' e1' e2' e3' t,
             (G |--ₚ e1; Ty_bool ~> e1') ->ₚ
             (G |--ₚ e2; t ~> e2') ->ₚ
             (G |--ₚ e3; t ~> e3') ->ₚ
             P G e1 Ty_bool e1' ->ₚ
             P G e2 t e2' ->ₚ
             P G e3 t e3' ->ₚ
             e' =ₚ (fun ι0 => e_if (e1' ι0) (e2' ι0) (e3' ι0)) ->ₚ
             P G (e_if e1 e2 e3) t e')%P }
      {pvar : forall w (G : Env w) x t e', entails Trueₚ
         ((resolve x G) =ₚ (Some t) ->ₚ
          e' =ₚ (fun _ => e_var x) ->ₚ
          P G (e_var x) t e') }
      {pabsu : forall w (G : Env w) x t1 t2 t e1 e1' e',
        entails Trueₚ
          ((cons (x, t1) G |--ₚ e1; t2 ~> e1') ->ₚ
           P (cons (x, t1) G) e1 t2 e1' ->ₚ
           t =ₚ (Ty_func t1 t2) ->ₚ
           e' =ₚ (fun ι0 => e_abst x (inst t1 ι0) (e1' ι0)) ->ₚ
           P G (e_absu x e1) t e' )}
      {pabst : forall w (G : Env w) x t1 t2 e1 e1' e' t,
          entails Trueₚ
            ((cons (x, lift t1 w) G |--ₚ e1; t2 ~> e1') ->ₚ
             P (cons (x, lift t1 w) G) e1 t2 e1' ->ₚ
             t =ₚ (Ty_func (lift t1 w) t2) ->ₚ
             e' =ₚ (fun ι0 => e_abst x t1 (e1' ι0)) ->ₚ
             P G (e_abst x t1 e1) t e')}
      {papp : forall w (G : Env w) e1 t1 e1' e2 t2 e2' e',
          entails Trueₚ
            ((G |--ₚ e1; Ty_func t2 t1 ~> e1') ->ₚ
             (G |--ₚ e2; t2 ~> e2') ->ₚ
             P G e1 (Ty_func t2 t1) e1' ->ₚ
             P G e2 t2 e2' ->ₚ
             e' =ₚ (fun ι0 => e_app (e1' ι0) (e2' ι0)) ->ₚ
             P G (e_app e1 e2) t1 e')%P }.

    Lemma TPB_ind w G (e : expr) (t : Ty w) (ee : Expr w) :
      (G |--ₚ e; t ~> ee) ⊢ₚ (P G e t ee).
    Proof.
      intros ι T. hnf in T.
      remember (inst G ι) as G'.
      remember (inst t ι) as t'.
      remember (inst ee ι) as ee'.
      revert HeqG' Heqt' Heqee'. revert G t ee. revert w ι.
      induction T; cbn; intros; subst.
      - apply pfalse; cbn; auto.
      - apply ptrue; cbn; auto.
      - specialize (IHT1 w ι G Ty_bool (fun _ => cnd') eq_refl eq_refl eq_refl).
        specialize (IHT2 w ι G t0      (fun _ => coq') eq_refl eq_refl eq_refl).
        specialize (IHT3 w ι G t0      (fun _ => alt') eq_refl eq_refl eq_refl).
        eapply pif; cbn; eauto; eauto.
      - apply pvar; cbn; auto.
        now rewrite resolve_inst in H.
      - specialize (IHT w ι (cons (v, lift vt _) G) (lift t _) (fun _ => e')).
        cbn in IHT. rewrite ?inst_lift in IHT.
        specialize (IHT eq_refl eq_refl eq_refl).
        eapply pabsu; cbn; eauto; rewrite ?inst_lift; eauto.
        change (@inst _ _ (@inst_sem expr) _ ?e ?ι) with (e ι); cbn.
        now rewrite inst_lift.
      - specialize (IHT w ι (cons (v, lift vt _) G) (lift t _) (fun _ => e')).
        cbn in IHT. rewrite ?inst_lift in IHT.
        specialize (IHT eq_refl eq_refl eq_refl).
        eapply pabst; cbn; eauto; rewrite ?inst_lift; eauto.
      - specialize (IHT1 w ι G (Ty_func (lift t2 _) t) (fun _ => e1')). cbn in IHT1.
        rewrite ?inst_lift in IHT1. specialize (IHT1 eq_refl eq_refl eq_refl).
        specialize (IHT2 w ι G (lift t2 _) (fun _ => e2')).
        rewrite ?inst_lift in IHT2. specialize (IHT2 eq_refl eq_refl eq_refl).
        eapply papp; cbn; eauto; rewrite ?inst_lift; eauto.
    Qed.

  End InductionScheme.

  Definition ProperPost {R} {reflR : Refl R} {instR : forall w : World, Inst (R w) (Assignment w)}
    {AT A} {persA : Persistent R AT} {instT : Inst AT A}
    {w} (Q : Box R (AT -> Pred) w) : Prop :=
    forall {w1} (r01 : R w w1) (te0 : AT w) (te1 : AT w1),
      (te1 =ₚ (persist _ te0 _ r01)) ⊢ₚ (Ext (Q w refl te0) r01 <->ₚ Q w1 r01 te1).

End Pred.
Export Pred (Pred).

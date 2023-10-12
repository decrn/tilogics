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
  Environment
  Prelude
  Stlc.Alloc
  Stlc.Instantiation
  Stlc.Persistence
  Stlc.Predicates
  Stlc.Sem
  Stlc.Spec
  Stlc.Worlds.

Import world.notations.
Import Pred Pred.notations.
Import Pred.proofmode.
Import iris.proofmode.tactics.

#[local] Notation "s [ ζ ]" :=
  (persist s ζ)
    (at level 7, left associativity,
      format "s [ ζ ]").
#[local] Set Implicit Arguments.

Class Pure (M : TYPE → TYPE) : Type :=
  pure : ∀ A, ⊧ A ⇢ M A.
#[global] Arguments pure {M _ A} [w].
Class Bind (Θ : SUB) (M : TYPE → TYPE) : Type :=
  bind : ∀ A B, ⊧ M A ⇢ Box Θ (A ⇢ M B) ⇢ M B.
#[global] Arguments bind {Θ M _ A B} [w].

Module MonadNotations.
  Notation "' x <- ma ;; mb" :=
    (bind ma (fun _ _ x => mb))
      (at level 80, x pattern, ma at next level, mb at level 200, right associativity,
        format "' x  <-  ma  ;;  mb").
  Notation "x <- ma ;; mb" :=
    (bind ma (fun _ _ x => mb))
      (at level 80, ma at next level, mb at level 200, right associativity).

  Existing Class sub.
  #[export] Existing Instance trans.
  #[export] Hint Mode sub - + - : typeclass_instances.
End MonadNotations.

Class TypeCheckM (M : TYPE -> TYPE) : Type :=
  { assert   : ⊧ Ṫy ⇢ Ṫy ⇢ M Unit;
    pick     : ⊧ M Ṫy;
    fail {A} : ⊧ M A;
  }.
#[global] Arguments fail {_ _ _ w}.
#[global] Arguments pick {_ _ w}.

Class WeakestPre (Θ : SUB) (M : TYPE -> TYPE) : Type :=
  WP [A] : ⊧ M A ⇢ Box Θ (A ⇢ Pred) ⇢ Pred.
Class WeakestLiberalPre (Θ : SUB) (M : TYPE -> TYPE) : Type :=
  WLP [A] : ⊧ M A ⇢ Box Θ (A ⇢ Pred) ⇢ Pred.

Class TypeCheckLogicM
  Θ {reflΘ : Refl Θ} {stepΘ : Step Θ} {transΘ : Trans Θ}
  M {pureM : Pure M} {bindM : Bind Θ M} {tcM : TypeCheckM M}
    {wpM : WeakestPre Θ M} {wlpM : WeakestLiberalPre Θ M} : Type :=
  { wp_pure [A w] (a : A w) (Q : Box Θ (A ⇢ Pred) w) :
      WP (pure a) Q ⊣⊢ₚ Q _ refl a;
    wp_bind [A B w0] (m : M A w0) (f : Box Θ (A ⇢ M B) w0) (Q : Box Θ (B ⇢ Pred) w0) :
      WP (bind m f) Q ⊣⊢ₚ WP m (fun w1 θ1 a => WP (f _ θ1 a) (_4 Q θ1));
    wp_assert [w] (σ τ : Ṫy w) (Q : Box Θ (Unit ⇢ Pred) w) :
      WP (assert σ τ) Q ⊣⊢ₚ σ =ₚ τ /\ₚ Q _ refl tt;
    wp_pick [w] (Q : Box Θ (Ṫy ⇢ Pred) w) :
      let α := world.fresh w in
      WP pick Q ⊣⊢ₚ Acc.wp step (Q (w ▻ α) step (ṫy.var world.in_zero));
    wp_fail [A w] (Q : Box Θ (A ⇢ Pred) w) :
      WP fail Q ⊣⊢ₚ ⊥ₚ;
    wp_mono [A w] (m : M A w) (P Q : Box Θ (A ⇢ Pred) w) :
      (∀ w1 (θ : Θ w w1) (a : A w1), Acc.wlp θ (P w1 θ a -∗ Q w1 θ a)) ⊢
      (WP m P -∗ WP m Q);

    wlp_pure [A w] (a : A w) (Q : Box Θ (A ⇢ Pred) w) :
      WLP (pure a) Q ⊣⊢ₚ Q _ refl a;
    wlp_bind [A B w0] (m : M A w0) (f : Box Θ (A ⇢ M B) w0) (Q : Box Θ (B ⇢ Pred) w0) :
      WLP (bind m f) Q ⊣⊢ₚ WLP m (fun w1 θ1 a => WLP (f _ θ1 a) (_4 Q θ1));
    wlp_assert [w] (σ τ : Ṫy w) (Q : Box Θ (Unit ⇢ Pred) w) :
      WLP (assert σ τ) Q ⊣⊢ₚ σ =ₚ τ ->ₚ Q _ refl tt;
    wlp_pick [w] (Q : Box Θ (Ṫy ⇢ Pred) w) :
      let α := world.fresh w in
      WLP pick Q ⊣⊢ₚ Acc.wlp step (Q (w ▻ α) step (ṫy.var world.in_zero));
    wlp_fail [A w] (Q : Box Θ (A ⇢ Pred) w) :
      WLP fail Q ⊣⊢ₚ ⊤ₚ;
    wlp_mono [A w] (m : M A w) (P Q : Box Θ (A ⇢ Pred) w) :
      (∀ w1 (θ : Θ w w1) (a : A w1), Acc.wlp θ (P w1 θ a -∗ Q w1 θ a)) ⊢
      (WLP m P -∗ WLP m Q);

    wp_impl [A w] (m : M A w) (P : Box Θ (A ⇢ Pred) w) (Q : Pred w) :
      (WP m P ->ₚ Q) ⊣⊢ₚ WLP m (fun w1 θ1 a1 => P w1 θ1 a1 ->ₚ Q[θ1]);
  }.
#[global] Arguments TypeCheckLogicM Θ {_ _ _} _ {_ _ _ _ _}.

Lemma wp_mono' `{TypeCheckLogicM Θ M} {A w} (m : M A w) (P Q : Box Θ (A ⇢ Pred) w) :
  (WP m P -∗ (∀ₚ w1 θ1 a1, Acc.wlp θ1 (P w1 θ1 a1 -∗ Q w1 θ1 a1)) -∗ WP m Q)%P.
Proof. iIntros "WP PQ". iRevert "WP". now iApply wp_mono. Qed.

Lemma wlp_mono' `{TypeCheckLogicM Θ M} {A w} (m : M A w) (P Q : Box Θ (A ⇢ Pred) w) :
  (WLP m P -∗ (∀ₚ w1 θ1 a1, Acc.wlp θ1 (P w1 θ1 a1 -∗ Q w1 θ1 a1)) -∗ WLP m Q)%P.
Proof. iIntros "WP PQ". iRevert "WP". now iApply wlp_mono. Qed.

Definition wp_diamond {Θ : SUB} {A} :
  ⊧ Diamond Θ A ⇢ Box Θ (A ⇢ Pred) ⇢ Pred :=
  fun w '(existT w1 (θ, a)) Q => Acc.wp θ (Q w1 θ a).

Definition wlp_diamond {Θ : SUB} {A} :
  ⊧ Diamond Θ A ⇢ Box Θ (A ⇢ Pred) ⇢ Pred :=
  fun w '(existT w1 (θ, a)) Q => Acc.wlp θ (Q w1 θ a).

Definition wp_option {A w1 w2} :
  Option A w1 -> (A w1 -> Pred w2) -> Pred w2 :=
  fun o Q =>
    match o with
    | Some a => Q a
    | None => ⊥ₚ
    end%P.

Definition wlp_option {A w1 w2} :
  Option A w1 -> (A w1 -> Pred w2) -> Pred w2 :=
  fun o Q =>
    match o with
    | Some a => Q a
    | None => ⊤ₚ
    end%P.

Section OptionDiamond.

  Definition OptionDiamond (Θ : SUB) (A : TYPE) : TYPE :=
    Option (Diamond Θ A).

  #[export] Instance wp_optiondiamond {Θ : SUB} : WeakestPre Θ (OptionDiamond Θ) :=
    fun A w m Q => wp_option m (fun d => wp_diamond d Q).
  #[global] Arguments wp_optiondiamond {Θ} {A}%indexed_scope [w] _ _%B _.
  #[global] Instance params_wp_optiondiamond : Params (@wp_optiondiamond) 5 := {}.

  #[export] Instance proper_wp_optiondiamond_bientails {Θ A w} :
    Proper
      (pointwise_relation _
         (forall_relation
            (fun _ => pointwise_relation _
                        (pointwise_relation _ (⊣⊢ₚ))) ==> (⊣⊢ₚ)))
      (@wp_optiondiamond Θ A w).
  Proof.
    intros d p q pq. destruct d as [(w1 & r01 & a)|]; cbn; [|easy].
    apply Acc.proper_wp_bientails. apply pq.
  Qed.

  #[export] Instance proper_wp_optiondiamond_entails {Θ A w} :
    Proper
      (pointwise_relation _
         (forall_relation
            (fun _ => pointwise_relation _
                        (pointwise_relation _ entails)) ==> entails))
      (@wp_optiondiamond Θ A w).
  Proof.
    intros d p q pq. destruct d as [(w1 & r01 & a)|]; cbn; [|easy].
    apply Acc.proper_wp_entails. apply pq.
  Qed.

  Lemma wp_optiondiamond_and {Θ A w} (d : OptionDiamond Θ A w)
    (P : Box Θ (A ⇢ Pred) w) (Q : Pred w) :
    WP d P /\ₚ Q ⊣⊢ₚ WP d (fun w1 θ1 a1 => P w1 θ1 a1 /\ₚ persist Q θ1).
  Proof.
    destruct d as [(w1 & θ1 & a1)|]; cbn.
    - now rewrite Acc.and_wp_l.
    - now rewrite bi.False_and.
  Qed.

  Lemma wp_optiondiamond_monotonic' {Θ A w} (d : OptionDiamond Θ A w)
    (R : Pred w) (P Q : Box Θ (A ⇢ Pred) w) :
    (forall w1 (r : Θ w w1) (a : A w1),
        persist R r ⊢ₚ P w1 r a ->ₚ Q w1 r a) ->
    R ⊢ₚ WP d P ->ₚ WP d Q.
  Proof.
    intros pq. destruct d as [(w1 & r01 & a)|]; cbn.
    - specialize (pq w1 r01 a).
      apply impl_and_adjoint.
      rewrite Acc.and_wp_r.
      apply Acc.proper_wp_entails.
      apply impl_and_adjoint.
      apply pq.
    - apply impl_and_adjoint.
      now rewrite and_false_r.
  Qed.

  #[export] Instance pure_optiondiaomd {Θ} {reflΘ : Refl Θ} :
    Pure (OptionDiamond Θ) :=
    fun A w a => Some (existT w (refl, a)).

  #[export] Instance bind_optiondiamond {Θ} {transΘ : Trans Θ} :
    Bind Θ (OptionDiamond Θ) :=
    fun A B w m f =>
      option.bind m
        (fun '(existT w1 (θ1,a1)) =>
           option.bind (f w1 θ1 a1)
             (fun '(existT w2 (θ2,b2)) =>
                Some (existT w2 (trans θ1 θ2, b2)))).

  (* Lemma wp_optiondiamond_pure {Θ} {reflΘ : Refl Θ} {lkreflΘ : LkRefl Θ} *)
  (*   {A w0} (a : A w0) (Q : Box Θ (A ⇢ Pred) w0) : *)
  (*   wp_optiondiamond (pure (M := DiamondT Θ Option) a) Q ⊣⊢ₚ Q _ refl a. *)
  (* Proof. cbn. now rewrite Acc.wp_refl. Qed. *)

  Lemma wp_optiondiamond_bind {Θ} {transΘ : Trans Θ} {lkTransΘ : LkTrans Θ}
    {A B w0} (d : OptionDiamond Θ A w0) (f : Box Θ (A ⇢ OptionDiamond Θ B) w0)
    (Q : Box Θ (B  ⇢ Pred) w0) :
    WP (bind d f) Q ⊣⊢ₚ WP d (fun w1 ζ1 a1 => WP (f w1 ζ1 a1) (_4 Q ζ1)).
  Proof.
    destruct d as [(w1 & r01 & a)|]; cbn; [|reflexivity].
    destruct (f w1 r01 a) as [(w2 & r12 & b2)|]; cbn;
      now rewrite ?Acc.wp_trans ?Acc.wp_false.
  Qed.

End OptionDiamond.

#[local] Instance instpred_diamond {Θ A} `{ipA : InstPred A} :
  InstPred (Diamond Θ A) :=
  fun w m => wp_diamond m (fun _ _ a => instpred a).
#[export] Instance instpred_optiondiamond {Θ A} `{ipA : InstPred A} :
  InstPred (OptionDiamond Θ A) :=
  fun w m => WP m (fun _ _ a => instpred a).

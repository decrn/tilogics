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
  Classes.Morphisms_Prop
(*   Lists.List *)
  Program.Tactics
  Strings.String.
(* From Equations Require Import *)
(*   Equations. *)
From stdpp Require Import
  base gmap.
From Em Require Import
  Prelude
  Shallow.Monad.Interface
  Spec.

#[local] Set Implicit Arguments.

Section Elaborate.
  Context M {mretM : MPure M} {mbindM : MBind M} {mfailM : MFail M} {tcmM : TypeCheckM M}.

  Fixpoint synth (e : Exp) (Γ : Env) : M (Ty * Exp) :=
    match e with
    | exp.var x =>
        match lookup x Γ with
        | Some t => pure (t, e)
        | None   => fail
        end
    | exp.false => pure (ty.bool, e)
    | exp.true  => pure (ty.bool, e)
    | exp.ifte e1 e2 e3 =>
        '(t1, e1') ← synth e1 Γ;
        '(t2, e2') ← synth e2 Γ;
        '(t3, e3') ← synth e3 Γ;
        equals ty.bool t1 ;;
        equals t2 t3;;
        pure (t3, exp.ifte e1' e2' e3')
    | exp.absu x e =>
        t1        ← pick;
        '(t2, e') ← synth e (Γ ,, x∷t1);
        pure (ty.func t1 t2, exp.abst x t1 e')
    | exp.abst x t1 e =>
        '(t2, e') ← synth e (Γ ,, x∷t1);
        pure (ty.func t1 t2, exp.abst x t1 e')
    | exp.app e1 e2 =>
        '(tf, e1') ← synth e1 Γ;
        '(t1, e2') ← synth e2 Γ;
        t2         ← pick;
        equals tf (ty.func t1 t2);;
        pure (t2, exp.app e1' e2')
    end.

  Context {wpM : WeakestPre M} {wlpM : WeakestLiberalPre M}
    {tclM : TypeCheckLogicM M}.

  Definition typing_algo (Γ : Env) (e : Exp) (t : Ty) (ee : Exp) : Prop :=
    WP (synth e Γ) (fun '(t',ee') => t = t' /\ ee = ee').
  Notation "Γ |--ₐ e ∷ t ~> e'" := (typing_algo Γ e t e') (at level 80).

  Goal False. Proof.
  Ltac solve_complete :=
    repeat
      (try apply wp_pure; try apply wp_fail; try apply wp_bind;
       try apply wp_equals; try (eapply wp_pick; intros; subst);
       try
         match goal with
         | H: ?x = _ |- WP match ?x with _ => _ end _ => rewrite H
         | IH: WP (synth ?e ?Γ1) _ |- WP (synth ?e ?Γ2) _ =>
             unify Γ1 Γ2; revert IH; apply wp_mono; intros; subst
         | H: _ /\ _ |- _ => destruct H; subst
         | |- _ /\ _ => split
         | |- WP match ?x with _ => _ end _ =>
             is_var x;
             match type of x with
             | prod Ty Exp => destruct x
             end
         end;
       intros; eauto).
  Abort.

  Lemma completeness (Γ : Env) (e ee : Exp) (t : Ty) :
    Γ |-- e ∷ t ~> ee  →  Γ |--ₐ e ∷ t ~> ee.
  Proof.
    unfold typing_algo.
    induction 1; cbn; solve_complete;
      try (eexists; solve_complete; fail).
  Qed.

  Goal False. Proof.
  Ltac solve_sound :=
    repeat
      (try apply wlp_pure; try apply wlp_fail; try apply wlp_bind;
       try (apply wlp_equals; intros; subst); try (apply wlp_pick; intro);
       try
         match goal with
         | IH : forall Γ, WLP (synth ?e Γ) _
                          |- WLP (synth ?e ?Γ) _ =>
             specialize (IH Γ); revert IH; apply wlp_mono; intros
         | |- tpb _ _ _ _    =>
             econstructor
           | |- WLP (match ?t with _ => _ end) _ =>
             destruct t eqn:?
         end;
       intros; eauto).
  Abort.

  Lemma soundness (Γ : Env) (e : Exp) t ee :
    Γ |--ₐ e ∷ t ~> ee  →  Γ |-- e ∷ t ~> ee.
  Proof.
    enough (WLP (synth e Γ) (fun '(t',ee') => Γ |-- e ∷ t' ~> ee')).
    { unfold typing_algo. apply wp_impl. revert H.
      apply wlp_mono. intros [t1 e1] HT [Heq1 Heq2]. now subst.
    }
    revert Γ. clear t ee.
    induction e; cbn; intros Γ; solve_sound.
  Qed.

  Lemma correctness Γ e t ee :
    Γ |-- e ∷ t ~> ee  ↔  Γ |--ₐ e ∷ t ~> ee.
  Proof. split; auto using completeness, soundness. Qed.

End Elaborate.

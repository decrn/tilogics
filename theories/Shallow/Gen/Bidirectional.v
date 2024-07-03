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
  Program.Tactics
  Strings.String.
From stdpp Require Import
  base gmap.
From Em Require Import
  Prelude
  Shallow.Monad.Interface
  Spec.

#[local] Set Implicit Arguments.

Section Elaborate.

  Fixpoint check `{MPure M, MBind M, MFail M, TypeCheckM M}
    (e : Exp) (Γ : Env) (t : Ty) : M Exp :=
    match e with
    | exp.var x =>
        match lookup x Γ with
        | Some t' => equals t t';; pure e
        | None    => fail
        end
    | exp.false => equals t ty.bool ;; pure e
    | exp.true  => equals t ty.bool ;; pure e
    | exp.ifte e1 e2 e3 =>
        e1' ← check e1 Γ ty.bool;
        e2' ← check e2 Γ t;
        e3' ← check e3 Γ t;
        pure (exp.ifte e1' e2' e3')
    | exp.absu x e =>
        t1 ← pick;
        t2 ← pick;
        _  ← equals t (ty.func t1 t2);
        e' ← check e (Γ ,, x∷t1) t2;
        pure (exp.abst x t1 e')
    | exp.abst x t1 e =>
        t2 ← pick;
        _  ← equals t (ty.func t1 t2);
        e' ← check e (Γ ,, x∷t1) t2;
        pure (exp.abst x t1 e')
    | exp.app e1 e2 =>
        '(t2,e2') ← synth e2 Γ;
        e1' ← check e1 Γ (ty.func t2 t);
        pure (exp.app e1' e2')
    end
  with synth `{MPure M, MBind M, MFail M, TypeCheckM M}
    (e : Exp) (Γ : Env) : M (Ty * Exp)%type :=
    match e with
    | exp.var x =>
        match lookup x Γ with
        | Some t => pure (t, e)
        | None   => fail
        end
    | exp.false => pure (ty.bool, e)
    | exp.true  => pure (ty.bool, e)
    | exp.ifte e1 e2 e3 =>
        e1' ← check e1 Γ ty.bool;
        '(t, e2') ← synth e2 Γ;
        e3' ← check e3 Γ t;
        pure (t, exp.ifte e1' e2' e3')
    | exp.absu x e =>
        t1        ← pick;
        '(t2, e') ← synth e (Γ ,, x∷t1);
        pure (ty.func t1 t2, exp.abst x t1 e')
    | exp.abst x t1 e =>
        '(t2, e') ← synth e (Γ ,, x∷t1);
        pure (ty.func t1 t2, exp.abst x t1 e')
    | exp.app e1 e2 =>
        '(tf, e1') ← synth e1 Γ;
        t1         ← pick;
        t2         ← pick;
        _ ← equals tf (ty.func t1 t2);
        e2' ← check e2 Γ t1;
        pure (t2, exp.app e1' e2')
    end.

  Context M {mretM : MPure M} {mbindM : MBind M} {mfailM : MFail M} {tcmM : TypeCheckM M}.
  Context {wpM : WeakestPre M} {wlpM : WeakestLiberalPre M}
    {tclM : TypeCheckLogicM M}.

  Definition typing_algo_synth (Γ : Env) (e : Exp) (t : Ty) (ee : Exp) : Prop :=
    WP (synth e Γ) (fun '(t',ee') => t = t' /\ ee = ee').
  Notation "Γ |--ₐ e ↓ t ~> e'" := (typing_algo_synth Γ e t e') (at level 75).

  Definition typing_algo_check (Γ : Env) (e : Exp) (t : Ty) (ee : Exp) : Prop :=
    WP (check e Γ t) (fun ee' => ee = ee').
  Notation "Γ |--ₐ e ↑ t ~> e'" := (typing_algo_check Γ e t e') (at level 75).

  Goal False. Proof.
  Ltac solve_complete :=
    repeat
      (try apply wp_pure; try apply wp_fail; try apply wp_bind;
       try apply wp_equals; try (eapply wp_pick; intros; subst);
       try
         match goal with
         | H: ?x = _ |- WP match ?x with _ => _ end _ => rewrite H
         | IH: WP (check ?e ?Γ1 ?t1) _ |- WP (check ?e ?Γ2 ?t2) _ =>
             unify Γ1 Γ2; unify t1 t2; revert IH; apply wp_mono; intros; subst
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
    Γ |-- e ∷ t ~> ee  →  Γ |--ₐ e ↑ t ~> ee  ∧  Γ |--ₐ e ↓ t ~> ee.
  Proof.
    unfold typing_algo_check, typing_algo_synth.
    induction 1; cbn; solve_complete.
  Qed.

  Goal False. Proof.
  Ltac solve_sound :=
    repeat
      (try apply wlp_pure; try apply wlp_fail; try apply wlp_bind;
       try (apply wlp_equals; intros; subst); try (apply wlp_pick; intro);
       try
         match goal with
         | H: _ /\ _ |- _ => destruct H
         | IH : ∀ Γ1 t1, WLP (check ?e Γ1 t1) _
           |- WLP (check ?e ?Γ2 ?t2) _ =>
             specialize (IH Γ2 t2); revert IH; apply wlp_mono; intros
         | IH : ∀ Γ, WLP (synth ?e Γ) _
           |- WLP (synth ?e ?Γ) _ =>
             specialize (IH Γ); revert IH; apply wlp_mono; intros
         | |- tpb _ _ _ _    => econstructor
         | |- WLP (match ?t with _ => _ end) _ => destruct t eqn:?
         end;
       intros; eauto).
  Abort.

  Lemma soundness_aux e :
    (∀ Γ t, WLP (check e Γ t) (fun ee => Γ |-- e ∷ t ~> ee)) ∧
    (∀ Γ,   WLP (synth e Γ) (fun '(t,ee) => Γ |-- e ∷ t ~> ee)).
  Proof.
    induction e; cbn; (split; [intros Γ ?t | intros Γ]); solve_sound.
  Qed.

  Lemma soundness_check (Γ : Env) (e : Exp) t ee :
    Γ |--ₐ e ↑ t ~> ee  →  Γ |-- e ∷ t ~> ee.
  Proof.
    unfold typing_algo_check. apply wp_impl.
    eapply wlp_mono; [| apply soundness_aux].
    intros ? ? ?; now subst.
  Qed.

  Lemma soundness_synth (Γ : Env) (e : Exp) t ee :
    Γ |--ₐ e ↓ t ~> ee  →  Γ |-- e ∷ t ~> ee.
  Proof.
    unfold typing_algo_synth. apply wp_impl.
    eapply wlp_mono; [| apply soundness_aux].
    intros [] ? []; now subst.
  Qed.

  Lemma correctness_check Γ e t ee :
    Γ |-- e ∷ t ~> ee  ↔  Γ |--ₐ e ↑ t ~> ee.
  Proof. split. apply completeness. apply soundness_check. Qed.

  Lemma correctness_synth Γ e t ee :
    Γ |-- e ∷ t ~> ee  ↔  Γ |--ₐ e ↓ t ~> ee.
  Proof. split. apply completeness. apply soundness_synth. Qed.

End Elaborate.

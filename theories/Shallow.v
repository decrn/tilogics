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
  Shallow.Interface
  Spec.

#[local] Set Implicit Arguments.

(* This module implements type inference for STLC
   using a shallow representation of constraints.
   Essentially, constraints are nothing more than propositions in Coq.
   This results in a fairly straightforward implementation,
   but one which is essentially unusable, because we cannot inspect
   the witnesses for these propositions. This is problematic,
   because these witnesses are the unified type variables
   which give the type and the elaboration of the term. *)

(* Monadic type inference for STLC is expressed as a computation inside TypeCheckM.
   Note that STLC requires unification of type variables.
   These type variables are introduced by the exists_ty computation *)

Fixpoint check (Γ : Env) (e : Exp) (t : Ty) : Prop :=
  match e with
  | exp.var x =>
      match lookup x Γ with
      | Some t' => t' = t
      | None    => False
      end
  | exp.false => t = ty.bool
  | exp.true  => t = ty.bool
  | exp.ifte e1 e2 e3 =>
      check Γ e1 ty.bool /\
      check Γ e2 t /\
      check Γ e3 t
  | exp.absu x e =>
      exists t1 t2,
        t = ty.func t1 t2 /\
        check (Γ ,, x∷t1) e t2
  | exp.abst x t1 e =>
      exists t2,
        t = ty.func t1 t2 /\
        check (Γ ,, x∷t1) e t2
  | exp.app e1 e2 =>
      exists t',
        check Γ e1 (ty.func t' t) /\
        check Γ e2 t'
  end.

Definition example_not : Exp :=
  exp.absu "x" (exp.ifte (exp.var "x") exp.false exp.true).

Definition example_cki : Exp :=
  exp.app
    (exp.absu "x" (exp.true))
    (exp.absu "y" (exp.var "y")).

Compute exists t, check empty example_not t.
Compute exists t, check empty example_cki t.

(* #[local] Notation "x <- ma ;; mb" := (bind ma (fun x => mb)) *)
(*   (at level 80, ma at next level, mb at level 200, right associativity). *)
(* #[local] Notation "ma ;; mb" := (bind ma (fun _ => mb)) *)
(*   (at level 200, mb at next level, right associativity). *)
(* #[local] Notation "' x <- ma ;; mb" := (bind ma (fun x => mb)) *)
(*   (at level 80, x pattern, ma at next level, mb at level 200, *)
(*     right associativity, format "' x  <-  ma  ;;  mb"). *)

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
        equals t1 ty.bool;;
        equals t2 t3;;
        pure (t2, exp.ifte e1' e2' e3')
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

  Definition tpb_algorithmic (Γ : Env) (e : Exp) (t : Ty) (ee : Exp) : Prop :=
    WP (synth e Γ) (fun '(t',ee') => t = t' /\ ee = ee').
  Notation "Γ |--ₐ e ∷ t ~> e'" := (tpb_algorithmic Γ e t e') (at level 80).


  Ltac solve_complete :=
    repeat
      (rewrite ?wp_pure, ?wp_bind, ?wp_fail, ?wp_equals, ?wp_pick;
       try
         match goal with
         | H: ?x = _ |- WP match ?x with _ => _ end _ => rewrite H
         | IH: WP (synth ?Γ1 ?e) _ |- WP (synth ?Γ2 ?e) _ =>
             unify Γ1 Γ2; revert IH; apply wp_mono; intros; subst
         | H: _ /\ _ |- _ => destruct H; subst
         | |- WP match ?x with _ => _ end _ =>
             is_var x;
             match type of x with
             | prod Ty Exp => destruct x
             end
         end;
       intros; eauto).

  Lemma synth_complete (Γ : Env) (e ee : Exp) (t : Ty) :
    Γ |-- e ∷ t ~> ee -> Γ |--ₐ e ∷ t ~> ee.
  Proof.
    intros T. unfold tpb_algorithmic.
    induction T; cbn.
    - solve_complete. now apply wp_pure.
    - apply wp_pure. auto.
    - apply wp_pure. auto.
    - apply wp_bind. revert IHT1. apply wp_mono.
      intros [t1 e1'']. intros []. subst.

      apply wp_bind. revert IHT2. apply wp_mono.
      intros [t2 e2'']. intros []. subst.

      apply wp_bind. revert IHT3. apply wp_mono.
      intros [t3 e3'']. intros []. subst.

      apply wp_bind, wp_equals. split; [easy|].
      apply wp_bind, wp_equals. split; [easy|].
      apply wp_pure. auto.
    - apply wp_bind.
      eapply wp_pick with t1. intros ? <-.
      apply wp_bind. revert IHT. apply wp_mono.
      intros [t3 e3'']. intros []. subst.
      apply wp_pure. auto.
    - apply wp_bind.
      revert IHT. apply wp_mono.
      intros [t3 e3'']. intros []. subst.
      apply wp_pure. auto.
    - apply wp_bind. revert IHT1. apply wp_mono.
      intros [tf e1'']. intros []. subst.
      apply wp_bind. revert IHT2. apply wp_mono.
      intros [t2' e2'']. intros []. subst.
      apply wp_bind.
      eapply wp_pick with t1. intros ? <-.
      apply wp_bind, wp_equals.
      split; auto.
      apply wp_pure; auto.
  (* Restart. *)
  (*   unfold tpb_algorithmic. *)
  (*   induction 1; cbn; solve_complete; *)
  (*     try (eexists; solve_complete; fail). *)
  Qed.

  Lemma synth_sound (Γ : Env) (e : Exp) t ee :
    (Γ |--ₐ e ∷ t ~> ee) -> (Γ |-- e ∷ t ~> ee).
  Proof.
  (*   revert Γ t ee. unfold tpb_algorithmic. *)
  (*   induction e; cbn; intros *. *)
  (*   4: { *)
  (*     apply wp_bind. admit. *)
  (*   } *)
  (* Restart. *)
    enough (WLP (synth e Γ) (fun '(t',ee') => Γ |-- e ∷ t' ~> ee')).
    { unfold tpb_algorithmic. apply wp_impl. revert H.
      apply wlp_mono. intros [t1 e1] HT [Heq1 Heq2]. now subst.
    }
    revert Γ. clear t ee.
    (* induction e; cbn; intros Γ; *)
    (*   repeat *)
    (*     (rewrite ?wlp_ret, ?wlp_bind, ?wlp_fail, ?wlp_equals, ?wlp_pick; *)
    (*      try *)
    (*        match goal with *)
    (*        | IH : forall Γ, WLP (synth Γ ?e) _ *)
    (*          |- WLP (synth ?Γ ?e) _ => *)
    (*          specialize (IH Γ); revert IH; apply wlp_mono; intros *)
    (*        | |- tpb _ _ _ _    => *)
    (*          econstructor *)
    (*        | |- ?x = ?y -> _ => *)
    (*          intro; subst *)
    (*        | |- WLP (match ?t with _ => _ end) _ => *)
    (*          destruct t eqn:? *)
    (*        end; intros; eauto). *)
  Admitted.

  Lemma synth_correct Γ e t ee :
    Γ |-- e ∷ t ~> ee <-> Γ |--ₐ e ∷ t ~> ee.
  Proof. split; auto using synth_complete, synth_sound. Qed.

End Elaborate.

Module Free.
  Inductive Free (A : Type) : Type :=
  | Ret (a : A)
  | Fail
  | Equalsk (t1 t2 : Ty) (k : Free A)
  | Pickk (f : Ty -> Free A).
  #[global] Arguments Fail {A}.

  #[export] Instance mret_free : MPure Free :=
    Ret.

  #[export] Instance mbind_free : MBind Free :=
    fun A B =>
      fix bind (m : Free A) f : Free B :=
      match m with
      | Ret a           => f a
      | Fail            => Fail
      | Equalsk t1 t2 k => Equalsk t1 t2 (bind k f)
      | Pickk g       => Pickk (fun t => bind (g t) f)
      end.

  #[export] Instance mfail_free : MFail Free :=
    fun A => Fail.

  #[export] Instance tcm_free : TypeCheckM Free :=
    {| equals t1 t2 := Equalsk t1 t2 (pure tt);
       pick         := Pickk (@pure Free _ _);
    |}.

  (* Eval vm_compute in *)
  (*   let e := exp.app (exp.abst "x" ty.bool (exp.var "x")) exp.true *)
  (*   in synth (M := Free) empty e. *)

  (* Eval vm_compute in *)
  (*   let e := exp.app (exp.absu "x" (exp.var "x")) exp.true *)
  (*   in synth (M := Free) empty e. *)

  (* Example K1 := exp.absu "k1" (exp.absu "l" (exp.var "k1")). *)
  (* Example K2 := exp.absu "k2" (exp.absu "l" (exp.var "k2")). *)
  (* Example I  := exp.absu "i" (exp.var "i"). *)

  (* Example KKI := (exp.app K1 (exp.app K2 I)). *)
  (* Eval vm_compute in *)
  (*   synth (M := Free) empty KKI. *)

  #[export] Instance wp_free : WeakestPre Free :=
    fix wp [A] (m : Free A) (Q: A -> Prop) : Prop :=
      match m with
      | Ret a           => Q a
      | Fail            => False
      | Equalsk t1 t2 k => t1 = t2 /\ wp k Q
      | Pickk f         => exists t, wp (f t) Q
      end.

  #[export] Instance wlp_free : WeakestLiberalPre Free :=
    fix wlp [A] (m : Free A) (Q: A -> Prop) : Prop :=
      match m with
      | Ret a           => Q a
      | Fail            => True
      | Equalsk t1 t2 k => t1 = t2 -> wlp k Q
      | Pickk f         => forall t, wlp (f t) Q
      end.

  #[export] Instance tcl_free: TypeCheckLogicM Free.
  Proof.
    constructor; try (induction m; cbn; firstorder; fail); auto.
    - cbn. intros. exists τ. auto.
  Qed.

End Free.

Module FromWitness.
  Import Free.

  (* WP but in Type instead of Prop *)
  Fixpoint gen [A : Type] (m : Free A) : Type :=
    match m with
    | Ret a => unit (* equiv. True in Prop *)
    | Equalsk t1 t2 k => (t1 = t2) * gen k
    | Fail => Empty_set (* equiv. False in Prop *)
    | Pickk f => { τ : Ty & gen (f τ)}
    end%type.

  (* Generates an A from a constraint m and its proof *)
  Fixpoint extract {A} (m : Free A) {struct m} : gen m -> A :=
    match m return gen m -> A with
    | Ret a           => fun _ => a
    | Fail            => fun P => match P with end
    | Equalsk t1 t2 k => fun P => extract k (snd P)
    | Pickk f       => fun P => let (t, Q) := P in
                                  extract (f t) Q
    end.

  Lemma test (τ : Ty) :
    let e := exp.app
               (exp.absu "x" (exp.var "x"))
               (exp.absu "y" (exp.var "y")) in
    gen (synth e empty).
  Proof.
    repeat eexists; eauto.
    Unshelve.
    exact τ.
  Defined.

  (* Eval vm_compute in fun t => extract _ (test t). *)

End FromWitness.

(* Module Unused. *)
(*   Import Prelude.option. *)

(*   Lemma unused_wp_match {A B} (m : option B) S N Q : *)
(*     @wp A *)
(*       match m with *)
(*       | Some x => S x *)
(*       | None => N *)
(*       end Q <-> match m with *)
(*                 | Some x => @wp A (S x) Q *)
(*                 | None   => @wp A N Q *)
(*                 end. *)
(*   Proof. now destruct m. Qed. *)

(*   Lemma unused_typing_inversion {Γ e t ee} : *)
(*     Γ |-- e ∷ t ~> ee <-> *)
(*     match e with *)
(*     | exp.true          => *)
(*         t = ty.bool /\ *)
(*         ee = exp.true *)
(*     | exp.false         => *)
(*         t = ty.bool /\ *)
(*         ee = exp.false *)
(*     | exp.ifte e1 e2 e3 => *)
(*         exists e1' e2' e3', *)
(*         exp.ifte e1' e2' e3' = ee /\ *)
(*         Γ |-- e1 ∷ ty.bool ~> e1' /\ *)
(*         Γ |-- e2 ∷ t ~> e2' /\ *)
(*         Γ |-- e3 ∷ t ~> e3' *)
(*     | exp.var x => *)
(*         exp.var x = ee /\ *)
(*         lookup x Γ = Some t *)
(*     | exp.absu x e1 => *)
(*         exists e1' t1 t2, *)
(*         ty.func t1 t2 = t /\ *)
(*         exp.abst x t1 e1' = ee /\ *)
(*         Γ ,, x∷t1 |-- e1 ∷ t2 ~> e1' *)
(*     | exp.abst x t1 e1 => *)
(*         exists e1' t2, *)
(*         ty.func t1 t2 = t /\ *)
(*         exp.abst x t1 e1' = ee /\ *)
(*         Γ ,, x∷t1 |-- e1 ∷ t2 ~> e1' *)
(*     | exp.app e1 e2 => *)
(*         exists e1' e2' t1, *)
(*         exp.app e1' e2' = ee /\ *)
(*         Γ |-- e1 ∷ ty.func t1 t ~> e1' /\ *)
(*         Γ |-- e2 ∷ t1 ~> e2' *)
(*     end. *)
(*   Proof. *)
(*     split; intros HT. *)
(*     - destruct HT; firstorder. admit. *)
(*     - destruct e; destruct_conjs; subst; try econstructor; eauto. *)
(*   Qed. *)

(* End Unused. *)

(* Module Old. *)
(*   Fixpoint gensem (G : Env) (e : Exp) (t : Ty) : Prop := *)
(*     match e with *)
(*     | exp.true  => t = ty.bool *)
(*     | exp.false => t = ty.bool *)
(*     | exp.ifte cnd coq alt => *)
(*         gensem G cnd ty.bool /\ *)
(*         gensem G coq t    /\ *)
(*         gensem G alt t *)
(*     | exp.var var => *)
(*         match (lookup var G) with *)
(*         | None => False *)
(*         | Some t' => t = t' *)
(*         end *)
(*     | exp.app e1 e2 => *)
(*         exists t2, *)
(*         gensem G e1 (ty.func t2 t) /\ *)
(*         gensem G e2 t2 *)
(*     | exp.absu var e => *)
(*         exists t_e t_var, *)
(*         gensem (G ,, var ∷ t_var) e t_e /\ *)
(*         t = (ty.func t_var t_e) *)
(*     | exp.abst var t_var e => *)
(*         exists t_e, *)
(*         gensem (G ,, var ∷ t_var) e t_e /\ *)
(*         t = (ty.func t_var t_e) *)
(*     end. *)

(*   Lemma gensem_correct (e : Exp) (G : Env) (t : Ty) : *)
(*     gensem G e t <-> exists e', G |-- e ∷ t ~> e'. *)
(*   Proof. *)
(*     split. *)
(*     - revert G t. induction e; cbn; intros; destruct_conjs; subst; *)
(*         repeat *)
(*           match goal with *)
(*           | [IH: forall G t, gensem G ?e t -> _, H: gensem _ ?e _ |- _] => *)
(*               specialize (IH _ _ H); destruct_conjs *)
(*           end. *)
(*       + destruct lookup eqn:?; [|easy]. *)
(*         subst. econstructor. econstructor. auto. *)
(*       + eexists. econstructor. *)
(*       + eexists. econstructor. *)
(*       + eexists. econstructor; eauto. *)
(*       + eexists. econstructor; eauto. *)
(*       + eexists. econstructor; eauto. *)
(*       + eexists. econstructor; eauto. *)
(*     - intros [e' T]. induction T; cbn; auto; try (firstorder; fail). *)
(*       rewrite H; auto. *)
(*   Qed. *)

(*   Example ex_gensem1 : *)
(*     gensem empty (exp.app (exp.absu "x" (exp.var "x")) exp.false) ty.bool. *)
(*   Proof. *)
(*     compute. repeat eexists. *)
(*   Qed. *)

(*   Example ex_gensem2 : *)
(*   gensem empty (exp.app (exp.absu "x" (exp.true)) (exp.absu "x" (exp.var "x"))) ty.bool. *)
(*   Proof. *)
(*     compute. repeat eexists. *)
(*     Unshelve. apply ty.bool. *)
(*   Qed. *)

(* End Old. *)

Module Prenex.

  Inductive Prenex (A : Type) : Type :=
  | Ret (a : A)
  | Fail
  | Pickk (f : Ty -> Prenex A).
  #[global] Arguments Fail {A}.

  Definition map {A B} (f : A -> B) : Prenex A -> Prenex B :=
    fix map (m : Prenex A) :=
      match m with
      | Ret a     => Ret (f a)
      | Fail      => Fail
      | Pickk g => Pickk (fun t => map (g t))
      end.

  Fixpoint prenex {A} (m : Free.Free A) : Prenex (list (Ty * Ty) * A) :=
    match m with
    | Free.Ret a           => Ret ([], a)
    | Free.Fail            => Fail
    | Free.Equalsk t1 t2 k => map
                                (fun '(eqs,a) => (cons (t1,t2) eqs, a))
                                (prenex k)
    | Free.Pickk f => Pickk (fun t => prenex (f t))
    end.

End Prenex.

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
  Prelude Stlc.Spec.

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
Class TypeCheckM (M : Type -> Type) {mretM : MRet M} {mbindM : MBind M} : Type :=
  MkTcM
    { assert (t1 t2 : Ty) : M unit;
      fail {A} : M A;
      choose : M Ty;
    }.
#[global] Arguments TypeCheckM M {_ _}.

Class TypeCheckLogic (M : Type -> Type) {mretM : MRet M} {mbindM : MBind M}
  {tcmM : TypeCheckM M} : Type :=
  { (* WP / Total correctness *)
    wp [A] (m : M A) (P : A -> Prop) : Prop;
    wp_ret {A} (a : A) (Q : A -> Prop) :
      wp (mret a) Q <-> Q a;
    wp_bind {A B} (f : A -> M B) (m : M A) (Q : B -> Prop) :
      wp (mbind f m) Q <-> wp m (fun a => wp (f a) Q);
    wp_fail {A} (Q : A -> Prop) :
      wp fail Q <-> False;
    wp_assert (t1 t2 : Ty) (Q : unit -> Prop) :
      wp (assert t1 t2) Q <-> t1 = t2 /\ Q tt;
    wp_choose (Q : Ty -> Prop) :
      wp choose Q <-> exists t, Q t;
    wp_mono {A} (P Q : A -> Prop) (m : M A) :
      (forall a, P a -> Q a) -> wp m P -> wp m Q;

    (* WLP / Partial correctness *)
    wlp [A] (m : M A) (P : A -> Prop) : Prop;
    wlp_ret {A} (a : A) (Q : A -> Prop) :
      wlp (mret a) Q <-> Q a ;
    wlp_bind {A B} (f : A -> M B) (m : M A) (Q : B -> Prop) :
      wlp (mbind f m) Q <-> wlp m (fun a => wlp (f a) Q);
    wlp_fail {A} (Q : A -> Prop) :
      wlp fail Q <-> True;
    wlp_assert (t1 t2 : Ty) (Q : unit -> Prop) :
      wlp (assert t1 t2) Q <-> (t1 = t2 -> Q tt);
    wlp_choose (Q : Ty -> Prop) :
      wlp choose Q <-> forall t, Q t;
    wlp_mono {A} (P Q : A -> Prop) (m : M A) :
      (forall a, P a -> Q a) -> wlp m P -> wlp m Q;

    wp_impl_wlp {A} (m : M A) (P : A -> Prop) (Q : Prop) :
      (wp m P -> Q) <-> wlp m (fun a => P a -> Q);
  }.
#[global ]Arguments TypeCheckLogic M {_ _ _}.

(* #[local] Notation "x <- ma ;; mb" := (bind ma (fun x => mb)) *)
(*   (at level 80, ma at next level, mb at level 200, right associativity). *)
(* #[local] Notation "ma ;; mb" := (bind ma (fun _ => mb)) *)
(*   (at level 200, mb at next level, right associativity). *)
(* #[local] Notation "' x <- ma ;; mb" := (bind ma (fun x => mb)) *)
(*   (at level 80, x pattern, ma at next level, mb at level 200, *)
(*     right associativity, format "' x  <-  ma  ;;  mb"). *)

Section Elaborate.
  Context `{tcmM : TypeCheckM M}.

  Fixpoint elab (Γ : Env) (e : Exp) : M (Ty * Exp) :=
    match e with
    | exp.var x =>
        match lookup x Γ with
        | Some t => mret (t, e)
        | None   => fail
        end
    | exp.false => mret (ty.bool, e)
    | exp.true  => mret (ty.bool, e)
    | exp.ifte e1 e2 e3 =>
        '(t1, e1') ← elab Γ e1;
        '(t2, e2') ← elab Γ e2;
        '(t3, e3') ← elab Γ e3;
        assert t1 ty.bool;;
        assert t2 t3;;
        mret (t2, exp.ifte e1' e2' e3')
    | exp.absu x e =>
        t1        ← choose;
        '(t2, e') ← elab (Γ ,, x∷t1) e;
        mret (ty.func t1 t2, exp.abst x t1 e')
    | exp.abst x t1 e =>
        '(t2, e') ← elab (Γ ,, x∷t1) e;
        mret (ty.func t1 t2, exp.abst x t1 e')
    | exp.app e1 e2 =>
        '(tf, e1') ← elab Γ e1;
        '(t1, e2') ← elab Γ e2;
        t2         ← choose;
        assert tf (ty.func t1 t2);;
        mret (t2, exp.app e1' e2')
    end.

  Context {tclM : TypeCheckLogic M}.

  Definition tpb_algorithmic (Γ : Env) (e : Exp) (t : Ty) (ee : Exp) : Prop :=
    wp (elab Γ e) (fun '(t',ee') => t = t' /\ ee = ee').
  Notation "Γ |--ₐ e ∷ t ~> e'" := (tpb_algorithmic Γ e t e') (at level 80).

  Lemma elab_sound (Γ : Env) (e : Exp) t ee :
    (Γ |--ₐ e ∷ t ~> ee) -> (Γ |-- e ∷ t ~> ee).
  Proof.
    enough (wlp (elab Γ e) (fun '(t',ee') => Γ |-- e ∷ t' ~> ee')).
    { unfold tpb_algorithmic. apply wp_impl_wlp. revert H.
      apply wlp_mono. intros [t1 e1] HT [Heq1 Heq2]. now subst.
    }
    revert Γ. clear t ee.
    induction e; cbn; intros Γ;
      repeat
        (rewrite ?wlp_ret, ?wlp_bind, ?wlp_fail, ?wlp_assert, ?wlp_choose;
         try
           match goal with
           | IH : forall Γ, wlp (elab Γ ?e) _
             |- wlp (elab ?Γ ?e) _ =>
             specialize (IH Γ); revert IH; apply wlp_mono; intros
           | |- tpb _ _ _ _    =>
             econstructor
           | |- ?x = ?y -> _ =>
             intro; subst
           | |- wlp (match ?t with _ => _ end) _ =>
             destruct t eqn:?
           end; intros; eauto).
  Qed.

  Ltac solve_complete :=
    repeat
      (rewrite ?wp_ret, ?wp_bind, ?wp_fail, ?wp_assert, ?wp_choose;
       try
         match goal with
         | H: ?x = _ |- wp match ?x with _ => _ end _ => rewrite H
         | IH: wp (elab ?Γ1 ?e) _ |- wp (elab ?Γ2 ?e) _ =>
             unify Γ1 Γ2; revert IH; apply wp_mono; intros; subst
         | H: _ /\ _ |- _ => destruct H; subst
         | |- wp match ?x with _ => _ end _ =>
             is_var x;
             match type of x with
             | prod Ty Exp => destruct x
             end
         end;
       intros; eauto).

  Lemma elab_complete (Γ : Env) (e ee : Exp) (t : Ty) :
    Γ |-- e ∷ t ~> ee -> Γ |--ₐ e ∷ t ~> ee.
  Proof.
    unfold tpb_algorithmic.
    induction 1; cbn; solve_complete;
      try (eexists; solve_complete; fail).
  Qed.

  Lemma elab_correct Γ e t ee :
    Γ |-- e ∷ t ~> ee <-> Γ |--ₐ e ∷ t ~> ee.
  Proof. split; auto using elab_complete, elab_sound. Qed.

End Elaborate.

Module Free.
  Inductive Free (A : Type) : Type :=
  | Ret (a : A)
  | Fail
  | Assertk (t1 t2 : Ty) (k : Free A)
  | Choosek (f : Ty -> Free A).
  #[global] Arguments Fail {A}.

  #[export] Instance mret_free : MRet Free :=
    Ret.

  #[export] Instance mbind_free : MBind Free :=
    fun A B f =>
      fix bind (m : Free A) : Free B :=
      match m with
      | Ret a           => f a
      | Fail            => Fail
      | Assertk t1 t2 k => Assertk t1 t2 (bind k)
      | Choosek g       => Choosek (fun t => bind (g t))
      end.

  #[export] Instance tcm_free : TypeCheckM Free :=
    {| assert t1 t2 := Assertk t1 t2 (mret tt);
       fail A       := Fail;
       choose       := Choosek mret;
    |}.

  (* Eval vm_compute in *)
  (*   let e := exp.app (exp.abst "x" ty.bool (exp.var "x")) exp.true *)
  (*   in elab (M := Free) empty e. *)

  (* Eval vm_compute in *)
  (*   let e := exp.app (exp.absu "x" (exp.var "x")) exp.true *)
  (*   in elab (M := Free) empty e. *)

  (* Example K1 := exp.absu "k1" (exp.absu "l" (exp.var "k1")). *)
  (* Example K2 := exp.absu "k2" (exp.absu "l" (exp.var "k2")). *)
  (* Example I  := exp.absu "i" (exp.var "i"). *)

  (* Example KKI := (exp.app K1 (exp.app K2 I)). *)
  (* Eval vm_compute in *)
  (*   elab (M := Free) empty KKI. *)

  Fixpoint wp [A] (m : Free A) (Q: A -> Prop) : Prop :=
    match m with
    | Ret a           => Q a
    | Fail            => False
    | Assertk t1 t2 k => t1 = t2 /\ wp k Q
    | Choosek f       => exists t, wp (f t) Q
    end.

  Fixpoint wlp [A] (m : Free A) (Q: A -> Prop) : Prop :=
    match m with
    | Ret a           => Q a
    | Fail            => True
    | Assertk t1 t2 k => t1 = t2 -> wlp k Q
    | Choosek f       => forall t, wlp (f t) Q
    end.

  #[export] Instance tcl_free: TypeCheckLogic Free.
  Proof.
    refine {| Shallow.wp := wp; Shallow.wlp := wlp; |};
      try reflexivity; try (induction m; cbn; firstorder; fail).
    - induction m; cbn; firstorder. apply H. firstorder.
  Qed.

End Free.

Module FromWitness.
  Import Free.

  (* WP but in Type instead of Prop *)
  Fixpoint gen [A : Type] (m : Free A) : Type :=
    match m with
    | Ret a => unit (* equiv. True in Prop *)
    | Assertk t1 t2 k => (t1 = t2) * gen k
    | Fail => Empty_set (* equiv. False in Prop *)
    | Choosek f => { τ : Ty & gen (f τ)}
    end%type.

  (* Generates an A from a constraint m and its proof *)
  Fixpoint extract {A} (m : Free A) {struct m} : gen m -> A :=
    match m return gen m -> A with
    | Ret a           => fun _ => a
    | Fail            => fun P => match P with end
    | Assertk t1 t2 k => fun P => extract k (snd P)
    | Choosek f       => fun P => let (t, Q) := P in
                                  extract (f t) Q
    end.

  Lemma test (τ : Ty) :
    let e := exp.app
               (exp.absu "x" (exp.var "x"))
               (exp.absu "y" (exp.var "y")) in
    gen (elab empty e).
  Proof.
    repeat eexists; eauto.
    Unshelve.
    exact τ.
  Defined.

  (* Eval vm_compute in fun t => extract _ (test t). *)

End FromWitness.

Module Unused.
  Import Prelude.option.

  Lemma unused_wp_match {A B} (m : option B) S N Q :
    @wp A
      match m with
      | Some x => S x
      | None => N
      end Q <-> match m with
                | Some x => @wp A (S x) Q
                | None   => @wp A N Q
                end.
  Proof. now destruct m. Qed.

  Lemma unused_typing_inversion {Γ e t ee} :
    Γ |-- e ∷ t ~> ee <->
    match e with
    | exp.true          =>
        t = ty.bool /\
        ee = exp.true
    | exp.false         =>
        t = ty.bool /\
        ee = exp.false
    | exp.ifte e1 e2 e3 =>
        exists e1' e2' e3',
        exp.ifte e1' e2' e3' = ee /\
        Γ |-- e1 ∷ ty.bool ~> e1' /\
        Γ |-- e2 ∷ t ~> e2' /\
        Γ |-- e3 ∷ t ~> e3'
    | exp.var x =>
        exp.var x = ee /\
        lookup x Γ = Some t
    | exp.absu x e1 =>
        exists e1' t1 t2,
        ty.func t1 t2 = t /\
        exp.abst x t1 e1' = ee /\
        Γ ,, x∷t1 |-- e1 ∷ t2 ~> e1'
    | exp.abst x t1 e1 =>
        exists e1' t2,
        ty.func t1 t2 = t /\
        exp.abst x t1 e1' = ee /\
        Γ ,, x∷t1 |-- e1 ∷ t2 ~> e1'
    | exp.app e1 e2 =>
        exists e1' e2' t1,
        exp.app e1' e2' = ee /\
        Γ |-- e1 ∷ ty.func t1 t ~> e1' /\
        Γ |-- e2 ∷ t1 ~> e2'
    end.
  Proof.
    split; intros HT.
    - destruct HT; firstorder.
    - destruct e; destruct_conjs; subst; try econstructor; eauto.
  Qed.

End Unused.

Module Old.
  Fixpoint gensem (G : Env) (e : Exp) (t : Ty) : Prop :=
    match e with
    | exp.true  => t = ty.bool
    | exp.false => t = ty.bool
    | exp.ifte cnd coq alt =>
        gensem G cnd ty.bool /\
        gensem G coq t    /\
        gensem G alt t
    | exp.var var =>
        match (lookup var G) with
        | None => False
        | Some t' => t = t'
        end
    | exp.app e1 e2 =>
        exists t2,
        gensem G e1 (ty.func t2 t) /\
        gensem G e2 t2
    | exp.absu var e =>
        exists t_e t_var,
        gensem (G ,, var ∷ t_var) e t_e /\
        t = (ty.func t_var t_e)
    | exp.abst var t_var e =>
        exists t_e,
        gensem (G ,, var ∷ t_var) e t_e /\
        t = (ty.func t_var t_e)
    end.

  Lemma gensem_correct (e : Exp) (G : Env) (t : Ty) :
    gensem G e t <-> exists e', G |-- e ∷ t ~> e'.
  Proof.
    split.
    - revert G t. induction e; cbn; intros; destruct_conjs; subst;
        repeat
          match goal with
          | [IH: forall G t, gensem G ?e t -> _, H: gensem _ ?e _ |- _] =>
              specialize (IH _ _ H); destruct_conjs
          end.
      + destruct lookup eqn:?; [|easy].
        subst. econstructor. econstructor. auto.
      + eexists. econstructor.
      + eexists. econstructor.
      + eexists. econstructor; eauto.
      + eexists. econstructor; eauto.
      + eexists. econstructor; eauto.
      + eexists. econstructor; eauto.
    - intros [e' T]. induction T; cbn; auto; try (firstorder; fail).
      rewrite H; auto.
  Qed.

  Example ex_gensem1 :
    gensem empty (exp.app (exp.absu "x" (exp.var "x")) exp.false) ty.bool.
  Proof.
    compute. repeat eexists.
  Qed.

  Example ex_gensem2 :
  gensem empty (exp.app (exp.absu "x" (exp.true)) (exp.absu "x" (exp.var "x"))) ty.bool.
  Proof.
    compute. repeat eexists.
    Unshelve. apply ty.bool.
  Qed.

End Old.

Module Prenex.

  Inductive Prenex (A : Type) : Type :=
  | Ret (a : A)
  | Fail
  | Choosek (f : Ty -> Prenex A).
  #[global] Arguments Fail {A}.

  Definition map {A B} (f : A -> B) : Prenex A -> Prenex B :=
    fix map (m : Prenex A) :=
      match m with
      | Ret a     => Ret (f a)
      | Fail      => Fail
      | Choosek g => Choosek (fun t => map (g t))
      end.

  Fixpoint prenex {A} (m : Free.Free A) : Prenex (list (Ty * Ty) * A) :=
    match m with
    | Free.Ret a           => Ret ([], a)
    | Free.Fail            => Fail
    | Free.Assertk t1 t2 k => map
                                (fun '(eqs,a) => (cons (t1,t2) eqs, a))
                                (prenex k)
    | Free.Choosek f => Choosek (fun t => prenex (f t))
    end.

End Prenex.

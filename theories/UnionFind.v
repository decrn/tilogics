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
  Arith.PeanoNat
  Relations.Relation_Definitions
  Relations.Relation_Operators
  Wellfounded.Transitive_Closure
  Wellfounded.Wellfounded.
From Equations Require Import
  Equations.
From Em Require Import
  Definitions
  Environment
  Context
  Predicates
  Prelude
  STLC
  Triangular.

Import ctx.notations.
Import SigTNotations.
Import World.notations.

Set Implicit Arguments.

#[local] Arguments Ty_hole {Σ i} xIn.
#[local] Arguments Ty_bool {Σ}.
#[local] Arguments Ty_func {Σ}.
#[local] Open Scope indexed_scope.

Ltac folddefs :=
  repeat
    match goal with
    | H: context[@Tri.refl ?w] |- _ =>
        change_no_check (@Tri.refl w) with (@refl Tri _ w) in H
    | |- context[@Tri.refl ?w] =>
        change_no_check (@Tri.refl w) with (@refl Tri _ w)
    | |- context[Tri.cons ?x ?t ?r] =>
        change_no_check (Tri.cons x t r) with (thick x t ⊙⁻ r)
    end.

Module DS.

  Definition rank := nat.

  Definition Ref : TYPE :=
    fun w => { x & x ∈ w }.

  #[export] Instance persistent_ref : Persistent Alloc Ref.
  Proof.
    intros w0 [x xIn] w1 r.
    refine (x; persist _ xIn _ r).
  Defined.

  Set Equations With UIP.
  Lemma persist_ref_step_inj {w x} (r1 r2 : Ref w) :
    persist w r1 (w ▻ x) step = persist w r2 (w ▻ x) step ->
    r1 = r2.
  Proof.
    destruct r1, r2. cbn. intros.
    remember (ctx.in_succ i).
    remember (ctx.in_succ i0).
    dependent elimination H.
    f_equal. subst.
    now dependent elimination Heqi2.
  Qed.

  Definition IsRepr {w} (f : Ref w -> Ref w) (x : Ref w) : Prop :=
    f x = x.

  Record DS (A : TYPE) (w : World) : Type :=
    { find : Ref w -> Ref w;
      cont : forall x : Ref w, IsRepr find x -> A w;
      find_isrepr :
        forall x : Ref w, IsRepr find (find x);
    }.
  #[global] Arguments cont [A]%indexed_scope [w]%ctx_scope d x _.

  Definition equiv {A} : ⊢ DS A -> Ref -> Ref -> Const bool :=
    fun w d x y =>
      if eq_dec (find d x) (find d y)
      then true else false.

  Definition get {A} : ⊢ DS A -> Ref -> A :=
    fun w d x => cont d (find d x) (find_isrepr d x).

  Definition set {A} : ⊢ DS A -> Ref -> A -> DS A :=
    fun w d x a =>
      {| find        := find d;
         cont r rr   := if equiv d r x then a else cont d r rr;
         find_isrepr := find_isrepr d;
      |}.

  Definition mergeFind :
    ⊢ (Ref -> Ref) -> Ref -> Ref -> Ref -> Ref :=
    fun w fnd x y z =>
      (* Map every z that previously is equivalent to y to x instead *)
      if eq_dec (fnd y) (fnd z) then fnd x else fnd z.

  Definition mergeCont {A : TYPE} :
    ⊢ (A -> A -> A) -> DS A -> Ref -> Ref -> Ref -> A :=
    fun w f d x y z =>
      if equiv d y z
      then (* In this case z was (potentially) retargeted to x. Combine the two
              values of the representatives with [f].
              TODO: In case, x and y were already in the same equivalence class
                    we still call [f]. Is this problematic? *)
           f (get d x) (get d y)
      else get d z.

  Program Definition merge {A : TYPE} :
    ⊢ (A -> A -> A) -> DS A -> Ref -> Ref -> DS A :=
    fun w f d x y =>
      {| find          := mergeFind (find d) x y;
         cont z _      := mergeCont f d x y z;
         find_isrepr z := _;
      |}.
  Next Obligation.
    unfold mergeFind, IsRepr, equiv. intros A w _ d x y z.
    destruct (eq_dec (find d y) (find d z));
      rewrite (find_isrepr d);
      destruct eq_dec; congruence.
  Qed.

  Definition measure {w} (fnd : Ref w -> Ref w) (r : Ref w) : bool :=
    if eq_dec (fnd r) r then true else false.

  Fixpoint lessthan {w} : forall (f g : Ref w -> bool), Prop :=
    match w with
    | ctx.nil      => fun _ _ => False
    | ctx.snoc w b =>
        fun f g =>
          symprod bool (Ref w -> bool) Bool.lt (@lessthan w)
            (f (b; ctx.in_zero), fun '(x;xIn) => f (x; ctx.in_succ xIn))
            (g (b; ctx.in_zero), fun '(x;xIn) => g (x; ctx.in_succ xIn))
    end.

  Lemma wf_bool_lt : well_founded Bool.lt.
  Proof.
    intros b.
    constructor; intros []; cbn; [intros []|intros ->].
    constructor; intros [] ?; [contradiction|discriminate].
  Qed.

  Lemma lessthan_wellfounded {w} : well_founded (lessthan (w:=w)).
  Proof.
    induction w; cbn.
    - hnf. intros f. constructor. intros g. intros [].
    - auto using wf_inverse_image, wf_symprod, wf_bool_lt.
  Qed.

  Lemma mergeFind_lt {w} (fnd : Ref w -> Ref w)
    (x y : Ref w) (H : fnd x <> fnd y) :
    lessthan (measure (mergeFind fnd x y)) (measure fnd).
  Proof. Admitted.

  Lemma refl {A w} (d : DS A w) (x : Ref w) :
    equiv d x x = true.
  Proof. unfold equiv. now rewrite eq_dec_refl. Qed.

  Lemma sym {A w} (d : DS A w) (x y : Ref w) :
    equiv d x y = true ->
    equiv d x y = true.
  Proof. unfold equiv. now destruct eq_dec. Qed.

  Lemma trans {A w} (d : DS A w) (x y z : Ref w) :
    equiv d x y = true ->
    equiv d y z = true ->
    equiv d x z = true.
  Proof. unfold equiv. destruct eq_dec; [rewrite e|]; easy. Qed.

  Lemma equiv_union {A w} (f : A w -> A w -> A w)
    (d : DS A w) (x y : Ref w) :
    equiv (merge f d x y) x y = true.
  Proof.
    unfold equiv, merge, mergeFind, equiv; cbn.
    rewrite eq_dec_refl.
    destruct (eq_dec (find d y) (find d x));
      now rewrite eq_dec_refl.
  Qed.

  Lemma equiv_monotone {A w} (f : A w -> A w -> A w)
    (d : DS A w) (x y u v : Ref w) :
    equiv d x y               = true ->
    equiv (merge f d u v) x y = true.
  Proof.
    unfold merge, mergeFind, equiv; cbn.
    destruct (eq_dec (find d x) (find d y)); cbn; [intros _|easy].
    rewrite e. clear x e.
    destruct (eq_dec (find d v) (find d y)); cbn;
      now rewrite eq_dec_refl.
  Qed.

  Definition compatible : ⊢ DS (Option TyF) -> Pred :=
    fun w d =>
      Pred.Forall
        (fun x : Ref w =>
           match get d x with
           | Some t => Pred.eqₚ (Ty_hole x.2) (inj _ t)
           | None   => Pred.Trueₚ
           end).

  Definition StateT (S : TYPE) (M : TYPE -> TYPE) (A : TYPE) : TYPE :=
    S -> M (Prod A S).

  Definition Id (A : TYPE) : TYPE := A.

  Definition Cont (R : ACC) (P A : TYPE) : TYPE :=
    Box R (A -> P) -> P.

  Definition M := StateT (DS (Option TyF)) Option.

  Definition pure {A} : ⊢ A -> M A.
  Admitted.

  Definition fail {A} : ⊢ M A.
  Admitted.
  #[global] Arguments fail {A w}.

  Definition bind {A B} : ⊢ M A -> (A -> M B) -> M B.
  Admitted.

  Definition flex : ⊢ Ref -> TyF -> M Unit.
  Proof.
    intros w x t. intros s.
    destruct (get s x).
  Admitted.

  Definition WP {A} : ⊢ StateT (DS (Option TyF)) Id A -> Cont Alloc Pred A :=
    fun w m k =>
       Pred.Forall
         (fun s =>
            Pred.implₚ
              (compatible s)
              (let (a, s') := m s in
               Pred.andₚ (compatible s') (k w Definitions.refl a))).

End DS.

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

From Coq Require Import Strings.String.
From stdpp Require Import base gmap.
From Em Require Import Environment Prelude Spec Worlds.

Import world.notations.

#[local] Set Implicit Arguments.

Class Persistent (A : TYPE) : Type :=
  persist : forall {Θ}, ⊧ A ⇢ Box Θ A.
#[global] Arguments persist {_ _ _} [w] _ [_] _.

#[export] Instance persist_ty : Persistent Ṫy :=
  fun Θ =>
    fix pers {w0} (t : Ṫy w0) {w1} θ : Ṫy w1 :=
      match t with
      | ṫy.var αIn    => lk θ αIn
      | ṫy.bool       => ṫy.bool
      | ṫy.func t1 t2 => ṫy.func (pers t1 θ) (pers t2 θ)
      end.

#[export] Instance persist_env : Persistent Ėnv.
Proof.
  intros Θ w0 Γ w1 θ. revert Γ.
  unfold Ėnv. eapply base.fmap.
  intros t. apply (persist t θ).
Defined.

Class LkRefl (Θ : SUB) (reflΘ : Refl Θ) : Prop :=
  lk_refl w α (αIn : α ∈ w) :
    lk refl αIn = ṫy.var αIn.
#[global] Arguments LkRefl Θ {_}.
Class LkTrans (Θ : SUB) (transΘ : Trans Θ) : Prop :=
  lk_trans w0 w1 w2 (θ1 : Θ w0 w1) (θ2 : Θ w1 w2) α (αIn : α ∈ w0) :
    lk (trans θ1 θ2) αIn = persist (lk θ1 αIn) θ2.
#[global] Arguments LkRefl Θ {_}.
#[global] Arguments LkTrans Θ {_}.

Class LkHMap (Θ1 Θ2 : SUB) (hmapΘ : HMap Θ1 Θ2) : Prop :=
  lk_hmap [w1 w2] (θ : Θ1 w1 w2) :
    ∀ α (αIn : α ∈ w1), lk (hmap θ) αIn = lk θ αIn.
#[global] Arguments LkHMap Θ1 Θ2 {_}.

Class PersistLaws A {persA : Persistent A} : Type :=
  { persist_refl {Θ} {reflΘ : Refl Θ} {lkreflΘ : LkRefl Θ} :
      forall w (a : A w),
        persist a (refl (Θ := Θ)) = a;
    persist_trans {Θ : SUB} {transΘ : Trans Θ} {lktransΘ : LkTrans Θ} :
      forall w0 (a : A w0) w1 (θ1 : Θ w0 w1) w2 (θ2 : Θ w1 w2),
        persist a (trans θ1 θ2) = persist (persist a θ1) θ2;
    persist_simulation {Θ1 Θ2 : SUB} :
      forall w0 a w1 (θ1 : Θ1 w0 w1) (θ2 : Θ2 w0 w1),
        (forall α (αIn : α ∈ w0), lk θ1 αIn = lk θ2 αIn) ->
        persist a θ1 = persist a θ2;
  }.
#[global] Arguments PersistLaws A {_}.

#[export] Instance persistlaws_ty : PersistLaws Ṫy.
Proof.
  constructor.
  - intros * ? w t. induction t; cbn.
    + apply lk_refl.
    + reflexivity.
    + now f_equal.
  - intros * ? w0 t *. induction t; cbn.
    + apply lk_trans.
    + reflexivity.
    + now f_equal.
  - intros ? ? ? t * Heq. induction t; cbn; f_equal; auto.
Qed.

#[export] Instance persistent_unit : Persistent Unit :=
  fun Θ w1 u w2 r => u.
#[export] Instance persistent_prod {A B}
  {pRA : Persistent A} {pRB : Persistent B} : Persistent (Prod A B) :=
  fun Θ w1 '(a,b) w2 r => (persist a r, persist b r).
#[export] Instance persistent_option {A} {pRA : Persistent A} :
  Persistent (Option A) :=
  fun Θ w1 oa w2 r => option.map (fun a => persist a r) oa.
#[export] Instance persistent_list {A} {pRA : Persistent A} :
  Persistent (List A) :=
  fun Θ w1 la w2 r => List.map (fun a => persist a r) la.

#[export] Instance persistlaws_option {A} `{persLawsA : PersistLaws A} :
  PersistLaws (Option A).
Proof.
  constructor.
  - intros. destruct a; cbn; f_equal. apply persist_refl.
  - intros. destruct a; cbn; f_equal. apply persist_trans.
  - intros. destruct a; cbn; f_equal. now apply persist_simulation.
Qed.

#[export] Instance persistlaws_prod {A B} `{PersistLaws A, PersistLaws B} :
  PersistLaws (Prod A B).
Proof.
  constructor.
  - intros. destruct a; cbn; f_equal; apply persist_refl.
  - intros. destruct a; cbn; f_equal; apply persist_trans.
  - intros. destruct a; cbn; f_equal; now apply persist_simulation.
Qed.

#[export] Instance persistlaws_env : PersistLaws Ėnv.
Proof.
  constructor.
  - intros * ? w Γ. unfold persist, persist_env, Ėnv.
    apply map_eq. intros x. rewrite lookup_fmap.
    destruct lookup as [t|]; cbn; f_equal.
    apply persist_refl.
  - intros * ? w0 Γ *. unfold persist, persist_env, Ėnv.
    apply map_eq. intros x. rewrite !lookup_fmap.
    destruct lookup as [t|]; cbn; f_equal.
    apply persist_trans.
  - intros ? ? ? t * Heq. unfold persist, persist_env.
    apply (map_fmap_ext _ _ t). intros x s _. clear - Heq.
    now apply persist_simulation.
Qed.

(* #[export] Instance Persistent_In {x} : *)
(*   Persistent Alloc (ctx.In x) := *)
(*   fix transient {w} (xIn : x ∈ w) {w'} (r : Alloc w w') {struct r} := *)
(*     match r with *)
(*     | alloc.refl _        => xIn *)
(*     | alloc.fresh _ α _ r => transient (in_succ xIn) r *)
(*     end. *)

(* #[export] Instance PersistLaws_In {x} : PersistLaws (ctx.In x). *)
(* Proof. constructor; [easy|induction r12; cbn; auto]. Qed. *)

#[export] Instance persistent_const {A} : Persistent (Const A) :=
  fun _ _ a _ _ => a.

Lemma lookup_persist {Θ : SUB}
  {w0 w1} (θ : Θ w0 w1) (G : Ėnv w0) (x : string) :
  lookup x (persist G θ) = persist (lookup x G) θ.
Proof.
  unfold persist at 1, persist_env, Ėnv.
  now rewrite lookup_fmap.
Qed.

Lemma persist_empty {Θ : SUB}
  {w0 w1} (θ : Θ w0 w1) :
  persist (empty (A := Ėnv w0)) θ = empty.
Proof.
  apply (fmap_empty (M := gmap string)).
Qed.

Lemma persist_insert {Θ : SUB}
  {w0 w1} (θ : Θ w0 w1) (G : Ėnv w0) (x : string) (t : Ṫy w0) :
  persist (insert x t G) θ = insert x (persist t θ) (persist G θ).
Proof. unfold persist, persist_env, Ėnv. now rewrite fmap_insert. Qed.

Class LkStep (Θ : SUB) (stepΘ : Step Θ) : Prop :=
  lk_step w α (αIn : α ∈ w) β :
    lk (step (α := β)) αIn = ṫy.var (world.in_succ αIn).
#[global] Arguments LkStep Θ {_}.

Class LkThin (Θ : SUB) (thinΘ : Thin Θ) : Prop :=
  lk_thin w α (αIn : α ∈ w) β (βIn : β ∈ w - α) :
    lk (thin α) βIn = ṫy.var (world.in_thin αIn βIn).
#[global] Arguments LkThin Θ {_}.

Class LkThick (Θ : SUB) (thickΘ : Thick Θ) : Prop :=
  lk_thick w α (αIn : α ∈ w) (t : Ṫy (w - α)) β (βIn : β ∈ w) :
    lk (thick α t) βIn = thickIn αIn t βIn.
#[global] Arguments LkThick Θ {_}.

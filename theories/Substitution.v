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

Class Subst (A : OType) : Type :=
  subst : forall {Θ}, ⊧ A ↠ Box Θ A.
#[global] Arguments subst {_ _ _} [w] _ [_] _.

Load SubstitutionStlcInstances.

#[export] Instance subst_unit : Subst Unit :=
  fun Θ w1 u w2 r => u.
#[export] Instance subst_prod {A B}
  {pRA : Subst A} {pRB : Subst B} : Subst (Prod A B) :=
  fun Θ w1 '(a,b) w2 r => (subst a r, subst b r).
#[export] Instance subst_option {A} {pRA : Subst A} :
  Subst (Option A) :=
  fun Θ w1 oa w2 r => option.map (fun a => subst a r) oa.
#[export] Instance subst_list {A} {pRA : Subst A} :
  Subst (List A) :=
  fun Θ w1 la w2 r => List.map (fun a => subst a r) la.

Class LkRefl (Θ : SUB) (reflΘ : Refl Θ) : Prop :=
  lk_refl w α (αIn : α ∈ w) :
    lk refl αIn = oty.evar αIn.
#[global] Arguments LkRefl Θ {_}.
Class LkTrans (Θ : SUB) (transΘ : Trans Θ) : Prop :=
  lk_trans w0 w1 w2 (θ1 : Θ w0 w1) (θ2 : Θ w1 w2) α (αIn : α ∈ w0) :
    lk (trans θ1 θ2) αIn = subst (lk θ1 αIn) θ2.
#[global] Arguments LkRefl Θ {_}.
#[global] Arguments LkTrans Θ {_}.

Class SubstLaws A {subA : Subst A} : Type :=
  { subst_refl {Θ} {reflΘ : Refl Θ} {lkreflΘ : LkRefl Θ} :
    forall w (a : A w),
      subst a (refl (Θ := Θ)) = a;
    subst_trans {Θ : SUB} {transΘ : Trans Θ} {lktransΘ : LkTrans Θ} :
    forall w0 (a : A w0) w1 (θ1 : Θ w0 w1) w2 (θ2 : Θ w1 w2),
      subst a (trans θ1 θ2) = subst (subst a θ1) θ2;
    subst_simulation {Θ1 Θ2 : SUB} :
    forall w0 a w1 (θ1 : Θ1 w0 w1) (θ2 : Θ2 w0 w1),
      (forall α (αIn : α ∈ w0), lk θ1 αIn = lk θ2 αIn) ->
      subst a θ1 = subst a θ2;
  }.
#[global] Arguments SubstLaws A {_}.

Load SubstitutionStlcProofs.

#[export] Instance substlaws_prod {A B} `{SubstLaws A, SubstLaws B} :
  SubstLaws (Prod A B).
Proof.
  constructor.
  - intros. destruct a; cbn; f_equal; apply subst_refl.
  - intros. destruct a; cbn; f_equal; apply subst_trans.
  - intros. destruct a; cbn; f_equal; now apply subst_simulation.
Qed.
#[export] Instance substlaws_option {A} `{subLawsA : SubstLaws A} :
  SubstLaws (Option A).
Proof.
  constructor.
  - intros. destruct a; cbn; f_equal. apply subst_refl.
  - intros. destruct a; cbn; f_equal. apply subst_trans.
  - intros. destruct a; cbn; f_equal. now apply subst_simulation.
Qed.
#[export] Instance subst_const {A} : Subst (Const A) :=
  fun _ _ a _ _ => a.

Class LkStep (Θ : SUB) (stepΘ : Step Θ) : Prop :=
  lk_step w α (αIn : α ∈ w) β :
    lk (step (α := β)) αIn = oty.evar (world.in_succ αIn).
#[global] Arguments LkStep Θ {_}.

Class LkThin (Θ : SUB) (thinΘ : Thin Θ) : Prop :=
  lk_thin w α (αIn : α ∈ w) β (βIn : β ∈ w - α) :
    lk (thin α) βIn = oty.evar (world.in_thin αIn βIn).
#[global] Arguments LkThin Θ {_}.

Class LkThick (Θ : SUB) (thickΘ : Thick Θ) : Prop :=
  lk_thick w α (αIn : α ∈ w) (t : OTy (w - α)) β (βIn : β ∈ w) :
    lk (thick α t) βIn = thickIn αIn t βIn.
#[global] Arguments LkThick Θ {_}.

Class LkHMap (Θ1 Θ2 : SUB) (hmapΘ : HMap Θ1 Θ2) : Prop :=
  lk_hmap [w1 w2] (θ : Θ1 w1 w2) :
    ∀ α (αIn : α ∈ w1), lk (hmap θ) αIn = lk θ αIn.
#[global] Arguments LkHMap Θ1 Θ2 {_}.

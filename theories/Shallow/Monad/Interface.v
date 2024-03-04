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
  Prelude Spec.

#[local] Set Implicit Arguments.

(* Not using the classes in stdpp.base because of mismatched argument order of MBind. *)
Section MonadClasses.
  Context (M : Type → Type).

  Class MPure : Type := pure : ∀ {A}, A -> M A.
  Class MBind : Type := bind : ∀ {A B},  M A → (A → M B) → M B.
  Class MFail : Type := fail : ∀ {A}, M A.
End MonadClasses.

#[global] Arguments fail {M _ A}.
#[global] Arguments bind {M _ _ _}.

Notation "m ≫= f" := (bind m f) (at level 60, right associativity).

Notation "x ← y ; z" := (y ≫= (λ x : _, z))
  (at level 20, y at level 100, z at level 200, only parsing).

Notation "' x ← y ; z" := (y ≫= (λ x : _, z))
  (at level 20, x pattern, y at level 100, z at level 200, only parsing).

Notation "x ;; z" := (x ≫= λ _, z)
  (at level 100, z at level 200, only parsing, right associativity).

Class TypeCheckM (M : Type -> Type) : Type :=
  MkTcM
    { equals (t1 t2 : Ty) : M unit;
      pick : M Ty;
    }.

Class WeakestPre (M : Type -> Type) : Type :=
  WP [A] : M A -> (A -> Prop) -> Prop.
Class WeakestLiberalPre (M : Type -> Type) : Type :=
  WLP [A] : M A -> (A -> Prop) -> Prop.

Class AxiomaticSemantics
  (M : Type -> Type) {mretM : MPure M} {mbindM : MBind M} {mfailM : MFail M}
  {tcmM : TypeCheckM M} {wpM : WeakestPre M} {wlpM : WeakestLiberalPre M} : Type :=
  { (* WP / Total correctness *)
    ax_wp_ret {A} (a : A) (Q : A -> Prop) :
      WP (pure a) Q <-> Q a;
    ax_wp_bind {A B} (f : A -> M B) (m : M A) (Q : B -> Prop) :
      WP (bind m f) Q <-> WP m (fun a => WP (f a) Q);
    ax_wp_fail {A} (Q : A -> Prop) :
      WP fail Q <-> False;
    ax_wp_equals (t1 t2 : Ty) (Q : unit -> Prop) :
      WP (equals t1 t2) Q <-> t1 = t2 /\ Q tt;
    ax_wp_pick (Q : Ty -> Prop) :
      WP pick Q <-> exists t, Q t;
    ax_wp_mono {A} (P Q : A -> Prop) (m : M A) :
      (forall a, P a -> Q a) -> WP m P -> WP m Q;

    (* WLP / Partial correctness *)
    ax_wlp_ret {A} (a : A) (Q : A -> Prop) :
      WLP (pure a) Q <-> Q a ;
    ax_wlp_bind {A B} (f : A -> M B) (m : M A) (Q : B -> Prop) :
      WLP (bind m f) Q <-> WLP m (fun a => WLP (f a) Q);
    ax_wlp_fail {A} (Q : A -> Prop) :
      WLP fail Q <-> True;
    ax_wlp_equals (t1 t2 : Ty) (Q : unit -> Prop) :
      WLP (equals t1 t2) Q <-> (t1 = t2 -> Q tt);
    ax_wlp_pick (Q : Ty -> Prop) :
      WLP pick Q <-> forall t, Q t;
    ax_wlp_mono {A} (P Q : A -> Prop) (m : M A) :
      (forall a, P a -> Q a) -> WLP m P -> WLP m Q;

    ax_wp_impl_wlp {A} (m : M A) (P : A -> Prop) (Q : Prop) :
      (WP m P -> Q) <-> WLP m (fun a => P a -> Q);
  }.
#[global] Arguments AxiomaticSemantics M {_ _ _ _ _ _}.

Class TypeCheckLogicM
  M {mretM : MPure M} {bindM : MBind M} {failM : MFail M} {tcM : TypeCheckM M}
    {wpM : WeakestPre M} {wlpM : WeakestLiberalPre M} : Type :=

  { wp_pure [A] (a : A) (Q : A -> Prop) :
      Q a -> WP (pure a) Q;
    wp_bind [A B] (m : M A) (f : A -> M B) (Q : B -> Prop) :
      WP m (fun a => WP (f a) Q) -> WP (bind m f) Q;
    wp_equals (σ τ : Ty) (Q : unit -> Prop) :
      σ = τ /\ Q tt -> WP (equals σ τ) Q;
    wp_pick [Q : Ty -> Prop] (τ : Ty) :
      (forall τ', τ = τ' -> Q τ') -> WP pick Q;
    wp_fail [A] (Q : A -> Prop) :
      False -> WP fail Q;
    wp_mono [A] (m : M A) (P Q : A -> Prop) :
      (forall a, P a -> Q a) -> (WP m P -> WP m Q);

    wlp_pure [A] (a : A) (Q : A -> Prop) :
      Q a -> WLP (pure a) Q;
    wlp_bind [A B] (m : M A) (f : A -> M B) (Q : B -> Prop) :
      WLP m (fun a => WLP (f a) Q) -> WLP (bind m f) Q;
    wlp_equals (σ τ : Ty) (Q : unit -> Prop) :
      (σ = τ -> Q tt) -> WLP (equals σ τ) Q;
    wlp_pick (Q : Ty -> Prop) :
      (forall τ, Q τ) -> WLP pick Q;
    wlp_fail [A] (Q : A -> Prop) :
      True -> WLP fail Q;
    wlp_mono [A] (m : M A) (P Q : A -> Prop) :
      (forall a, P a -> Q a) ->
      (WLP m P -> WLP m Q);

    wp_impl [A] (m : M A) (P : A -> Prop) (Q : Prop) :
      WLP m (fun a1 => P a1 -> Q) -> (WP m P -> Q);

  }.
#[global] Arguments TypeCheckLogicM _ {_ _ _ _ _ _}.

#[export] Instance axiomatic_tcmlogic `{AxiomaticSemantics M} :
  TypeCheckLogicM M.
Proof.
  constructor; intros *.
  - now rewrite ax_wp_ret.
  - now rewrite ax_wp_bind.
  - now rewrite ax_wp_equals.
  - rewrite ax_wp_pick. exists τ. auto.
  - now rewrite ax_wp_fail.
  - apply ax_wp_mono.
  - now rewrite ax_wlp_ret.
  - now rewrite ax_wlp_bind.
  - now rewrite ax_wlp_equals.
  - now rewrite ax_wlp_pick.
  - now rewrite ax_wlp_fail.
  - apply ax_wlp_mono.
  - now rewrite ax_wp_impl_wlp.
Qed.

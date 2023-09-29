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
  Classes.Morphisms
  Relations.Relation_Definitions.
From Em Require Import
  Context
  Environment
  Stlc.Persistence
  Stlc.Spec
  Stlc.Worlds.

Import ctx.notations.
Import World.notations.

#[local] Set Implicit Arguments.

Reserved Notation "w1 ⊒⁻ w2" (at level 80).

Definition Later (A : TYPE) : TYPE :=
  fun w => forall x (xIn : x ∈ w), A (w - x).
Definition LaterTm (A : TYPE) : TYPE :=
  fun w => forall x (xIn : x ∈ w), Ṫy (w - x) -> A (w - x).

Definition Sooner (A : TYPE) : TYPE :=
  fun w => sigT (fun x => sigT (fun (xIn : x ∈ w) => A (w - x))).
Definition SoonerTm (A : TYPE) : TYPE :=
  fun w => sigT (fun x => sigT (fun (xIn : x ∈ w) => Ṫy (w - x) * A (w - x)))%type.

Module Tri.

  (* #[local] Unset Elimination Schemes. *)

  Inductive Raw (w : World) : World -> Set :=
  | refl      : Raw w w
  | cons {w' x} (xIn : x ∈ w) (t : Ṫy (w - x)) (ζ : Raw (w - x) w') : Raw w w'.
  #[global] Arguments refl {_}.
  #[global] Arguments cons {_ _} x {_} t ζ.

  Section InnerRecursion.

    Context [w w' : World] (rec : forall y (yIn : y ∈ w), Ṫy w').

    Fixpoint persist_inner (t : Ṫy w) : Ṫy w' :=
      match t with
      | ṫy.var xIn    => rec xIn
      | ṫy.bool       => ṫy.bool
      | ṫy.func t1 t2 => ṫy.func (persist_inner t1) (persist_inner t2)
      end.

  End InnerRecursion.

  #[export] Instance proper_persist_inner {w0 w1} :
    Proper (forall_relation (fun y => pointwise_relation (y ∈ w0) eq) ==> pointwise_relation _ eq) (@persist_inner w0 w1).
  Proof. intros r1 r2 Hr t; induction t; cbn; now f_equal; auto. Qed.

  Fixpoint persist_outer {w0} t {w1} (r : Raw w0 w1) {struct r} : Ṫy w1 :=
    match r with
    | refl       => t
    | cons α s r => persist_inner
                      (fun b βIn => persist_outer (thickIn _ s βIn) r)
                      t
    end.

  Canonical Structure Tri : ACC :=
    {| acc              := Raw;
       lk w1 w2 θ α αIn := persist_outer (ṫy.var αIn) θ;
    |}.
  Notation "w1 ⊒⁻ w2" := (acc Tri w1 w2).

  #[export] Instance thick_tri : Thick Tri :=
    fun w x xIn t => cons x t refl.
  #[export] Instance refl_tri : Refl Tri :=
    fun w => refl.
  #[export] Instance trans_tri : Trans Tri :=
    fix trans [w0 w1 w2] (ζ1 : w0 ⊒⁻ w1) {struct ζ1} : w1 ⊒⁻ w2 -> w0 ⊒⁻ w2 :=
      match ζ1 with
      | refl        => fun ζ2 => ζ2
      | cons x t ζ1 => fun ζ2 => cons x t (trans ζ1 ζ2)
      end.

  Module Import notations.
    Notation "▷ A" := (Later A) (at level 9, right associativity).
    Notation "▶ A" := (LaterTm A) (at level 9, right associativity).
    Notation "◁ A" := (Sooner A) (at level 9, right associativity).
    Notation "◀ A" := (SoonerTm A) (at level 9, right associativity).
    Notation "□⁻ A" := (Box Tri A) (at level 9, format "□⁻ A", right associativity).
  End notations.

  Definition box_intro_split {A} :
    ⊢ʷ A -> ▶□⁻A -> □⁻A :=
    fun w0 a la w1 ζ =>
      match ζ with
      | Tri.refl => a
      | Tri.cons x t ζ' => la x _ t _ ζ'
      end.

  #[export] Instance refltrans_tri : ReflTrans Tri.
  Proof.
    constructor.
    - easy.
    - induction r; cbn; [|rewrite IHr]; easy.
    - induction r1; cbn; congruence.
  Qed.

  #[export] Instance lkrefl_tri : LkRefl Tri.
  Proof. intros w α αIn. reflexivity. Qed.

  Lemma persist_outer_fix {w0 w1} (θ : Tri w0 w1) (t : Ṫy w0) :
     persist_outer t θ =
     match t with
     | ṫy.var αIn    => lk θ αIn
     | ṫy.bool       => ṫy.bool
     | ṫy.func t1 t2 => ṫy.func (persist_outer t1 θ) (persist_outer t2 θ)
     end.
  Proof. induction θ; destruct t; cbn; auto. Qed.

  Lemma persist_outer_refl {w} (t : Ṫy w) : persist_outer t Worlds.refl = t.
  Proof. reflexivity. Qed.

  Lemma persist_persist_inner {w0 w1} (t : Ṫy w0) (rec : forall y (yIn : y ∈ w0), Ṫy w1) {w2} (r : Tri w1 w2) :
    persist (persist_inner rec t) r = persist_inner (fun y yIn => persist (rec y yIn) r) t.
  Proof. induction t; cbn; f_equal; auto. Qed.

  Lemma persist_outer_persist_inner {w0 w1} (t : Ṫy w0) (rec : forall y (yIn : y ∈ w0), Ṫy w1) {w2} (r : Tri w1 w2) :
    persist_outer (persist_inner rec t) r = persist_inner (fun y yIn => persist_outer (rec y yIn) r) t.
  Proof.
    induction t; cbn; auto; rewrite persist_outer_fix at 1; f_equal; auto.
  Qed.

  Lemma persist_outer_trans {w0} (t : Ṫy w0) {w1 w2} (θ1 : Tri w0 w1) (θ2 : Tri w1 w2) :
    persist_outer t (θ1 ⊙ θ2) = persist_outer (persist_outer t θ1) θ2.
  Proof.
    induction θ1; cbn.
    - reflexivity.
    - rewrite persist_outer_persist_inner.
      now apply proper_persist_inner.
  Qed.

  Lemma persist_outer_persist {w0 w1} (θ : w0 ⊒⁻ w1) (t : Ṫy w0) :
    persist_outer t θ = persist t θ.
  Proof. induction t; cbn; rewrite persist_outer_fix; f_equal; auto. Qed.

  #[export] Instance lktrans_tri : LkTrans Tri.
  Proof.
    intros w0 w1 w2 θ1 θ2 α αIn. unfold lk; cbn.
    generalize (ṫy.var αIn). clear. intros t.
    now rewrite persist_outer_trans, persist_outer_persist.
  Qed.

  #[export] Instance lkthick_tri : LkThick Tri.
  Proof. easy. Qed.

End Tri.
Export Tri (Tri).
Notation "w1 ⊒⁻ w2" := (Tri w1 w2) (at level 80).
Infix "⊙⁻" := (trans (Θ := Tri)) (at level 60, right associativity).

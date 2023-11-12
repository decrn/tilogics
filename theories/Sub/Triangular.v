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

From Em Require Import Prelude Persistence Worlds.

Import world.notations.

#[local] Set Implicit Arguments.

Reserved Notation "w1 ⊒⁻ w2" (at level 80).

Module Tri.

  Inductive Rel (w : World) : World -> Set :=
  | nil : Rel w w
  | cons {w' α} (αIn : α ∈ w) (τ : OTy (w - α)) (θ : w - α ⊒⁻ w') : w ⊒⁻ w'
  where "w0 ⊒⁻ w1" := (Rel w0 w1).
  #[global] Arguments nil {_}.
  #[global] Arguments cons {_ _} α {_} τ θ.

  Section InnerRecursion.

    Context [w w' : World] (rec : ∀ y (yIn : y ∈ w), OTy w').

    Fixpoint persist_inner (t : OTy w) : OTy w' :=
      match t with
      | oty.evar xIn   => rec xIn
      | oty.bool       => oty.bool
      | oty.func t1 t2 => oty.func (persist_inner t1) (persist_inner t2)
      end.

  End InnerRecursion.

  Lemma proper_persist_inner {w0 w1} (rec1 rec2 : ∀ α, α ∈ w0 → OTy w1)
    (Hrec : ∀ α (αIn : α ∈ w0), rec1 α αIn = rec2 α αIn) :
    ∀ τ, persist_inner rec1 τ = persist_inner rec2 τ.
  Proof. induction τ; cbn; now f_equal; auto. Qed.

  Fixpoint persist_outer {w0} t {w1} (r : w0 ⊒⁻ w1) {struct r} : OTy w1 :=
    match r with
    | nil        => t
    | cons α s r => persist_inner
                      (fun b βIn => persist_outer (thickIn _ s βIn) r)
                      t
    end.

  Canonical Structure Tri : SUB :=
    {| sub              := Rel;
       lk w1 w2 θ α αIn := persist_outer (oty.evar αIn) θ;
    |}.

  #[export] Instance thick_tri : Thick Tri :=
    fun w x xIn t => cons x t nil.
  #[export] Instance refl_tri : Refl Tri :=
    fun w => nil.
  #[export] Instance trans_tri : Trans Tri :=
    fix trans [w0 w1 w2] (ζ1 : w0 ⊒⁻ w1) {struct ζ1} : w1 ⊒⁻ w2 -> w0 ⊒⁻ w2 :=
      match ζ1 with
      | nil         => fun ζ2 => ζ2
      | cons x t ζ1 => fun ζ2 => cons x t (trans ζ1 ζ2)
      end.

  #[export] Instance refltrans_tri : ReflTrans Tri.
  Proof.
    constructor.
    - easy.
    - induction r; cbn; now f_equal.
    - induction r1; cbn; intros; now f_equal.
  Qed.

  #[export] Instance lkrefl_tri : LkRefl Tri.
  Proof. easy. Qed.

  Lemma persist_outer_fix {w0 w1} (θ : w0 ⊒⁻ w1) (t : OTy w0) :
     persist_outer t θ =
     match t with
     | oty.evar αIn   => lk θ αIn
     | oty.bool       => oty.bool
     | oty.func t1 t2 => oty.func (persist_outer t1 θ) (persist_outer t2 θ)
     end.
  Proof. induction θ; destruct t; cbn; now f_equal. Qed.

  Lemma persist_outer_refl {w} (t : OTy w) : persist_outer t refl = t.
  Proof. reflexivity. Qed.

  Lemma persist_persist_inner {w0 w1} (t : OTy w0)
    (rec : ∀ y (yIn : y ∈ w0), OTy w1) {w2} (r : w1 ⊒⁻ w2) :
    persist (persist_inner rec t) r =
    persist_inner (fun y yIn => persist (rec y yIn) r) t.
  Proof. induction t; cbn; now f_equal. Qed.

  Lemma persist_outer_persist_inner {w0 w1} (t : OTy w0)
    (rec : ∀ y (yIn : y ∈ w0), OTy w1) {w2} (r : w1 ⊒⁻ w2) :
    persist_outer (persist_inner rec t) r =
    persist_inner (fun y yIn => persist_outer (rec y yIn) r) t.
  Proof.
    induction t; cbn; auto; rewrite persist_outer_fix at 1; f_equal; auto.
  Qed.

  Lemma persist_outer_trans {w0 w1 w2 τ} (θ1 : w0 ⊒⁻ w1) (θ2 : w1 ⊒⁻ w2) :
    persist_outer τ (θ1 ⊙ θ2) = persist_outer (persist_outer τ θ1) θ2.
  Proof.
    induction θ1; cbn.
    - reflexivity.
    - rewrite persist_outer_persist_inner.
      now apply proper_persist_inner.
  Qed.

  Lemma persist_outer_persist {w0 w1} (θ : w0 ⊒⁻ w1) (t : OTy w0) :
    persist_outer t θ = persist t θ.
  Proof. induction t; cbn; rewrite persist_outer_fix; f_equal; auto. Qed.

  #[export] Instance lktrans_tri : LkTrans Tri.
  Proof.
    intros w0 w1 w2 θ1 θ2 α αIn. unfold lk; cbn.
    now rewrite persist_outer_trans, persist_outer_persist.
  Qed.

  #[export] Instance lkthick_tri : LkThick Tri.
  Proof. easy. Qed.

  Ltac folddefs :=
    repeat
      match goal with
      | |- context[@Tri.nil ?w] =>
          change_no_check (@nil w) with (@refl Tri _ w)
      | |- context[Tri.cons ?x ?t refl] =>
          change_no_check (cons x t refl) with (thick x t)
      | |- context[Tri.cons ?x ?t ?r] =>
          change_no_check (cons x t r) with (trans (Θ := Tri) (thick x t) r)
      end.

End Tri.
Export Tri (Tri).
Notation "w1 ⊑⁻ w2" := (sub Tri w1 w2) (at level 80).
Infix "⊙⁻" := (trans (Θ := Tri)) (at level 60, right associativity).
Notation "□⁻ A" := (Box Tri A)
  (at level 9, right associativity, format "□⁻ A") : indexed_scope.
Notation "◇⁻ A" := (Diamond Tri A)
  (at level 9, right associativity, format "◇⁻ A") : indexed_scope.

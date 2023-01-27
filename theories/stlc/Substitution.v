(******************************************************************************)
(* Copyright (c) 2022 Steven Keuchel                                          *)
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

From Equations Require Import
     Equations.
From Em Require Import
     Definitions Context Environment Prelude STLC Triangular.
Import SigTNotations.
Import ctx.notations.

Set Implicit Arguments.

#[local] Arguments Ty_hole {Σ i} xIn.
#[local] Arguments Ty_bool {Σ}.
#[local] Arguments Ty_func {Σ}.
#[local] Open Scope indexed_scope.

Reserved Notation "w1 ⊒ˢ w2" (at level 80).

Module Sub.

  Definition Sub (w1 w2 : World) : Type :=
    @env.Env nat (fun _ => Ty w2) w1.
  Local Notation "w1 ⊒ˢ w2" := (Sub w1 w2).

  Definition Box (A : TYPE) : TYPE :=
    fun w0 => forall w1, w0 ⊒ˢ w1 -> A w1.
  Local Notation "□ A" := (Box A) (at level 9, format "□ A", right associativity).

  Definition subst : ⊢ Ty -> □Ty :=
    fun w1 =>
      fix subst (S : Ty w1) {w2} (ζ : w1 ⊒ˢ w2) {struct S} : Ty w2 :=
      match S with
      | Ty_hole σIn   => env.lookup ζ σIn
      | Ty_bool       => Ty_bool
      | Ty_func S1 S2 => Ty_func (subst S1 ζ) (subst S2 ζ)
      end.

  Definition id {w} : w ⊒ˢ w :=
    env.tabulate (fun _ => Ty_hole).
  Definition thick {w x} (xIn : x ∈ w) (s : Ty (w - x)) : w ⊒ˢ w - x :=
    env.tabulate (thickIn xIn s).
  Definition thin {w x} (xIn : x ∈ w) : w - x ⊒ˢ w :=
    env.tabulate (fun y yIn => Ty_hole (ctx.in_thin xIn yIn)).
  Definition comp {w0 w1 w2} (ζ1 : w0 ⊒ˢ w1) (ζ2 : w1 ⊒ˢ w2) : w0 ⊒ˢ w2 :=
    env.map (fun _ t => subst t ζ2) ζ1.
  Local Infix "⊙ˢ" := comp (at level 60, right associativity).

  Fixpoint triangular {w1 w2} (ζ : w1 ⊒⁻ w2) : w1 ⊒ˢ w2 :=
    match ζ with
    | Tri.refl       => id
    | Tri.cons x t ζ => comp (thick _ t) (triangular ζ)
    end.

  Lemma lookup_id {w x} (xIn : x ∈ w)  :
    env.lookup id xIn = Ty_hole xIn.
  Proof. unfold id. now rewrite env.lookup_tabulate. Qed.

  Lemma lookup_comp {w1 w2 w3 x} (xIn : x ∈ w1) (ζ1 : w1 ⊒ˢ w2) (ζ2 : w2 ⊒ˢ w3) :
    env.lookup (comp ζ1 ζ2) xIn = subst (env.lookup ζ1 xIn) ζ2.
  Proof. unfold comp. now rewrite env.lookup_map. Qed.

  Lemma lookup_thin {w x y} (xIn : x ∈ w) (yIn : y ∈ w - x) :
    env.lookup (thin xIn) yIn = Ty_hole (ctx.in_thin xIn yIn).
  Proof. unfold thin. now rewrite env.lookup_tabulate. Qed.

  Lemma lookup_thick {w x y} (xIn : x ∈ w) (t : Ty _) (yIn : y ∈ w) :
    env.lookup (thick xIn t) yIn = thickIn xIn t yIn.
  Proof. unfold thick. now rewrite env.lookup_tabulate. Qed.

  Lemma subst_id {w} (t : Ty w) :
    subst t id = t.
  Proof. induction t; cbn; f_equal; now rewrite ?lookup_id. Qed.

  Lemma subst_comp {w1} (t : Ty w1) {w2 w3} (ζ2 : w2 ⊒ˢ w3) (ζ1 : w1 ⊒ˢ w2) :
    subst t (comp ζ1 ζ2) = subst (subst t ζ1) ζ2.
  Proof. induction t; cbn; f_equal; now rewrite ?lookup_comp. Qed.

  Lemma comp_assoc {w1 w2 w3 w4} (ζ1 : w1 ⊒ˢ w2) (ζ2 : w2 ⊒ˢ w3) (ζ3 : w3 ⊒ˢ w4) :
    comp (comp ζ1 ζ2) ζ3 = comp ζ1 (comp ζ2 ζ3).
  Proof.
    apply env.lookup_extensional. intros x xIn.
    now rewrite ?lookup_comp, subst_comp.
  Qed.

  Lemma comp_id_left {w1 w2} (ζ : w1 ⊒ˢ w2) : comp id ζ = ζ.
  Proof.
    apply env.lookup_extensional. intros x xIn.
    now rewrite lookup_comp, lookup_id.
  Qed.

  Lemma comp_id_right {w1 w2} (ζ : w1 ⊒ˢ w2) :
    comp ζ id = ζ.
  Proof.
    apply env.lookup_extensional. intros x xIn.
    now rewrite lookup_comp, subst_id.
  Qed.

  Lemma triangular_trans {w0 w1 w2} (ζ01 : w0 ⊒⁻ w1) (ζ12 : w1 ⊒⁻ w2) :
    triangular (Tri.trans ζ01 ζ12) =
      comp (triangular ζ01) (triangular ζ12).
  Proof.
    induction ζ01; cbn [triangular Tri.trans].
    - now rewrite comp_id_left.
    - now rewrite comp_assoc, IHζ01.
  Qed.

  Lemma comp_thin_thick {w x} (xIn : x ∈ w) (t : Ty (w - x)) :
    comp (thin xIn) (thick xIn t) = id.
  Proof.
    apply env.lookup_extensional. intros y yIn.
    rewrite lookup_comp, lookup_id, lookup_thin. cbn.
    rewrite lookup_thick. unfold thickIn.
    now rewrite ctx.occurs_check_view_thin.
  Qed.

  Lemma subst_thin {w x} (xIn : x ∈ w) (T : Ty (w - x)) :
    Triangular.thin xIn T = subst T (thin xIn).
  Proof. induction T; cbn; f_equal; now rewrite ?lookup_thin. Qed.

  Definition geq {w0 w1} (ζ1 : w0 ⊒ˢ w1) [w2] (ζ2 : w0 ⊒ˢ w2) : Prop :=
    exists ζ12 : w1 ⊒ˢ w2, ζ2 = ζ1 ⊙ˢ ζ12.
  Notation "ζ1 ≽ ζ2" := (geq ζ1 ζ2) (at level 80).

  Lemma geq_refl {w1 w2} (ζ : w1 ⊒ˢ w2) : ζ ≽ ζ.
  Proof. exists Sub.id. symmetry. apply Sub.comp_id_right. Qed.

  Lemma geq_trans {w0 w1 w2 w3} (ζ1 : w0 ⊒ˢ w1) (ζ2 : w0 ⊒ˢ w2) (ζ3 : w0 ⊒ˢ w3) :
    ζ1 ≽ ζ2 -> ζ2 ≽ ζ3 -> ζ1 ≽ ζ3.
  Proof.
    intros [ζ12 H12] [ζ23 H23]. rewrite H23, H12.
    exists (ζ12 ⊙ˢ ζ23). apply Sub.comp_assoc.
  Qed.

  Lemma geq_precom {w0 w1 w2 w3} (ζ1 : w0 ⊒ˢ w1) (ζ2 : w1 ⊒ˢ w2) (ζ3 : w1 ⊒ˢ w3) :
    ζ2 ≽ ζ3 -> ζ1 ⊙ˢ ζ2 ≽ ζ1 ⊙ˢ ζ3.
  Proof. intros [ζ23 ->]. exists ζ23. symmetry. apply Sub.comp_assoc. Qed.

  Lemma geq_max {w1 w2} (ζ : w1 ⊒ˢ w2) : id ≽ ζ.
  Proof. exists ζ. symmetry. apply Sub.comp_id_left. Qed.

  Lemma geq_extend {w0 w1 w2} (ζ1 : w0 ⊒ˢ w1) (ζ2 : w1 ⊒ˢ w2) : ζ1 ≽ ζ1 ⊙ˢ ζ2.
  Proof. now exists ζ2. Qed.

  Fixpoint geqb {w0 w1} (ζ1 : w0 ⊒⁻ w1) [w2] (ζ2 : w0 ⊒ˢ w2) {struct ζ1} : bool :=
    match ζ1 with
    | Tri.refl => true
    | Tri.cons x t ζ1 =>
        let ζ2' := thin _ ⊙ˢ ζ2 in
        if Ty_eqdec (subst (Ty_hole _) ζ2) (subst t ζ2')
        then geqb ζ1 ζ2'
        else false
    end.
  Infix "≽?" := geqb (at level 80).

  Lemma geqb_spec {w0 w1} (ζ1 : w0 ⊒⁻ w1) :
    forall [w2] (ζ2 : w0 ⊒ˢ w2),
      Bool.reflect (triangular ζ1 ≽ ζ2) (ζ1 ≽? ζ2).
  Proof.
    induction ζ1; cbn [geqb triangular]; intros w2 ζ2.
    - constructor. apply geq_max.
    - destruct Ty_eqdec.
      + destruct (IHζ1 _ (thin xIn ⊙ˢ ζ2)); constructor; clear IHζ1.
        * destruct g as [ζ2']. exists ζ2'.
          rewrite comp_assoc. rewrite <- H. clear - e.
          apply env.lookup_extensional.
          intros y yIn.
          rewrite lookup_comp.
          rewrite lookup_thick. unfold thickIn.
          destruct (ctx.occurs_check_view xIn yIn). apply e.
          cbn. rewrite lookup_comp. unfold thin.
          now rewrite env.lookup_tabulate.
        * intros [ζ2' ->]. apply n. clear n. exists ζ2'.
          rewrite <- ?comp_assoc.
          rewrite comp_thin_thick.
          rewrite comp_id_left.
          reflexivity.
      + constructor. intros [ζ2' ->]. apply n. clear n.
        rewrite <- ?comp_assoc.
        rewrite comp_thin_thick.
        rewrite comp_id_left.
        cbn. rewrite ?lookup_comp, lookup_thick.
        unfold thickIn. rewrite ctx.occurs_check_view_refl.
        now rewrite subst_comp.
  Qed.

End Sub.
Infix "⊒ˢ" := Sub.Sub.
Infix "⊙ˢ" := Sub.comp (at level 60, right associativity).
Infix "≽ˢ" := Sub.geq (at level 80).
(* Infix "≽?" := Sub.geqb (at level 80). *)

(* Infix "≽⁻" := Tri.geq (at level 80). *)
(* Infix "≽?" := Sub.geqb (at level 80). *)

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

From Coq Require Import Relations.Relation_Operators Strings.String.
From stdpp Require Import base gmap.
From Em Require Import Environment Substitution Spec Worlds.

Import world.notations.

#[local] Set Implicit Arguments.

Notation Assignment := (env.Env Ty).

(* The default assignment we use, grounds all evars to the boolean type. *)
Fixpoint grounding (w : World) : Assignment w :=
  match w with
  | world.nil      => env.nil
  | world.snoc Γ b => env.snoc (grounding Γ) b ty.bool
  end%world.

(* For a pair of a closed type A and open type AT, lift converts a value 
   from the closed to the open type. *)
Class Lift (AT : OType) (A : Type) : Type :=
  lift : A → ⊧ AT.
#[global] Arguments lift {_ _ _} _ {_}.

#[export] Instance lift_prod {AT BT A B} `{Lift AT A, Lift BT B} :
  Lift (Prod AT BT) (A * B) :=
  fun '(a , b) w => (lift a, lift b).

(* Inst for instantiation applies a given assignment to a value of an open type
   to get a corresponding value of the closed type. *)
Class Inst (A : OType) (a : Type) : Type :=
  inst : ∀ {w}, A w → Assignment w → a.

#[export] Instance inst_list {A : OType} {a : Type} `{Inst A a} :
  Inst (List A) (list a) :=
  fun w xs ass => List.map (fun x => inst x ass) xs.
#[export] Instance inst_const {A} : Inst (Const A) A | 10 :=
  fun Σ x ι => x.
#[export] Instance inst_unit : Inst Unit unit :=
  fun _ x ass => x.
#[export] Instance inst_prod {AT BT A B} `{Inst AT A, Inst BT B} :
  Inst (Prod AT BT) (A * B) :=
  fun ass '(a , b) ι => (inst a ι, inst b ι).
#[export] Instance inst_option {AT A} `{Inst AT A} :
  Inst (Option AT) (option A) :=
  fun w ma ass => option_map (fun a => inst a ass) ma.

(* Instances for Ty and Env are in a separate file for the sole purpose
   of counting SLoC for the generic and specific categories. *)
Load InstantiationStlcInstances.

(* One special instance is that anything of a substitution type can be
   instantiated to an assignment. This is a kind of composition of the
   substituition with the given assignment: An evar is first subtituted for an
   open type, and then that open type is instantiated to a closed type.
   Effectively we get a mapping from evars to closed types, which is just
   assignment. *)
#[export] Instance inst_sub {Θ : SUB} : ∀ w, Inst (Θ w) (Assignment w) :=
  fun w0 w1 θ ι => env.tabulate (fun α αIn => inst (lk θ αIn) ι).

(* The inst and lift operations interact with each other and also
   with the substitution operator. The following type classes encapsulate
   these interactions. *)
Class InstLift AT A `{Inst AT A, Lift AT A} : Prop :=
  inst_lift (w : World) (a : A) (ι : Assignment w) :
    inst (lift a) ι = a.
#[global] Arguments InstLift _ _ {_ _}.
Class SubstLift AT A {liftA : Lift AT A} {subA: Subst AT} : Prop :=
  subst_lift [Θ : SUB] {w0 w1} (a : A) (θ : Θ w0 w1) :
    subst (lift a) θ = lift a.
#[global] Arguments SubstLift _ _ {_ _}.
Class InstSubst AT A `{Subst AT, Inst AT A} : Prop :=
  inst_subst [Θ : SUB] {w0 w1} (θ : Θ w0 w1) (t : AT w0) (ι : Assignment w1) :
    inst (subst t θ) ι = inst t (inst θ ι).
#[global] Arguments InstSubst _ _ {_ _}.

#[export] Instance inst_lift_prod {AT A BT B}
  `{InstLift AT A, InstLift BT B} : InstLift (Prod AT BT) (A * B).
Proof. intros w [a b] ι. cbn. f_equal; apply inst_lift. Qed.
#[export] Instance inst_subst_prod {AT A BT B}
  `{InstSubst AT A, InstSubst BT B} : InstSubst (Prod AT BT) (A * B).
Proof. intros Θ w0 w1 θ [a b] ι. cbn. f_equal; apply inst_subst. Qed.

(* Just like before load the instances for the interaction proofs from
   another file. *)
Load InstantiationStlcProofs.

(* The instantiation of substitutions also interacts with the different
   operations on substitutions. The following lemmas witness some of these. *)
Lemma inst_refl {Θ} {reflΘ : Refl Θ} {lkreflΘ : LkRefl Θ} w (ι : Assignment w) :
  inst (refl (Θ := Θ)) ι = ι.
Proof.
  apply env.lookup_extensional. intros α αIn. unfold inst, inst_sub.
  now rewrite env.lookup_tabulate, lk_refl.
Qed.

Lemma inst_trans {Θ} {transΘ : Trans Θ} {lktransΘ : LkTrans Θ} w0 w1 w2
  (θ1 : Θ w0 w1) (θ2 : Θ w1 w2) (ι : Assignment w2) :
  inst (θ1 ⊙ θ2) ι = inst θ1 (inst θ2 ι).
Proof.
  apply env.lookup_extensional. intros α αIn. unfold inst, inst_sub.
  now rewrite ?env.lookup_tabulate, lk_trans, inst_subst.
Qed.

Lemma inst_step_snoc {Θ} {stepΘ : Step Θ} {lkStepΘ : LkStep Θ}
  {w x} (ι : Assignment w) (t : Ty) :
  inst (step (Θ := Θ)) (env.snoc ι x t) = ι.
Proof.
  apply env.lookup_extensional. intros α αIn. unfold inst, inst_sub.
  rewrite env.lookup_tabulate. rewrite lk_step. reflexivity.
Qed.

Lemma inst_step {Θ} {stepΘ : Step Θ} {lkStepΘ : LkStep Θ}
  {w x} (ι : Assignment (w ، x)) :
  inst (step (Θ := Θ)) ι = let (ι',_) := env.view ι in ι'.
Proof. destruct env.view. apply inst_step_snoc. Qed.

Lemma inst_thin {Θ} {thinΘ : Thin Θ} {lkthinΘ : LkThin Θ}
  {w} (ι : Assignment w) {α} (αIn : α ∈ w) :
  inst (thin α) ι = env.remove α ι αIn.
Proof.
  apply env.lookup_extensional. intros β βIn. unfold inst, inst_sub.
  rewrite env.lookup_tabulate. rewrite lk_thin. cbn.
  now rewrite env.lookup_thin.
Qed.

Lemma inst_thick {Θ} {thickΘ : Thick Θ} {lkthickΘ : LkThick Θ} {w x}
  (xIn : x ∈ w) (t : OTy (w - x)) (ι : Assignment (w - x)) :
  inst (thick (Θ := Θ) x t) ι = env.insert xIn ι (inst t ι).
Proof.
  apply env.lookup_extensional. intros β βIn. unfold inst, inst_sub.
  rewrite env.lookup_tabulate, lk_thick. unfold thickIn.
  destruct world.occurs_check_view; cbn.
  - now rewrite env.lookup_insert.
  - now rewrite env.lookup_thin, env.remove_insert.
Qed.

Lemma inst_hmap `{LkHMap Θ1 Θ2} {w1 w2} (θ : Θ1 w1 w2) (ι : Assignment w2) :
  inst (hmap θ) ι = inst θ ι.
Proof.
  apply env.lookup_extensional. intros β βIn. unfold inst, inst_sub.
  now rewrite !env.lookup_tabulate, lk_hmap.
Qed.

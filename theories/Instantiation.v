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
From Em Require Import Environment Prelude Persistence Spec Worlds.

Import world.notations.

#[local] Set Implicit Arguments.

Notation Assignment := (env.Env Ty).

Section Inst.

  Class Inst (A : OType) (a : Type) : Type :=
    inst : forall {w}, A w -> Assignment w -> a.

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

  #[export] Instance inst_ty : Inst Ṫy Ty :=
    fix inst_ty {w} t ι :=
      match t with
      | ṫy.var αIn    => env.lookup ι αIn
      | ṫy.bool       => ty.bool
      | ṫy.func t1 t2 => ty.func (inst_ty t1 ι) (inst_ty t2 ι)
      end.

  #[export] Instance inst_env : Inst Ėnv Env :=
    fun w Γ ι => base.fmap (fun t : Ṫy w => inst t ι) Γ.

  #[export] Instance inst_acc {Θ : SUB} :
    forall w, Inst (Θ w) (Assignment w) :=
    fun w0 w1 θ ι => env.tabulate (fun α αIn => inst (lk θ αIn) ι).
End Inst.

Section Lift.

  Class Lift (AT : OType) (A : Type) : Type :=
    lift : A -> ⊧ AT.
  #[global] Arguments lift {_ _ _} _ {_}.

  (* Indexes a given ty by a world Σ *)
  #[export] Instance lift_ty : Lift Ṫy Ty :=
    fix lift_ty (t : Ty) w : Ṫy w :=
      match t with
      | ty.bool       => ṫy.bool
      | ty.func t1 t2 => ṫy.func (lift_ty t1 w) (lift_ty t2 w)
      end.

  #[export] Instance lift_env : Lift Ėnv Env :=
    fun E w => fmap (fun t => lift t) E.

  #[export] Instance lift_prod {AT BT A B} `{Lift AT A, Lift BT B} :
    Lift (Prod AT BT) (A * B) :=
    fun '(a , b) w => (lift a, lift b).

End Lift.

Section InstLift.

  Class InstLift AT A `{Inst AT A, Lift AT A} : Prop :=
    inst_lift (w : World) (a : A) (ι : Assignment w) :
      inst (lift a) ι = a.
  #[global] Arguments InstLift _ _ {_ _}.

  #[export] Instance inst_lift_ty : InstLift Ṫy Ty.
  Proof. intros w t ι. induction t; cbn; f_equal; auto. Qed.

  #[export] Instance inst_lift_env : InstLift Ėnv Env.
  Proof.
    intros w E ι. unfold inst, inst_env, lift, lift_env.
    rewrite <- map_fmap_id, <- map_fmap_compose.
    apply map_fmap_ext. intros x t Hlk. apply inst_lift.
  Qed.

  #[export] Instance inst_lift_prod {AT A BT B}
    `{InstLift AT A, InstLift BT B} : InstLift (Prod AT BT) (A * B).
  Proof. intros w [a b] ι. cbn. f_equal; apply inst_lift. Qed.

End InstLift.

Section InstPersist.

  Class InstPersist AT A `{Persistent AT, Inst AT A} : Prop :=
    inst_persist [Θ : SUB] {w0 w1} (θ : Θ w0 w1) (t : AT w0) (ι : Assignment w1) :
      inst (persist t θ) ι = inst t (inst θ ι).
  #[global] Arguments InstPersist _ _ {_ _}.

  #[export] Instance inst_persist_ty : InstPersist Ṫy Ty.
  Proof.
    intros Θ w0 w1 θ t ι. induction t; cbn; f_equal; auto.
    unfold inst at 2, inst_acc. now rewrite env.lookup_tabulate.
  Qed.

  #[export] Instance inst_persist_env : InstPersist Ėnv Env.
  Proof.
    intros Θ w0 w1 θ E ι. unfold persist, persist_env, inst at 1 2, inst_env.
    rewrite <- map_fmap_compose. apply map_fmap_ext.
    intros x t Hlk. apply inst_persist.
  Qed.

  #[export] Instance inst_persist_prod {AT A BT B}
    `{InstPersist AT A, InstPersist BT B} : InstPersist (Prod AT BT) (A * B).
  Proof. intros Θ w0 w1 θ [a b] ι. cbn. f_equal; apply inst_persist. Qed.

End InstPersist.

Section PersistLift.
  Class PersistLift AT A {liftA : Lift AT A} {persA: Persistent AT} : Prop :=
    persist_lift [Θ : SUB] {w0 w1} (a : A) (θ : Θ w0 w1) :
      persist (lift a) θ = lift a.
  #[global] Arguments PersistLift _ _ {_ _}.

  #[export] Instance persist_lift_ty : PersistLift Ṫy Ty.
  Proof. intros Θ w0 w1 t θ. induction t; cbn; f_equal; auto. Qed.

  #[export] Instance persist_lift_env : PersistLift Ėnv Env.
  Proof.
    intros Θ w0 w1 E θ. unfold persist, lift, persist_env, lift_env, Ėnv.
    rewrite <- map_fmap_compose. apply map_fmap_ext.
    intros x t Hlk. apply persist_lift.
  Qed.

End PersistLift.

Lemma inst_refl {Θ} {reflΘ : Refl Θ} {lkreflΘ : LkRefl Θ} :
  forall w (ι : Assignment w), inst (refl (Θ := Θ)) ι = ι.
Proof.
  intros. apply env.lookup_extensional. intros α αIn. unfold inst, inst_acc.
  now rewrite env.lookup_tabulate, lk_refl.
Qed.

Lemma inst_trans {Θ} {transΘ : Trans Θ} {lktransΘ : LkTrans Θ} :
  forall w0 w1 w2 (θ1 : Θ w0 w1) (θ2 : Θ w1 w2) (ι : Assignment w2),
    inst (trans θ1 θ2) ι = inst θ1 (inst θ2 ι).
Proof.
  intros. apply env.lookup_extensional. intros α αIn. unfold inst, inst_acc.
  now rewrite ?env.lookup_tabulate, lk_trans, inst_persist.
Qed.

Lemma inst_step_snoc {Θ} {stepΘ : Step Θ} {lkStepΘ : LkStep Θ}
  {w x} (ι : Assignment w) (t : Ty) :
  inst (step (Θ := Θ)) (env.snoc ι x t) = ι.
Proof.
  apply env.lookup_extensional. intros α αIn. unfold inst, inst_acc.
  rewrite env.lookup_tabulate. rewrite lk_step. reflexivity.
Qed.

Lemma inst_step {Θ} {stepΘ : Step Θ} {lkStepΘ : LkStep Θ}
  {w x} (ι : Assignment (w ▻ x)) :
  inst (step (Θ := Θ)) ι = let (ι',_) := env.view ι in ι'.
Proof. destruct env.view. apply inst_step_snoc. Qed.

Lemma inst_thin {Θ} {thinΘ : Thin Θ} {lkthinΘ : LkThin Θ}
  {w} (ι : Assignment w) {α} (αIn : α ∈ w) :
  inst (thin α) ι = env.remove α ι αIn.
Proof.
  apply env.lookup_extensional. intros β βIn. unfold inst, inst_acc.
  rewrite env.lookup_tabulate. rewrite lk_thin. cbn.
  now rewrite env.lookup_thin.
Qed.

Lemma inst_thick {Θ} {thickΘ : Thick Θ} {lkthickΘ : LkThick Θ} :
  forall {w} {x} (xIn : x ∈ w) (t : Ṫy (w - x)) (ι : Assignment (w - x)),
    inst (thick (Θ := Θ) x t) ι = env.insert xIn ι (inst t ι).
Proof.
  intros. apply env.lookup_extensional. intros β βIn. unfold inst, inst_acc.
  rewrite env.lookup_tabulate, lk_thick. unfold thickIn.
  destruct world.occurs_check_view; cbn.
  - now rewrite env.lookup_insert.
  - now rewrite env.lookup_thin, env.remove_insert.
Qed.

Lemma inst_hmap `{LkHMap Θ1 Θ2} {w1 w2} (θ : Θ1 w1 w2) (ι : Assignment w2) :
  inst (hmap θ) ι = inst θ ι.
Proof.
  intros. apply env.lookup_extensional. intros β βIn. unfold inst, inst_acc.
  now rewrite !env.lookup_tabulate, lk_hmap.
Qed.

Lemma inst_direct_subterm {w} (t1 t2 : Ṫy w) (ι : Assignment w) :
  ṫy.Ṫy_direct_subterm t1 t2 ->
  ty.Ty_direct_subterm (inst t1 ι) (inst t2 ι).
Proof. intros []; constructor. Qed.

Lemma inst_subterm {w} (ι : Assignment w) (t1 t2 : Ṫy w) :
  ṫy.Ṫy_subterm t1 t2 -> ty.Ty_subterm (inst t1 ι) (inst t2 ι).
Proof.
  induction 1.
  - constructor 1. now apply inst_direct_subterm.
  - eapply t_trans; eauto.
Qed.

Lemma lookup_lift (Γ : Env) (x : string) (w : World) :
  lookup x (lift (w:=w) Γ) = option.map (fun t => lift t) (lookup x Γ).
Proof. unfold lift, lift_env. now rewrite <- lookup_fmap. Qed.

Lemma lookup_inst (w : World) (Γ : Ėnv w) (x : string) (ι : Assignment w) :
  lookup x (inst Γ ι) = inst (lookup x Γ) ι.
Proof. unfold inst at 1, inst_env. now rewrite lookup_fmap. Qed.

Lemma inst_insert {w} (Γ : Ėnv w) (x : string) (t : Ṫy w) (ι : Assignment w) :
  inst (insert (M := Ėnv w) x t Γ) ι = inst Γ ι ,, x ∷ inst t ι.
Proof. cbv [inst inst_env Ėnv]. now rewrite fmap_insert. Qed.

Lemma inst_empty {w} (ι : Assignment w) :
  inst (A := Ėnv) empty ι = empty.
Proof. cbv [inst inst_env Ėnv]. now rewrite fmap_empty. Qed.

Lemma lift_insert {w x t Γ} :
  lift (insert (M := Env) x t Γ) = insert (M := Ėnv w) x (lift t) (lift Γ).
Proof. unfold lift, lift_env. now rewrite fmap_insert. Qed.

Fixpoint grounding (w : World) : Assignment w :=
  match w with
  | world.nil      => env.nil
  | world.snoc Γ b => env.snoc (grounding Γ) b ty.bool
  end%world.

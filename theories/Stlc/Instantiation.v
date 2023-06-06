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
  Relations.Relation_Operators
  Strings.String.
From stdpp Require Import
  base gmap.
From Em Require Import
  Context
  Environment
  Prelude
  Stlc.Persistence
  Stlc.Spec
  Stlc.Worlds.

Import ctx.notations.

#[local] Set Implicit Arguments.

Notation Assignment := (@env.Env nat (fun _ => Ty)).

Class Inst (A : TYPE) (a : Type) : Type :=
  inst : forall {w}, A w -> Assignment w -> a.

#[export] Instance inst_list {A : TYPE} {a : Type} `{Inst A a} :
  Inst (List A) (list a) :=
  fun w xs ass => List.map (fun x => inst x ass) xs.

#[export] Instance inst_const {A} :
  Inst (Const A) A | 10 :=
  fun Σ x ι => x.

#[export] Instance inst_unit :
  Inst Unit unit :=
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

#[export] Instance inst_acc {Θ : ACC} :
  forall w, Inst (Θ w) (Assignment w).
Proof.
  intros w0 w1 θ ι.
  apply env.tabulate.
  intros α αIn.
  apply (inst (lk θ αIn) ι).
Defined.

Section Lift.
  Import World.notations.

  (* Indexes a given ty by a world Σ *)
  Fixpoint lift (t : Ty) : ⊢ʷ Ṫy :=
    fun w =>
      match t with
      | ty.bool       => ṫy.bool
      | ty.func t1 t2 => ṫy.func (lift t1 w) (lift t2 w)
      end.

  Definition liftEnv (E : Env) : ⊢ʷ Ėnv.
  Proof.
    intros w. revert E. unfold Ėnv. apply base.fmap.
    intros t. apply (lift t).
  Defined.

  Lemma inst_lift (w : World) (t : Ty) (ι : Assignment w) :
    inst (lift t w) ι = t.
  Proof. Admitted.

  Lemma inst_lift_env (w : World) (G : Env) (ι : Assignment w) :
    inst (liftEnv G w) ι = G.
  Proof. Admitted.

End Lift.

Lemma inst_persist {Θ : ACC}
  {AT A} {pers : Persistent AT} {instAT : Inst AT A}
  {w0 w1} (θ : Θ w0 w1) (t : AT w0) (ι : Assignment w1) :
  inst (persist t θ) ι = inst t (inst θ ι).
Proof. Admitted.

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

Lemma inst_reduce {Θ} {reduceΘ : Reduce Θ} :
  forall {w α t} (ι : Assignment w),
    inst (reduce α t) ι = env.snoc ι α (inst t ι).
Proof. Admitted.

Lemma inst_step {Θ} {stepΘ : Step Θ} :
  forall {w x} (ι : Assignment (w ▻ x)),
    inst (step (Θ := Θ)) ι = let (ι',_) := env.view ι in ι'.
Proof. Admitted.

Lemma inst_step_snoc {Θ} {stepΘ : Step Θ} :
  forall {w x} (ι : Assignment w) (t : Ty),
    inst (step (Θ := Θ)) (env.snoc ι x t) = ι.
Proof. intros. rewrite inst_step. reflexivity. Qed.

Lemma inst_thin {Θ} {thinΘ : Thin Θ}
  {w} (ι : Assignment w) {α} (αIn : α ∈ w) :
  inst (thin α) ι = env.remove α ι αIn.
Proof. Admitted.

Lemma inst_thick {Θ} {thickΘ : Thick Θ} :
  forall {w} {x} (xIn : x ∈ w) (t : Ṫy (w - x)) (ι : Assignment (w - x)),
      inst (thick (Θ := Θ) x t) ι = env.insert xIn ι (inst t ι).
Proof. Admitted.

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
  lookup x (liftEnv Γ w) =
    option.map (fun t => lift t w) (lookup x Γ).
Proof. unfold liftEnv. now rewrite <- lookup_fmap. Qed.

Lemma lookup_inst (w : World) (Γ : Ėnv w) (x : string) (ι : Assignment w) :
  lookup x (inst Γ ι) = inst (lookup x Γ) ι.
Proof.
  unfold inst at 1, inst_env.
  now rewrite lookup_fmap.
Qed.

Lemma inst_insert {w} (Γ : Ėnv w) (x : string) (t : Ṫy w) (ι : Assignment w) :
  inst (Γ ,, x∷t) ι = inst Γ ι ,, x ∷ inst t ι.
Proof. cbv [inst inst_env]. now rewrite fmap_insert. Qed.

Lemma inst_empty {w} (ι : Assignment w) :
  inst (A := Ėnv) empty ι = empty.
Proof. cbv [inst inst_env Ėnv]. now rewrite fmap_empty. Qed.

Lemma liftEnv_insert {w x t Γ} :
  liftEnv (insert x t Γ) w = insert x (lift t w) (liftEnv Γ w).
Proof. unfold liftEnv. now rewrite fmap_insert. Qed.

Lemma persist_liftTy {Θ : ACC} {w0 w1} t (θ : Θ w0 w1) :
  persist (lift t w0) θ = lift t w1.
Proof. induction t; cbn; f_equal; auto. Qed.

  (* Lemma persist_split : forall w w' iw (pos : w ↑ iw) (neg : iw ↓ w') x, *)
  (*   persist w  x iw pos -> *)
  (*   persist iw x w' neg -> *)
  (*   persist w  x w' {| iw := iw; pos := pos; neg := neg |}. *)

Lemma persist_liftEnv {Θ : ACC} {w0 w1} (e : Env) (θ : Θ w0 w1) :
  persist (liftEnv e w0) θ = liftEnv e w1.
Proof.
  unfold liftEnv, persist, persist_env. rewrite <- map_fmap_compose.
  apply (map_fmap_ext (M := gmap string)). intros _ t _.
  unfold compose. apply persist_liftTy.
Qed.

Fixpoint grounding (w : World) : Assignment w :=
  match w with
  | ctx.nil      => env.nil
  | ctx.snoc Γ b => env.snoc (grounding Γ) b ty.bool
  end%ctx.

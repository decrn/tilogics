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
     Context
     Environment
     Prelude
     Stlc.Instantiation
     Stlc.Spec
     Stlc.Persistence
     Stlc.Worlds.

Import ctx.notations.
Import World.notations.

#[local] Set Implicit Arguments.

Reserved Notation "w1 ⊑ˢ w2" (at level 80).

Module Sub.

  Canonical Structure Sub : ACC :=
    {| acc w0 w1        := @env.Env nat (fun _ => Ṫy w1) w0;
       lk w0 w1 θ α αIn := env.lookup θ αIn
    |}.

  #[local] Notation "w0 ⊑ˢ w1" := (acc Sub w0 w1).
  #[local] Notation "□ˢ A" := (Box Sub A) (at level 9, format "□ˢ A", right associativity).
  #[local] Notation subst t θ := (persist t θ) (only parsing).

  #[export] Instance refl_sub : Refl Sub :=
    fun w => env.tabulate (@ṫy.var w).
  #[export] Instance trans_sub : Trans Sub :=
    fix trans {w0 w1 w2} θ1 θ2 {struct θ1} :=
      match θ1 with
      | env.nil         => env.nil
      | env.snoc θ1 x t => env.snoc (trans θ1 θ2) x (persist t θ2)
      end.
  #[export] Instance thick_sub : Thick Sub :=
    fun w x xIn s => env.tabulate (thickIn xIn s).
  #[export] Instance thin_sub : Thin Sub :=
    fun w α αIn => env.tabulate (fun β βIn => ṫy.var (ctx.in_thin αIn βIn)).
  #[export] Instance step_sub : Step Sub :=
    fun w x => thin _ (αIn := ctx.in_zero).

  Definition up1 {w0 w1} (r01 : Sub w0 w1) {n} : Sub (w0 ▻ n) (w1 ▻ n) :=
    env.snoc (env.map (fun _ (t : Ṫy _) => persist t step) r01) n (ṫy.var ctx.in_zero).

  Ltac foldlk :=
    change (env.lookup ?θ ?αIn) with (@lk Sub _ _ θ _ αIn).

  #[export] Instance lk_refl_sub : LkRefl Sub.
  Proof.
    intros w α αIn.
    apply (env.lookup_tabulate (fun _ βIn => ṫy.var βIn)).
  Qed.

  #[export] Instance lk_trans_sub : LkTrans Sub.
  Proof.
    intros w0 w1 w2 θ1 θ2 α αIn.
    induction θ1; destruct (ctx.view αIn); cbn; now foldlk.
  Qed.

  #[export] Instance lk_thin_sub : LkThin Sub.
  Proof.
    intros w0 α αIn β βIn. unfold lk, thin, thin_sub; cbn.
    now rewrite env.lookup_tabulate.
  Qed.

  #[export] Instance lk_thick_sub : LkThick Sub.
  Proof.
    intros w0 α αIn t β βIn. unfold lk, thick, thick_sub; cbn.
    now rewrite env.lookup_tabulate.
  Qed.

  Lemma lk_up1_zero {w0 w1 x} (θ : Sub w0 w1) :
    lk (up1 θ (n := x)) ctx.in_zero = ṫy.var ctx.in_zero.
  Proof. reflexivity. Qed.

  Lemma lk_up1_succ {w0 w1 x} (θ : Sub w0 w1) {y} {yIn : y ∈ w0} :
    lk (up1 θ (n := x)) (ctx.in_succ yIn) = persist (lk θ yIn) step.
  Proof. cbn - [step]. now rewrite env.lookup_map. Qed.

  (* #[export] Instance persist_preorder_sub {T} `{Persistent T} : PersistPreOrder Sub T. *)
  (* Proof. *)
  (*   (* constructor; intros w t *. *) *)
  (*   (* - induction t; cbn; f_equal; now rewrite ?lk_refl. *) *)
  (*   (* - induction t; cbn; f_equal; now rewrite ?lk_trans. *) *)
  (* Admitted. *)

  #[export] Instance refltrans_sub : ReflTrans Sub.
  Proof.
    constructor.
    - intros. apply env.lookup_extensional. intros. foldlk.
      now rewrite lk_trans, lk_refl.
    - intros. apply env.lookup_extensional. intros. foldlk.
      now rewrite lk_trans, persist_refl.
    - intros. apply env.lookup_extensional. intros. foldlk.
      now rewrite ?lk_trans, persist_trans.
  Qed.

  (* #[export] Instance InstSub : forall w, Inst (Sub w) (Assignment w) := *)
  (*   fun w0 w1 r ι => env.map (fun _ (t : Ty w1) => inst t ι) r. *)
  (*   (* fix instsub {w0 w1} (r : Sub w0 w1) (ι : Assignment w1) {struct r} := *) *)
  (*   (*   match r with *) *)
  (*   (*   | env.nil        => env.nil *) *)
  (*   (*   | env.snoc r _ t => env.snoc (inst (Inst := @instsub _) r ι) _ (inst t ι) *) *)
  (*   (*   end. *) *)

  Lemma comp_thin_thick {w α} (αIn : α ∈ w) (s : Ṫy (w - α)) :
    trans (thin α) (thick α s) = refl.
  Proof.
    apply env.lookup_extensional. intros β βIn. foldlk.
    rewrite lk_trans, lk_refl, lk_thin. cbn. foldlk.
    rewrite lk_thick. unfold thickIn.
    now rewrite ctx.occurs_check_view_thin.
  Qed.

  Lemma thin_thick_pointful {w α} (αIn : α ∈ w) (s : Ṫy (w - α)) (t : Ṫy (w - α)) :
    subst (subst t (thin α)) (thick α s) = t.
  Proof. now rewrite <- persist_trans, comp_thin_thick, persist_refl. Qed.

  (* Lemma subst_thin {w x} (xIn : x ∈ w) (t : Ṫy (w - x)) : *)
  (*   STLC.thin xIn T = subst T (thin xIn). *)
  (* Proof. induction T; cbn; f_equal; now rewrite ?lk_thin. Qed. *)

  Definition of {Θ : ACC} [w0 w1] (θ01 : Θ w0 w1) : Sub w0 w1 :=
    env.tabulate (@lk _ _ _ θ01).

  Lemma lk_of {Θ : ACC} [w0 w1] (θ : Θ w0 w1) α (αIn : α ∈ w0) :
    lk (of θ) αIn = lk θ αIn.
  Proof. unfold of, lk at 1; cbn. now rewrite env.lookup_tabulate. Qed.

  Lemma Ty_subterm_subst {w1 w2} (s t : Ṫy w1) (θ : Sub w1 w2) :
    ṫy.Ṫy_subterm s t -> ṫy.Ṫy_subterm (persist s θ) (persist t θ).
  Proof.
    unfold ṫy.Ṫy_subterm. induction 1; cbn.
    - constructor 1; destruct H; constructor.
    - econstructor 2; eauto.
  Qed.

  Lemma of_step {Θ} {stepΘ : Step Θ} {lkStepΘ : LkStep Θ} w α :
    of (@step Θ stepΘ w α) = step (Θ := Sub).
  Proof.
    apply env.lookup_extensional. intros β βIn. unfold of. cbn.
    rewrite !env.lookup_tabulate. now rewrite lk_step.
  Qed.

  Lemma of_thick {Θ} {thickΘ : Thick Θ} {lkThickΘ : LkThick Θ}
    w α αIn t :
    of (@thick Θ thickΘ w α αIn t) = thick (Θ := Sub) α t.
  Proof.
    apply env.lookup_extensional. intros β βIn. unfold of, thick at 2, thick_sub.
    now rewrite !env.lookup_tabulate, lk_thick.
  Qed.

  Lemma of_trans {Θ} {transΘ : Trans Θ} {lktransΘ : LkTrans Θ}
    {w0 w1 w2} (θ1 : Θ w0 w1) (θ2 : Θ w1 w2) :
    of (trans θ1 θ2) = trans (of θ1) (of θ2).
  Proof.
    apply env.lookup_extensional. intros α αIn. unfold of at 1.
    rewrite env.lookup_tabulate.
    change (lk (θ1 ⊙ θ2) αIn = lk (of θ1 ⊙ of θ2) αIn).
    rewrite !lk_trans, lk_of. apply persist_simulation.
    intros. now rewrite lk_of.
  Qed.

  Lemma persist_sim {Θ : ACC} {T} {persT : Persistent T} {persLT : PersistLaws T}
    [w0 w1] (θ : Θ w0 w1) :
    forall t, persist t (of θ) = persist t θ.
  Proof. intros. apply persist_simulation. intros. now rewrite lk_of. Qed.

  Lemma persist_sim_step {Θ} {stepΘ : Step Θ} {lkStepΘ : LkStep Θ}
    [T] {persT : Persistent T} {persLT : PersistLaws T}
    w α (t : T w) :
    persist t (step (Θ := Θ)) = persist t (step (Θ := Sub) (α := α)).
  Proof. now rewrite <- persist_sim, of_step. Qed.

End Sub.
Export Sub (Sub).
Notation "w0 ⊑ˢ w1" := (acc Sub w0 w1).

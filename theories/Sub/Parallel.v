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

From Em Require Import Environment Instantiation Persistence Prelude Spec Worlds.

Import world.notations.

Reserved Notation "w1 ⊑ˢ w2" (at level 80).

Module Par.

  Canonical Structure Par : SUB :=
    {| sub w0 w1        := env.Env (Ṫy w1) w0;
       lk w0 w1 θ α αIn := env.lookup θ αIn
    |}.

  #[local] Notation "w0 ⊑ˢ w1" := (sub Par w0 w1).
  #[local] Notation "□ˢ A" := (Box Par A) (at level 9, format "□ˢ A", right associativity).
  #[local] Notation subst t θ := (persist t θ) (only parsing).

  #[export] Instance refl_par : Refl Par :=
    fun w => env.tabulate (@ṫy.var w).
  #[export] Instance trans_par : Trans Par :=
    fix trans {w0 w1 w2} θ1 θ2 {struct θ1} :=
      match θ1 with
      | env.nil         => env.nil
      | env.snoc θ1 x t => env.snoc (trans θ1 θ2) x (persist t θ2)
      end.
  #[export] Instance thick_par : Thick Par :=
    fun w x xIn s => env.tabulate (thickIn xIn s).
  #[export] Instance thin_par : Thin Par :=
    fun w α αIn => env.tabulate (fun β βIn => ṫy.var (world.in_thin αIn βIn)).
  #[export] Instance step_par : Step Par :=
    fun w α => env.tabulate (fun β βIn => ṫy.var (world.in_succ βIn)).

  Ltac foldlk :=
    change (env.lookup ?θ ?αIn) with (@lk Par _ _ θ _ αIn).

  #[export] Instance lk_refl_par : LkRefl Par.
  Proof.
    intros w α αIn.
    apply (env.lookup_tabulate (fun _ βIn => ṫy.var βIn)).
  Qed.

  #[export] Instance lk_trans_par : LkTrans Par.
  Proof.
    intros w0 w1 w2 θ1 θ2 α αIn.
    induction θ1; destruct (world.view αIn); cbn; now foldlk.
  Qed.

  #[export] Instance lk_step_par : LkStep Par.
  Proof.
    intros w α αIn β. unfold lk, step, step_par; cbn.
    now rewrite env.lookup_tabulate.
  Qed.

  #[export] Instance lk_thin_par : LkThin Par.
  Proof.
    intros w0 α αIn β βIn. unfold lk, thin, thin_par; cbn.
    now rewrite env.lookup_tabulate.
  Qed.

  #[export] Instance lk_thick_par : LkThick Par.
  Proof.
    intros w0 α αIn t β βIn. unfold lk, thick, thick_par; cbn.
    now rewrite env.lookup_tabulate.
  Qed.

  #[export] Instance refltrans_par : ReflTrans Par.
  Proof.
    constructor.
    - intros. apply env.lookup_extensional. intros. foldlk.
      now rewrite lk_trans, lk_refl.
    - intros. apply env.lookup_extensional. intros. foldlk.
      now rewrite lk_trans, persist_refl.
    - intros. apply env.lookup_extensional. intros. foldlk.
      now rewrite ?lk_trans, persist_trans.
  Qed.

  Lemma comp_thin_thick {w α} (αIn : α ∈ w) (s : Ṫy (w - α)) :
    trans (thin α) (thick α s) = refl.
  Proof.
    apply env.lookup_extensional. intros β βIn. foldlk.
    rewrite lk_trans, lk_refl, lk_thin. cbn. foldlk.
    rewrite lk_thick. unfold thickIn.
    now rewrite world.occurs_check_view_thin.
  Qed.

  Lemma thin_thick_pointful {w α} (αIn : α ∈ w) (s : Ṫy (w - α)) (t : Ṫy (w - α)) :
    subst (subst t (thin α)) (thick α s) = t.
  Proof. now rewrite <- persist_trans, comp_thin_thick, persist_refl. Qed.

  #[export] Instance hmap_par {Θ : SUB} : HMap Θ Par :=
    fun w0 w1 θ => env.tabulate (@lk _ _ _ θ).

  #[export] Instance lk_hmap_par {Θ : SUB} : LkHMap Θ Par.
  Proof.
    intros w0 w1 θ a αIn.
    unfold hmap, hmap_par, lk at 1; cbn.
    now rewrite env.lookup_tabulate.
  Qed.

  Lemma Ty_subterm_subst {w1 w2} (s t : Ṫy w1) (θ : Par w1 w2) :
    ṫy.Ṫy_subterm s t -> ṫy.Ṫy_subterm (persist s θ) (persist t θ).
  Proof.
    unfold ṫy.Ṫy_subterm. induction 1; cbn.
    - constructor 1; destruct H; constructor.
    - econstructor 2; eauto.
  Qed.

  Lemma hmap_step {Θ} {stepΘ : Step Θ} {lkStepΘ : LkStep Θ} w α :
    hmap (@step Θ stepΘ w α) = step (Θ := Par).
  Proof.
    apply env.lookup_extensional. intros β βIn.
    foldlk. now rewrite lk_hmap, !lk_step.
  Qed.

  Lemma hmap_thick {Θ} {thickΘ : Thick Θ} {lkThickΘ : LkThick Θ}
    w α (αIn : α ∈ w) t :
    hmap (thick (Θ := Θ) α t) = thick (Θ := Par) α t.
  Proof.
    apply env.lookup_extensional. intros β βIn.
    foldlk. now rewrite lk_hmap, !lk_thick.
  Qed.

  Lemma persist_hmap {Θ : SUB} {T} {persT : Persistent T} {persLT : PersistLaws T}
    [w0 w1] (θ : Θ w0 w1) :
    forall t, persist t (hmap θ) = persist t θ.
  Proof. intros. apply persist_simulation. intros. now rewrite lk_hmap. Qed.

End Par.
Export Par (Par).
Notation "w0 ⊑ˢ w1" := (sub Par w0 w1).
Infix "⊙ˢ" := (trans (Θ := Par)) (at level 60, right associativity).
Notation "□ˢ A" := (Box Par A)
  (at level 9, right associativity, format "□ˢ A") : indexed_scope.
Notation "◇ˢ A" := (Diamond Par A)
  (at level 9, right associativity, format "◇ˢ A") : indexed_scope.

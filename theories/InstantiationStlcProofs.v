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


#[export] Instance inst_lift_ty : InstLift OTy Ty.
Proof. intros w t ι. induction t; cbn; f_equal; auto. Qed.

#[export] Instance inst_lift_env : InstLift OEnv Env.
Proof.
  intros w E ι. unfold inst, inst_env, lift, lift_env.
  rewrite <- map_fmap_id, <- map_fmap_compose.
  apply map_fmap_ext. intros x t Hlk. apply inst_lift.
Qed.

#[export] Instance subst_lift_ty : SubstLift OTy Ty.
Proof. intros Θ w0 w1 t θ. induction t; cbn; f_equal; auto. Qed.

#[export] Instance subst_lift_env : SubstLift OEnv Env.
Proof.
  intros Θ w0 w1 E θ. unfold subst, lift, subst_env, lift_env, OEnv.
  rewrite <- map_fmap_compose. apply map_fmap_ext.
  intros x t Hlk. apply subst_lift.
Qed.

Lemma inst_direct_subterm {w} (t1 t2 : OTy w) (ι : Assignment w) :
  oty.OTy_direct_subterm t1 t2 ->
  ty.Ty_direct_subterm (inst t1 ι) (inst t2 ι).
Proof. intros []; constructor. Qed.

Lemma inst_subterm {w} (ι : Assignment w) (t1 t2 : OTy w) :
  oty.OTy_subterm t1 t2 -> ty.Ty_subterm (inst t1 ι) (inst t2 ι).
Proof.
  induction 1.
  - constructor 1. now apply inst_direct_subterm.
  - eapply t_trans; eauto.
Qed.

Lemma lookup_lift (Γ : Env) (x : string) (w : World) :
  lookup x (lift (w:=w) Γ) = option.map (fun t => lift t) (lookup x Γ).
Proof. unfold lift, lift_env. now rewrite <- lookup_fmap. Qed.

Lemma lookup_inst (w : World) (Γ : OEnv w) (x : string) (ι : Assignment w) :
  lookup x (inst Γ ι) = inst (lookup x Γ) ι.
Proof. unfold inst at 1, inst_env. now rewrite lookup_fmap. Qed.

Lemma inst_insert {w} (Γ : OEnv w) (x : string) (t : OTy w) (ι : Assignment w) :
  inst (insert (M := OEnv w) x t Γ) ι = inst Γ ι ,, x ∷ inst t ι.
Proof. cbv [inst inst_env OEnv]. now rewrite fmap_insert. Qed.

Lemma inst_empty {w} (ι : Assignment w) : inst (A := OEnv) empty ι = empty.
Proof. cbv [inst inst_env OEnv]. now rewrite fmap_empty. Qed.

Lemma lift_insert {w x t Γ} :
  lift (insert (M := Env) x t Γ) = insert (M := OEnv w) x (lift t) (lift Γ).
Proof. unfold lift, lift_env. now rewrite fmap_insert. Qed.

#[export] Instance inst_subst_ty : InstSubst OTy Ty.
Proof.
  intros Θ w0 w1 θ t ι. induction t; cbn; f_equal; auto.
  unfold inst at 2, inst_sub. now rewrite env.lookup_tabulate.
Qed.

#[export] Instance inst_subst_env : InstSubst OEnv Env.
Proof.
  intros Θ w0 w1 θ E ι. unfold subst, subst_env, inst at 1 2, inst_env.
  rewrite <- map_fmap_compose. apply map_fmap_ext.
  intros x t Hlk. apply inst_subst.
Qed.

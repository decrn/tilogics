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

#[export] Instance substlaws_ty : SubstLaws OTy.
Proof.
  constructor.
  - intros * ? w t. induction t; cbn.
    + apply lk_refl.
    + reflexivity.
    + now f_equal.
  - intros * ? w0 t *. induction t; cbn.
    + apply lk_trans.
    + reflexivity.
    + now f_equal.
  - intros ? ? ? t * Heq. induction t; cbn; f_equal; auto.
Qed.

#[export] Instance substlaws_env : SubstLaws OEnv.
Proof.
  constructor.
  - intros * ? w Γ. unfold subst, subst_env, OEnv.
    apply map_eq. intros x. rewrite lookup_fmap.
    destruct lookup as [t|]; cbn; f_equal.
    apply subst_refl.
  - intros * ? w0 Γ *. unfold subst, subst_env, OEnv.
    apply map_eq. intros x. rewrite !lookup_fmap.
    destruct lookup as [t|]; cbn; f_equal.
    apply subst_trans.
  - intros ? ? ? t * Heq. unfold subst, subst_env.
    apply (map_fmap_ext _ _ t). intros x s _. clear - Heq.
    now apply subst_simulation.
Qed.

Lemma lookup_subst {Θ : SUB}
  {w0 w1} (θ : Θ w0 w1) (G : OEnv w0) (x : string) :
  lookup x (subst G θ) = subst (lookup x G) θ.
Proof.
  unfold subst at 1, subst_env, OEnv.
  now rewrite lookup_fmap.
Qed.

Lemma subst_empty {Θ : SUB}
  {w0 w1} (θ : Θ w0 w1) :
  subst (empty (A := OEnv w0)) θ = empty.
Proof.
  apply (fmap_empty (M := gmap string)).
Qed.

Lemma subst_insert {Θ : SUB}
  {w0 w1} (θ : Θ w0 w1) (G : OEnv w0) (x : string) (t : OTy w0) :
  subst (insert x t G) θ = insert x (subst t θ) (subst G θ).
Proof. unfold subst, subst_env, OEnv. now rewrite fmap_insert. Qed.

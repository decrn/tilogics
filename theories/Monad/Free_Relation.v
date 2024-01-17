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

Require Import Coq.Classes.RelationClasses.
From iris Require Import proofmode.tactics.
From Em Require Import
  Monad.Interface
  Shallow.Interface
  Related.Interface
  Prefix.
From Em Require Free_Shallow Free_Deep.
Import (hints) Free_Shallow Free_Deep.

Module S := Free_Shallow.
Module D := Free_Deep.

Import Pred Pred.notations Pred.Sub Pred.proofmode world.notations.

#[local] Set Implicit Arguments.

Import logicalrelation.

Inductive RawFree (DA : OType) (SA : Type) (RA : Rel DA SA) : RawRel (D.Free DA) (S.Free SA) :=
  | ret : forall w da sa ass, RSat RA da sa ass -> @RawFree DA SA RA w (D.Ret da) (S.Ret sa) ass
  | pickk w α (dk : D.Free DA (w ، α)) (sk : Ty -> S.Free SA) ass
          (rk : forall st, @RawFree DA SA RA (w ، α) dk (sk st) (env.snoc ass α st))
    : @RawFree DA SA RA w (D.Pickk α dk) (S.Pickk sk) ass.

Goal False. match type of @pickk with ?t => let t' := eval cbv [RTy] in t in idtac t' end. Abort.

Definition RFree (DA : OType) (SA : Type) (RA : Rel DA SA) : Rel (D.Free DA) (S.Free SA) :=
  MkRel (RawFree RA).

Definition rwp {DA SA} (RA : Rel DA SA) : Rel (D.Free DA ⇢ Box Prefix (DA ⇢ Pred) ⇢ Pred) (S.Free SA -> (SA -> Prop) -> Prop).
apply RImpl. apply RFree. apply RA. apply RImpl. apply RBox. apply RImpl. apply RA. all: apply RPred. Defined.

#[export] Instance rpure_free : RPure RFree.
Proof.
  intros DA SA RA.
  intros w.
  cbn.
  constructor.
  intros ι _ da sa ra.
  now constructor.
Qed.

(* Lemma wlps_are_related : Prop. *)
(*   eapply rwp. exact RTy. apply D.wp_free. apply S.wp_free. apply env.nil. Abort. *)
(* (* Generalizing *) *)
(* Lemma wlps_are_related : forall w ass, rwp RTy (@D.wp_free OTy w) (S.wp_free (A:=Ty)) ass. *)
(*   intros w ass. unfold rwp. *)
(*   intros dm sm rm. induction rm; cbn; intros dpost spost rpost. *)
(*   - apply rpost. apply inst_refl. auto. *)
(*   - unfold RPred. unfold wp. setoid_rewrite inst_step. split. *)
(*     + intros. destruct H0. destruct env.view. exists v. specialize rk with v. destruct H0. unfold RArr, RBox in *. *)
(*       specialize (H v (_4 dpost step) spost). subst. eapply H in H1. auto. intros w' θ ass' eq. *)
(*       unfold _4. apply rpost. rewrite inst_trans inst_step eq. now simpl. *)
(*     + intros. destruct H0. exists (env.snoc ass α x). cbn. split. auto. eapply H; eauto. intros w' θ ass' eq. apply rpost. rewrite inst_trans inst_step eq. now simpl. *)
(* Qed. *)

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

From Em Require Import Prelude Instantiation Spec Persistence Worlds.

Module Open.

  Definition Open (A : Type) : OType :=
    fun w => Assignment w → A.

  (* pure  :: a -> f a *)
  Definition pure {A} (a : A) : Valid (Open A) := fun _ _ => a.
  #[global] Arguments pure {A} _ {w} ι/.

  Definition fmap {A B} (f : A -> B) : ⊧ Open A ⇢ Open B :=
    fun w a ι => f (a ι).
  #[global] Arguments fmap {A B} _ {w} a ι/.

  (* ap :: f (a -> b) -> f a -> f b *)
  Definition ap {A B : Type} : ⊧ Open (A → B) ⇢ Open A ⇢ Open B :=
    fun w f a ι => f ι (a ι).
  #[global] Arguments ap {A B} [w] f a ι/.

  #[export] Instance inst_sem {A} : Inst (Open A) A :=
    fun w x ι => x ι.
  #[global] Arguments inst_sem {A} [w] x ι/.

  #[export] Instance lift_sem {A} : Lift (Open A) A :=
    pure.

  #[export] Instance persistent_sem {A} : Persistent (Open A) :=
    fun Θ w0 t w1 θ ι => t (inst θ ι).

  #[export] Instance inst_lift_sem {A} : InstLift (Open A) A.
  Proof. easy. Qed.

  #[export] Instance inst_persist_sem {A} : InstPersist (Open A) A.
  Proof. easy. Qed.

  #[export] Instance persist_lift_sem {A} : PersistLift (Open A) A.
  Proof. easy. Qed.

  Section InstLemmas.

    Lemma inst_pure {A w} {ι : Assignment w} (a : A) :
      inst (pure a) ι = a.
    Proof. reflexivity. Qed.

    Lemma inst_fmap {A B} (f : A -> B) [w0] (a : Open A w0) (ι : Assignment w0) :
      inst (fmap f a) ι = f (inst a ι).
    Proof. reflexivity. Qed.

    Lemma inst_ap {A B} [w0] (f : Open (A -> B) w0) (a : Open A w0) (ι : Assignment w0) :
      inst (ap f a) ι = (inst f ι) (inst a ι).
    Proof. reflexivity. Qed.

  End InstLemmas.

  Section PersistLemmas.
    Context {Θ : SUB}.

    Lemma persist_pure {A} (a : A) [w0 w1] (θ : Θ w0 w1) :
      persist (pure a) θ = pure a.
    Proof. reflexivity. Qed.

    Lemma persist_fmap {A B} (f : A -> B) [w0] (a : Open A w0) [w1] (θ : Θ w0 w1) :
      persist (fmap f a) θ = fmap f (persist a θ).
    Proof. reflexivity. Qed.

    Lemma persist_app {A B} [w0] (f : Open (A -> B) w0) (a : Open A w0) [w1] (θ : Θ w0 w1) :
      persist (ap f a) θ = ap (persist f θ) (persist a θ).
    Proof. reflexivity. Qed.

  End PersistLemmas.

  Definition decode_ty : ⊧ OTy ⇢ Open Ty := fun w t => inst t.
  #[global] Arguments decode_ty [w] _.
  (* Definition decode_env : ⊧ OEnv ⇢ Open Env := fun w G => inst G. *)
  (* #[global] Arguments decode_env [w] _. *)

  Module notations.

    Notation "f <$> a" := (@Open.fmap _ _ f _ a) (at level 61, left associativity).
    Notation "f <*> a" := (@Open.ap _ _ _ f a) (at level 61, left associativity).

  End notations.

End Open.
Export (hints) Open.
Export Open (Open).

Notation OExp := (Open Exp).
Module oexp.
  Import Open Open.notations.

  Set Implicit Arguments.
  Set Maximal Implicit Insertion.

  Definition var : ⊧ Const string ⇢ OExp :=
    fun _ x => Open.pure (exp.var x).
  Definition true : ⊧ OExp :=
    fun _ => Open.pure exp.true.
  Definition false : ⊧ OExp :=
    fun _ => Open.pure exp.false.
  Definition ifte : ⊧ OExp ⇢ OExp ⇢ OExp ⇢ OExp :=
    fun _ e1 e2 e3 => exp.ifte <$> e1 <*> e2 <*> e3.
  Definition absu : ⊧ Const string ⇢ OExp ⇢ OExp :=
    fun _ x e => exp.absu x <$> e.
  Definition abst : ⊧ Const string ⇢ OTy ⇢ OExp ⇢ OExp :=
    fun _ x t e => exp.abst x <$> decode_ty t <*> e.
  Definition app : ⊧ OExp ⇢ OExp ⇢ OExp :=
    fun _ e1 e2 => exp.app <$> e1 <*> e2.

  Section InstLemmas.
    Context {w} (ι : Assignment w).
    Lemma inst_var x : inst (var x) ι = exp.var x.
    Proof. reflexivity. Qed.
    Lemma inst_true : inst true ι = exp.true.
    Proof. reflexivity. Qed.
    Lemma inst_false : inst false ι = exp.false.
    Proof. reflexivity. Qed.
    Lemma inst_ifte e1 e2 e3 :
      inst (ifte e1 e2 e3) ι = exp.ifte (inst e1 ι) (inst e2 ι) (inst e3 ι).
    Proof. reflexivity. Qed.
    Lemma inst_absu x e :
      inst (absu x e) ι = exp.absu x (inst e ι).
    Proof. reflexivity. Qed.
    Lemma inst_abst x t e :
      inst (abst x t e) ι = exp.abst x (inst t ι) (inst e ι).
    Proof. reflexivity. Qed.
    Lemma inst_app e1 e2 :
      inst (app e1 e2) ι = exp.app (inst e1 ι) (inst e2 ι).
    Proof. reflexivity. Qed.
  End InstLemmas.

End oexp.

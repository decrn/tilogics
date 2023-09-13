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
  Logic.FunctionalExtensionality.
From Em Require Import
  Environment
  Stlc.Instantiation
  Stlc.Spec
  Stlc.Persistence
  Stlc.Worlds.

Module Sem.
  Import World.notations.

  Definition Sem (A : Type) : TYPE :=
    fun w => Assignment w -> A.

  (* pure  :: a -> f a *)
  Definition pure {A} (a : A) : Valid (Sem A) := fun _ _ => a.
  #[global] Arguments pure {A} _ {w} ι/.

  Definition fmap {A B} (f : A -> B) : ⊢ʷ Sem A -> Sem B :=
    fun w a ι => f (a ι).
  #[global] Arguments fmap {A B} _ {w} a ι/.

  (* app :: f (a -> b) -> f a -> f b *)
  Definition app {A B : Type} : ⊢ʷ (Sem (A -> B)) -> Sem A -> Sem B :=
    fun w f a ι => f ι (a ι).
  #[global] Arguments app {A B} [w] f a ι/.

  (* <&> : f a -> f b -> f (a * b) *)
  Definition spaceship {A B : Type} : ⊢ʷ (Sem A) -> (Sem B) -> (Sem (A * B)) :=
    fun w a b ι => (a ι, b ι).

  #[export] Instance inst_sem {A} : Inst (Sem A) A :=
    fun w x ι => x ι.
  #[global] Arguments inst_sem {A} [w] x ι/.

  #[export] Instance lift_sem {A} : Lift (Sem A) A :=
    pure.

  #[export] Instance persistent_sem {A} : Persistent (Sem A) :=
    fun Θ w0 t w1 θ ι => t (inst θ ι).

  #[export] Instance persistlaws_sem {A} : PersistLaws (Sem A).
  Proof.
    constructor.
    - intros. cbv [persist persistent_sem].
      extensionality ι. now rewrite inst_refl.
    - intros. cbv [persist persistent_sem].
      extensionality ι. now rewrite inst_trans.
    - intros. cbv [persist persistent_sem].
      extensionality ι. f_equal.
      apply env.lookup_extensional. intros α αIn.
      change (inst (ṫy.var αIn) (inst θ1 ι) = inst (ṫy.var αIn) (inst θ2 ι)).
      rewrite <- ?inst_persist. f_equal. cbn. apply H.
  Qed.

  #[export] Instance inst_persist_sem {A} : InstPersist (Sem A) A.
  Proof. easy. Qed.

  Section PersistLemmas.
    Context {Θ : ACC}.

    Lemma persist_pure {A} (a : A) [w0 w1] (θ : Θ w0 w1) :
      persist (pure a) θ = pure a.
    Proof. reflexivity. Qed.

    Lemma persist_fmap {A B} (f : A -> B) [w0] (a : Sem A w0) [w1] (θ : Θ w0 w1) :
      persist (fmap f a) θ = fmap f (persist a θ).
    Proof. reflexivity. Qed.

    Lemma persist_app {A B} [w0] (f : Sem (A -> B) w0) (a : Sem A w0) [w1] (θ : Θ w0 w1) :
      persist (app f a) θ = app (persist f θ) (persist a θ).
    Proof. reflexivity. Qed.

  End PersistLemmas.

  Definition decode_ty : ⊢ʷ Ṫy -> Sem Ty := fun w t => inst t.
  #[global] Arguments decode_ty [w] _.
  Definition decode_env : ⊢ʷ Ėnv -> Sem Env := fun w G => inst G.
  #[global] Arguments decode_env [w] _.

End Sem.
Export (hints) Sem.
Export Sem (Sem).

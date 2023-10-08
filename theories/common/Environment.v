(******************************************************************************)
(* Copyright (c) 2019 Steven Keuchel, Dominique Devriese, Georgy Lukyanov     *)
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

From Em Require Import
     Context Prelude.
Import world.notations.

#[local] Set Implicit Arguments.

Declare Scope env_scope.
Delimit Scope env_scope with env.

Module env.

Section WithBinding.

  Section WithDom.
    Context {D : Set}.

    Inductive Env : World → Set :=
    | nil                              : Env []
    | snoc {w} (E : Env w) {α} (d : D) : Env (w ▻ α).

    Variant NilView : Env [] → Set :=
      isNil : NilView nil.

    Variant SnocView {w α} : Env (w ▻ α) → Set :=
      isSnoc (E : Env w) (v : D) : SnocView (snoc E v).

    Definition view (w : World) (E : Env w) :
      match w with
      | []    => NilView
      | w ▻ α => SnocView
      end E :=
      match E with
      | nil      => isNil
      | snoc E v => isSnoc E v
      end.

    Fixpoint lookup {w} (E : Env w) : ∀ [α], α ∈ w → D :=
      match E with
      | nil      => fun _ αIn => match world.view αIn with end
      | snoc E v => fun _ αIn => match world.view αIn with
                                 | world.isZero      => v
                                 | world.isSucc αIn' => lookup E αIn'
                                 end
      end.

    Fixpoint tabulate {w} : (∀ α, α ∈ w → D) → Env w :=
      match w with
      | []    => fun _ => nil
      | w ▻ α => fun Ewα =>
                   snoc
                     (tabulate (fun β βIn => Ewα β (world.in_succ βIn)))
                     (Ewα _ world.in_zero)
      end.

    Fixpoint remove {Γ b} (E : Env Γ) : ∀ (bIn : b ∈ Γ), Env (Γ - b) :=
      match E with
      | nil      => fun bIn => match world.view bIn with end
      | snoc E d => fun bIn =>
                      match world.view bIn return Env (_ - _) with
                      | world.isZero => E
                      | world.isSucc i => snoc (remove E i) d
                      end
      end.
    #[global] Arguments remove {_} b E.

    Fixpoint insert {Γ b} (bIn : b ∈ Γ) : Env (Γ - b) → D → Env Γ :=
      match bIn with
      | world.in_zero     => fun E v => snoc E v
      | world.in_succ bIn => fun E v =>
        let (E,v') := view E in
        snoc (insert bIn E v) v'
      end.

    Lemma remove_insert {b} {Γ} (bIn : b ∈ Γ) (v : D) (E : Env (Γ - b)) :
      remove b (insert bIn E v) bIn = E.
    Proof. induction bIn; cbn in *. easy. destruct view. cbn. now f_equal. Qed.

    Lemma insert_remove {b} {Γ} (bIn : b ∈ Γ) (E : Env Γ) :
      insert bIn (remove b E bIn) (lookup E bIn) = E.
    Proof. induction E; destruct (world.view bIn); cbn; now f_equal. Qed.

    Lemma lookup_insert {b Γ} (bIn : b ∈ Γ) (v : D) (E : Env (Γ - b)) :
      lookup (insert bIn E v) bIn = v.
    Proof. induction bIn; cbn in *. easy. destruct view. cbn. now f_equal. Qed.

    Lemma lookup_thin {b Γ b'} {E : Env Γ} {bIn : b ∈ Γ} (i : b' ∈ Γ - b) :
      lookup E (world.in_thin bIn i) = lookup (remove b E bIn) i.
    Proof.
      induction bIn; destruct (view E); cbn. easy.
      destruct (world.view i); cbn; auto.
    Qed.

    Lemma lookup_extensional {Γ} (E1 E2 : Env Γ) :
      (∀ {b} (bInΓ : b ∈ Γ), lookup E1 bInΓ = lookup E2 bInΓ) →
      E1 = E2.
    Proof.
      induction E1; destruct (view E2); [easy|]. intros Heq. f_equal.
      - apply IHE1. intros ? bIn. apply (Heq _ (world.in_succ bIn)).
      - apply (Heq _ world.in_zero).
    Qed.

    Lemma lookup_tabulate {Γ} (g : ∀ b, b ∈ Γ → D) [b] (bIn : b ∈ Γ) :
      lookup (tabulate g) bIn = g b bIn.
    Proof. induction bIn; cbn; [easy|apply IHbIn]. Qed.

  End WithDom.

  Arguments Env : clear implicits.

  Section Map.

    Context {D1 D2 : Set} (f : D1 → D2).

    Fixpoint map [Γ] (E : Env D1 Γ) : Env D2 Γ :=
      match E with
      | nil       => nil
      | snoc E db => snoc (map E) (f db)
      end.

    Lemma lookup_map {Γ} (E : Env D1 Γ) :
      ∀ [b] (bInΓ : b ∈ Γ), lookup (map E) bInΓ = f (lookup E bInΓ).
    Proof.
      induction E; intros x xIn; destruct (world.view xIn); cbn; now subst.
    Qed.

  End Map.

End WithBinding.

#[global] Arguments Env D w : clear implicits.
#[global] Arguments nil {D}.
#[global] Arguments snoc {D w%world} E%env α & d.

Ltac destroy x :=
  try (progress hnf in x);
  lazymatch type of x with
  | Env _ []       => destruct (view x)
  | Env _ (_ ▻ _)  => destruct (view x) as [x]; destroy x
  | _ ∈ []         => destruct (world.view x)
  | _ ∈ _ ▻ _      => destruct (world.view x)
  | _              => idtac
  end.

End env.
Export env (Env).
Bind Scope env_scope with Env.

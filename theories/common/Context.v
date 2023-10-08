(******************************************************************************)
(* Copyright (c) 2019 Steven Keuchel, Georgy Lukyanov                         *)
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

From Equations Require Import Equations.
From Em Require Import Prelude.

#[local] Unset Equations Derive Equations.
#[local] Set Transparent Obligations.

Declare Scope world_scope.
Delimit Scope world_scope with world.

Module Import world.

  (* Type of contexts. This is a list of bindings of type B. This type and
     subsequent types use the common notation of snoc lists. *)
  Inductive World : Type :=
  | nil
  | snoc (w : World) (α : nat).
  Derive NoConfusion EqDec for World.

  (* In represents context containment proofs. This is essentially a
     well-typed de Bruijn index, i.e. a de Bruijn index with a proof that it
     resolves to the binding b.  *)
  Inductive In α : World → Type :=
  | in_zero {w} : α ∈ snoc w α
  | in_succ {w β} (αIn : α ∈ w) : α ∈ snoc w β
  where "α ∈ w" := (In α w%world).
  Section WithUIP.
    Set Equations With UIP.
    Derive Signature NoConfusion EqDec for In.
  End WithUIP.
  Existing Class In.
  #[global] Arguments in_zero {α w}.
  #[global] Arguments in_succ {α w β} _.

  (* We define views on [In] which allows us to define mechanisms for
     reusable dependent pattern matching. For more information on views as a
     programming technique see:
     - Ulf Norell (2009), "Dependently Typed Programming in Agda." AFP'08.
       https://doi.org/10.1007/978-3-642-04652-0_5
     - Philip Wadler (1987). "Views: a way for pattern matching to cohabit
       with data abstraction." POPL'87.
       https://doi.org/10.1145/41625.41653
     - Conor McBride & James McKinna (2004). "The view from the left." JFP'04.
       https://doi.org/10.1017/S0956796803004829 *)

  (* A view expressing that membership in the empty context is uninhabited. *)
  Variant NilView [α] (αIn : In α nil) : Type :=.

  (* A view for membership in a non-empty context. *)
  Variant SnocView {β w} : ∀ [α], α ∈ snoc w β → Type :=
  | isZero                   : SnocView in_zero
  | isSucc {α} (αIn : α ∈ w) : SnocView (in_succ αIn).

  (* Instead of defining separate view functions, that construct a value
     of the *View datatypes, we use a single definition. This way, we
     avoid definition dummy definitions the other cases like it is usually
     done in small inversions. We simply define inversions for all cases at
     once. *)
  Definition view {w α} (αIn : α ∈ w) :
    match w return ∀ β, β ∈ w → Type with
    | nil      => NilView
    | snoc _ _ => SnocView
    end α αIn :=
    match αIn with
    | in_zero   => isZero
    | in_succ i => isSucc i
    end.

  Fixpoint remove {w} α {αIn : α ∈ w} : World :=
    match αIn with
    | @in_zero _ w        => w
    | @in_succ _ _ β αIn' => snoc (remove α) β
    end.
  #[global] Arguments remove _ _ {_}.

  Fixpoint in_thin {w α} (αIn : α ∈ w) [β] : β ∈ remove w α → β ∈ w :=
    match αIn with
    | in_zero      => in_succ
    | in_succ αIn' => fun βIn =>
                        match view βIn with
                        | isZero      => in_zero
                        | isSucc βIn' => in_succ (in_thin αIn' βIn')
                        end
    end.

  Inductive OccursCheckView {w α} (αIn : In α w) : ∀ [β], In β w → Type :=
  | Same                               : OccursCheckView αIn αIn
  | Diff {β} (βIn : In β (remove w α)) : OccursCheckView αIn (in_thin αIn βIn).

  Equations occurs_check_view {w α β} (αIn : In α w) (βIn : In β w) :
    OccursCheckView αIn βIn :=
  | in_zero      , in_zero      => Same in_zero
  | in_zero      , in_succ βIn' => Diff in_zero βIn'
  | in_succ αIn' , in_zero      => Diff (in_succ αIn') in_zero
  | in_succ αIn' , in_succ βIn' =>
      match occurs_check_view αIn' βIn' with
      | Same _     => Same (in_succ αIn')
      | Diff _ βIn' => Diff (in_succ αIn') (in_succ βIn')
      end.

  Lemma occurs_check_view_refl {w α} (αIn : In α w) :
    occurs_check_view αIn αIn = Same αIn.
  Proof. induction αIn; cbn; now rewrite ?IHαIn. Qed.

  Lemma occurs_check_view_thin {w α β} (αIn : In α w) (βIn : In β (remove w α)) :
    occurs_check_view αIn (in_thin αIn βIn) = Diff αIn βIn.
  Proof. induction αIn; [|destruct (view βIn)]; cbn; now rewrite ?IHαIn. Qed.

  Fixpoint max (w : World) : nat :=
    match w with
    | nil      => 0
    | snoc w α => Nat.max (max w) α
    end.
  Definition fresh (w : World) : nat :=
    S (max w).

  Module notations.

    Open Scope world_scope.

    Notation "'ε'" := nil (only parsing) : world_scope.
    Infix "▻" := snoc : world_scope.
    Notation "α ∈ w" := (In α w%world) : type_scope.

    (* Use the same notations as in ListNotations. *)
    Notation "[ ]" := (nil) : world_scope.
    Notation "w - x" := (remove w x) : world_scope.

  End notations.

End world.
Export world (World).
Export (hints) world.
Bind Scope world_scope with World.

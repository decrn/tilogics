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

From Coq Require Import Strings.String.
From Equations.Prop Require Import
  Equations EqDecInstances.
From stdpp Require Import base gmap.
From Em Require Export Prelude.

#[local] Unset Equations Derive Equations.
#[local] Set Transparent Obligations.

Declare Scope world_scope.
Delimit Scope world_scope with world.

Module Import world.

  #[export] Instance eqdec_string : EqDec string :=
    string_dec.

  (* Type of contexts. This is a list of bindings of type B. This type and
     subsequent types use the common notation of snoc lists. *)
  Inductive World : Type :=
  | nil
  | snoc (w : World) (α : string).
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
  Variant NilView [α] (αIn : α ∈ nil) : Type :=.

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

  (* Calculate a new world with the given element removed. The [remove] function
     and the subsequent [OccursCheckView] machinery are Based on:

     Chantal Keller and Thorsten Altenkirch (2010), "Hereditary substitutions
     for simple types, formalized." MSFP'10.
     https://doi.org/10.1145/1863597.1863601 *)
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

  Variant OccursCheckView {w α} (αIn : α ∈ w) : ∀ [β], β ∈ w → Type :=
  | Same                           : OccursCheckView αIn αIn
  | Diff {β} (βIn : β ∈ remove w α) : OccursCheckView αIn (in_thin αIn βIn).

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

  Lemma occurs_check_view_refl {w α} (αIn : α ∈ w) :
    occurs_check_view αIn αIn = Same αIn.
  Proof. induction αIn; cbn; now rewrite ?IHαIn. Qed.

  Lemma occurs_check_view_thin {w α β} (αIn : α ∈ w) (βIn : β ∈ remove w α) :
    occurs_check_view αIn (in_thin αIn βIn) = Diff αIn βIn.
  Proof. induction αIn; [|destruct (view βIn)]; cbn; now rewrite ?IHαIn. Qed.

  Module Import notations.

    Open Scope world_scope.

    Notation "'ε'" := nil : world_scope.
    Infix "،" := snoc (at level 61, left associativity) : world_scope.
    Notation "α ∈ w" := (In α w%world) : type_scope.
    Notation "w - x" := (remove w x) : world_scope.

  End notations.

  Section Fresh.
    Import Strings.Ascii Strings.String.
    Open Scope string_scope.

    Definition incr_char (a:ascii) : bool * ascii :=
      match a with
      |"a" => (false,"b")|"b" => (false,"c")|"c" => (false,"d")
      |"d" => (false,"e")|"e" => (false,"f")|"f" => (false,"g")
      |"g" => (false,"h")|"h" => (false,"i")|"i" => (false,"j")
      |"j" => (false,"k")|"k" => (false,"l")|"l" => (false,"m")
      |"m" => (false,"n")|"n" => (false,"o")|"o" => (false,"p")
      |"p" => (false,"q")|"q" => (false,"r")|"r" => (false,"s")
      |"s" => (false,"t")|"t" => (false,"u")|"u" => (false,"v")
      |"v" => (false,"w")|"w" => (false,"x")|"x" => (false,"y")
      |"y" => (false,"z")| _   => (true,"a")
      end%char.

    Fixpoint incr (s : string) : bool * string :=
      match s with
      | ""          => (false, "a")
      | String a "" => let (b, a') := incr_char a in
                       (b, String a' "")
      | String a s  => let (b, s') := incr s in
                       if b
                       then let (b', a') := incr_char a in
                            (b', String a' s')
                       else (false , String a s')
      end.

    Fixpoint string_to_pos_cont (s : string) (p : positive) : positive :=
      match s with
      | EmptyString => p
      | String c s => string_to_pos_cont s (strings.ascii_cons_pos c p)
      end.

    Definition shortlex_ltb (x y : string) : bool :=
      Pos.ltb (string_to_pos_cont x 1) (string_to_pos_cont y 1).

    Fixpoint max (α : string) (w : World) : string :=
      match w with
      | nil      => α
      | snoc w β => if shortlex_ltb α β then max β w else max α w
      end.

    Definition fresh (w : World) : string :=
      let (b, s') := incr (max "" w) in
      if b then String "a" s' else s'.

    Goal fresh nil        = "a".  reflexivity. Abort.
    Goal fresh (ε ، "1")  = "aa". reflexivity. Abort.
    Goal fresh (ε ، "a")  = "b".  reflexivity. Abort.
    Goal fresh (ε ، "z")  = "aa". reflexivity. Abort.
    Goal fresh (ε ، "~")  = "aa". reflexivity. Abort.
    Goal fresh (ε ، "aa") = "ab". reflexivity. Abort.

  End Fresh.

End world.
Export world (World, nil, snoc, fresh).
Export (hints) world.
Bind Scope world_scope with World.

Import world.notations.

Definition OType : Type := World → Type.

Module oty.

  #[local] Set Implicit Arguments.

  Inductive OTy (w : World) : Type :=
  | evar {α} (αIn : α ∈ w)
  | bool
  | func (t1 t2 : OTy w).
  #[global] Arguments evar {w α}.
  #[global] Arguments bool {w}.
  #[global] Arguments func {w} _ _.

  Set Equations With UIP.
  Derive NoConfusion Subterm EqDec for OTy.

  Lemma no_cycle {w} (t : OTy w) : ~ OTy_subterm t t.
  Proof.
    induction (well_founded_OTy_subterm t) as [? _ IH].
    intros Hx. apply (IH _ Hx Hx).
  Qed.

End oty.
Export oty (OTy).
Export (hints) oty.

Definition OEnv (w : World) :=
  stdpp.gmap.gmap string (OTy w).

(* Substitutions types as relations between worlds. Because we work with
   multiple different definitions of substitutions, we abstract many
   definitions over an relation. *)
Structure SUB : Type :=
  MkSub
    { sub :> World → World → Type;
      #[canonical=no] lk {w0 w1} (θ : sub w0 w1) α (αIn : α ∈ w0) : OTy w1;
    }.
#[global] Arguments sub Θ (_ _)%world_scope : rename, simpl never.
#[global] Arguments lk {Θ} [w0 w1] !θ [α] αIn : rename.

Class Refl (Θ : SUB) : Type :=
  refl w : Θ w w.
Class Trans (Θ : SUB) : Type :=
  trans w0 w1 w2 : Θ w0 w1 → Θ w1 w2 → Θ w0 w2.
#[global] Arguments refl {Θ _ w}.
#[global] Arguments trans {Θ _ w0 w1 w2} _ _.
Infix "⊙" := trans (at level 60, right associativity).

Class ReflTrans Θ {reflΘ : Refl Θ} {transΘ : Trans Θ} : Prop :=
  { trans_refl_l {w1 w2} {r : Θ w1 w2} :
      refl ⊙ r = r;
    trans_refl_r {w1 w2} {r : Θ w1 w2} :
      r ⊙ refl = r;
    trans_assoc {w0 w1 w2 w3} (r1 : Θ w0 w1) (r2 : Θ w1 w2) (r3 : Θ w2 w3) :
      (r1 ⊙ r2) ⊙ r3 = r1 ⊙ (r2 ⊙ r3);
  }.
#[global] Arguments ReflTrans Θ {_ _}.

Class HMap (Θ1 Θ2 : SUB) : Type :=
  hmap [w1 w2] : Θ1 w1 w2 → Θ2 w1 w2.
#[export] Instance hmap_refl {Θ} : HMap Θ Θ | 0 :=
  fun w1 w2 θ => θ.

Class Step (Θ : SUB) : Type :=
  step w α : Θ w (w ، α).
#[global] Arguments step {Θ _ w α}.

Class Thin (Θ : SUB) : Type :=
  thin w α {αIn : α ∈ w} : Θ (w - α) w.
#[global] Arguments thin {Θ _} [w] α {αIn}.

Class Thick (Θ : SUB) : Type :=
  thick w α {αIn : α ∈ w} (t : OTy (w - α)) : Θ w (w - α).
#[global] Arguments thick {Θ _} [w] α {αIn} t.

Definition Valid (A : OType) : Type := ∀ w, A w.
Polymorphic Definition Impl (A B : OType) : OType :=
  fun w => A w → B w.
Definition Forall {I : Type} (A : I → OType) : OType :=
  fun w => ∀ i : I, A i w.

Declare Scope indexed_scope.
Bind    Scope indexed_scope with OType.
Delimit Scope indexed_scope with W.

Definition Const (A : Type) : OType := fun _ => A.
Definition PROP : OType := fun _ => Prop.
Definition Unit : OType := fun _ => unit.
Definition Option (A : OType) : OType := fun w => option (A w).
Definition List (A : OType) : OType := fun w => list (A w).
Definition Prod (A B : OType) : OType := fun w => prod (A w) (B w).

Definition Box (Θ : SUB) (A : OType) : OType :=
  fun w0 => ∀ w1, Θ w0 w1 → A w1.

Definition Diamond (Θ : SUB) (A : OType) : OType :=
  fun w0 => {w1 & Θ w0 w1 * A w1}%type.

Declare Scope box_scope.
Bind    Scope box_scope with Box.
Delimit Scope box_scope with B.

Notation "⊧ A" := (Valid A%W) (at level 200, right associativity) : type_scope.
Notation "A ↠ B" := (Impl A B)
  (at level 99, B at level 200, right associativity) : indexed_scope.

Notation "A * B" := (Prod A%W B%W) : indexed_scope.
Notation "'∀' x .. y , P " :=
  (Forall (fun x => .. (Forall (fun y => P%W)) ..)) : indexed_scope.
Notation "( α ∈)" := (world.In α) (format "( α  ∈)") : indexed_scope.

Notation "◻ A" := (Box _ A%W)
  (at level 9, right associativity, format "◻ A").
(* Notation "◇ A" := (Diamond _ A) *)
(*   (at level 9, right associativity, format "◇ A") : indexed_scope. *)
Notation "▹ A" :=
  (fun (w : World) => ∀ α (αIn : α ∈ w), A%W (w - α))
    (at level 9, right associativity).

Definition _4 {Θ} {transΘ : Trans Θ} {A} : ⊧ Box Θ A ↠ Box Θ (Box Θ A) :=
  fun w0 a w1 θ1 w2 θ2 => a w2 (trans θ1 θ2).
#[global] Arguments _4 {Θ _ A} [_] _ [_] _ [_] _.

Definition thickIn [w x] (xIn : x ∈ w) (s : OTy (w - x)) :
  ∀ y, y ∈ w → OTy (w - x) :=
  fun y yIn =>
    match world.occurs_check_view xIn yIn with
    | world.Same _     => s
    | world.Diff _ yIn => oty.evar yIn
    end.
#[global] Arguments thickIn [w x] xIn s [y] yIn.

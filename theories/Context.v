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

From Coq Require Import
     Bool.Bool
     Arith.PeanoNat
     NArith.BinNat
     Numbers.DecimalString
     Strings.Ascii
     Strings.String.

From Equations Require Import Equations.
From MasterThesis Require Import
     Prelude.

Local Set Implicit Arguments.
Local Unset Equations Derive Equations.

Declare Scope ctx_scope.
Delimit Scope ctx_scope with ctx.

Module Binding.

  (* Local Set Primitive Projections. *)
  Local Set Transparent Obligations.

  Section WithNT.
    Context (N T : Set).

    Record Binding : Set :=
      MkB { name :> N; type :> T; }.

    Context {eqN : EqDec N} {eqT : EqDec T}.
    Derive NoConfusion EqDec for Binding.

  End WithNT.

  Arguments MkB [N T] name type.
  Arguments name {N T} b.
  Arguments type {N T} b.

End Binding.
Export Binding.

Module ctx.

  (* Type of contexts. This is a list of bindings of type B. This type and
     subsequent types use the common notation of snoc lists. *)
  Inductive Ctx (B : Set) : Set :=
  | nil
  | snoc (Γ : Ctx B) (b : B).

  Section TransparentObligations.
    Local Set Transparent Obligations.
    Derive NoConfusion for Ctx.
  End TransparentObligations.

  Arguments nil {_}.
  Arguments snoc {_} _%ctx _%ctx.

  Section WithBinding.
    Context {B : Set}.

    Global Instance eq_dec_ctx (eqB : EqDec B) : EqDec (Ctx B) :=
      fix eq_dec_ctx (Γ Δ : Ctx B) {struct Γ} : dec_eq Γ Δ :=
        match Γ , Δ with
        | nil      , nil      => left eq_refl
        | snoc Γ b , snoc Δ c => f_equal2_dec snoc noConfusion_inv
                                   (eq_dec_ctx Γ Δ) (eq_dec b c)
        | _        , _        => right noConfusion_inv
        end.

    Fixpoint lookup (Γ : Ctx B) (n : nat) : option B :=
      match Γ , n with
      | snoc _ b , O   => Some b
      | snoc Γ _ , S n => lookup Γ n
      | _        , _   => None
      end.

    (* Concatenation of two contexts. *)
    Fixpoint cat (Γ1 Γ2 : Ctx B) {struct Γ2} : Ctx B :=
      match Γ2 with
      | nil       => Γ1
      | snoc Γ2 τ => snoc (cat Γ1 Γ2) τ
      end.

    (* This is a predicate that that encodes that the de Bruijn index n points
       to the binding b in Γ. *)
    Fixpoint nth_is (Γ : Ctx B) (n : nat) (b : B) {struct Γ} : Prop :=
      match Γ , n with
      | snoc _ x , O   => x = b
      | snoc Γ _ , S n => nth_is Γ n b
      | _        , _   => False
      end.

    Lemma nth_is_right_exact {Γ : Ctx B} (n : nat) (b1 b2 : B) :
      nth_is Γ n b1 -> nth_is Γ n b2 -> b1 = b2.
    Proof.
      revert n.
      induction Γ.
      - intros ? [].
      - cbn in *.
        destruct n. intros e1 e2.
        refine (eq_trans _ e2).
        apply eq_sym. auto.
        apply IHΓ.
    Qed.

    Section WithUIP.

      Context {UIP_B : UIP B}.

      Fixpoint proof_irrelevance_nth_is {Γ} (n : nat) (b : B) {struct Γ} :
        forall (p q : nth_is Γ n b), p = q :=
        match Γ with
        | nil       => fun p q => match q with end
        | snoc Γ b' => match n with
                       | 0   => uip
                       | S n => proof_irrelevance_nth_is n b
                       end
        end.

      Global Instance eqdec_ctx_nth {Γ n b} : EqDec (nth_is Γ n b).
      Proof. intros p q. left. apply proof_irrelevance_nth_is. Defined.

      Lemma proof_irrelevance_nth_is_refl {Γ} (n : nat) (b : B) (p : nth_is Γ n b) :
        proof_irrelevance_nth_is n b p p = eq_refl.
      Proof. apply uip. Qed.

    End WithUIP.

    Section In.
       (* In represents context containment proofs. This is essentially a
          well-typed de Bruijn index, i.e. a de Bruijn index with a proof that it
          resolves to the binding b.  *)
      Inductive In (b : B) : Ctx B -> Set :=
      | in_zero {Γ : Ctx B} : In b (snoc Γ b)
      | in_succ {Γ : Ctx B} {b' : B} (bIn : In b Γ) : In b (snoc Γ b').
      Existing Class In.
      Global Arguments in_zero {b Γ}.
      Derive Signature NoConfusion for In.

    End In.

    (* (* Two proofs of context containment are equal of the deBruijn indices are equal *) *)
    (* Definition In_eqb {Γ} {b1 b2 : B} (b1inΓ : In b1 Γ) (b2inΓ : In b2 Γ) : bool := *)
    (*   Nat.eqb (in_at b1inΓ) (in_at b2inΓ). *)

    (* Lemma In_eqb_spec `{UIP B} {Γ} {b1 b2 : B} (b1inΓ : In b1 Γ) (b2inΓ : In b2 Γ) : *)
    (*   reflect *)
    (*     (existT _ _ b1inΓ = existT _ _ b2inΓ :> sigT (fun b => In b Γ)) *)
    (*     (In_eqb b1inΓ b2inΓ). *)
    (* Proof. *)
    (*   destruct b1inΓ as [m p], b2inΓ as [n q]; cbn. *)
    (*   destruct (Nat.eqb_spec m n); constructor. *)
    (*   - subst. pose proof (nth_is_right_exact _ _ _ p q). subst. *)
    (*     f_equal. f_equal. apply proof_irrelevance_nth_is. *)
    (*   - intros e. depelim e. destruct n, m; cbn in H0; congruence. *)
    (* Qed. *)

    Inductive NilView {b : B} (i : In b nil) : Set :=.

    Equations nilView {b : B} (i : In b nil) : NilView i :=.

    Inductive SnocView (Γ : Ctx B) {b' : B} : forall b, In b (snoc Γ b') -> Set :=
    | snocViewZero                  : SnocView in_zero
    | snocViewSucc {b} (i : In b Γ) : SnocView (in_succ i).
    Global Arguments snocViewZero {_ _}.

    Equations snocView {Γ} {b b' : B} (i : In b (snoc Γ b')) :
      @SnocView Γ b' b i :=
    | in_zero   => snocViewZero
    | in_succ i => snocViewSucc i.

    Fixpoint in_cat_left {b : B} {Γ : Ctx B} (Δ : Ctx B) (bIn : In b Γ) : In b (cat Γ Δ) :=
      match Δ with
      | nil      => bIn
      | snoc Δ _ => in_succ (in_cat_left Δ bIn)
      end.

    Fixpoint in_cat_right {b : B} {Γ : Ctx B} (Δ : Ctx B) (bIn : In b Δ) : In b (cat Γ Δ) :=
      match bIn with
      | in_zero   => in_zero
      | in_succ i => in_succ (in_cat_right i)
      end.

    Inductive CatView {Γ Δ} {b : B} : In b (cat Γ Δ) -> Set :=
    | isCatLeft  (bIn : In b Γ) : CatView (in_cat_left Δ bIn)
    | isCatRight (bIn : In b Δ) : CatView (in_cat_right bIn).

    Definition catView_nil {Γ b} (bIn : In b Γ) : @CatView Γ nil b bIn :=
      @isCatLeft Γ nil b bIn.

    Definition catView_zero {Γ Δ b} : @CatView Γ (snoc Δ b) b in_zero :=
      @isCatRight Γ (snoc Δ b) b in_zero.

    Definition catView_succ {Γ Δ b b'} (bIn : In b (cat Γ Δ)) (bInV : CatView bIn) :
      @CatView Γ (snoc Δ b') b (in_succ bIn) :=
      match bInV with
      | isCatLeft bIn => @isCatLeft Γ (@snoc B Δ b') b bIn
      | isCatRight bIn => @isCatRight Γ (@snoc B Δ b') b (@in_succ b Δ b' bIn)
      end.

    Equations catView {Γ} Δ {b : B} (bIn : In b (cat Γ Δ)) : CatView bIn :=
    | nil      | bIn       => catView_nil bIn
    | snoc Δ _ | in_zero   => catView_zero
    | snoc Δ _ | in_succ i => catView_succ (catView Δ i).

    Section All.

      Inductive All (P : B -> Type) : Ctx B -> Type :=
      | all_nil : All P nil
      | all_snoc {Γ b} : @All P Γ -> P b -> All P (snoc Γ b).

      Definition all_intro {P} (HP : forall b, P b) : forall Γ, All P Γ :=
        fix all_intro Γ :=
          match Γ with
          | nil      => all_nil P
          | snoc Γ b => all_snoc (all_intro Γ) (HP b)
          end.

    End All.

  End WithBinding.

  Section WithAB.
    Context {A B : Set} (f : A -> B).

    Fixpoint map (Γ : Ctx A) : Ctx B :=
      match Γ with
      | nil      => nil
      | snoc Γ a => snoc (map Γ) (f a)
      end.

  End WithAB.

  Module notations.

    Open Scope ctx_scope.

    Notation "x :: τ" := (MkB x τ) (only parsing) : ctx_scope.
    Notation "N ∷ T" := (Binding N T) : type_scope.
    Notation "x ∷ t" := (MkB x t) : ctx_scope.

    Notation "'ε'" := nil (only parsing) : ctx_scope.
    Infix "▻" := snoc : ctx_scope.
    Notation "Γ1 ▻▻ Γ2" := (cat Γ1%ctx Γ2%ctx) : ctx_scope.
    Notation "b ∈ Γ" := (In b%ctx Γ%ctx) : type_scope.

    (* Use the same notations as in ListNotations. *)
    Notation "[ ]" := (nil) : ctx_scope.
    Notation "[ x ]" := (snoc nil x) : ctx_scope.
    Notation "[ x ; y ; .. ; z ]" :=
      (snoc .. (snoc (snoc nil x) y) .. z) : ctx_scope.

  End notations.
  Import notations.

  Local Notation NCtx N T := (Ctx (Binding N T)).

  Section Resolution.

    Context {Name : Set} {Name_eqdec : EqDec Name} {D : Set}.

    Fixpoint resolve (Γ : NCtx Name D) (x : Name) {struct Γ} : option D :=
      match Γ with
      | []      => None
      | Γ ▻ y∷d => if Name_eqdec x y then Some d else resolve Γ x
      end.

    Fixpoint resolve_mk_in (Γ : NCtx Name D) (x : Name) {struct Γ} :
      let m := resolve Γ x in forall (p : IsSome m), x∷fromSome m p ∈ Γ :=
      match Γ with
      | [] => fun p => match p with end
      | Γ ▻ y∷d =>
        match Name_eqdec x y as s return
          (forall p, (x∷fromSome (if s then Some d else resolve Γ x) p) ∈ Γ ▻ y∷d)
        with
        | left e => fun _ => match e with eq_refl => in_zero end
        | right _ => fun p => in_succ (resolve_mk_in Γ x p)
        end
      end.

    Fixpoint names (Γ : NCtx Name D) : list Name :=
      match Γ with
      | []      => List.nil
      | Γ ▻ y∷_ => cons y (names Γ)
      end.

  End Resolution.

  Module resolution.

    (* Hook the reflective procedure for name resolution into the typeclass
       resolution mechanism. *)
    #[export]
    Hint Extern 10 (?x∷_ ∈ ?Γ) =>
      let xInΓ := eval compute in (resolve_mk_in Γ x tt) in
        exact xInΓ : typeclass_instances.

  End resolution.

  Section FreshName.

    Open Scope string_scope.

    Fixpoint split_at_dot' {R} (x : string) (k : string -> string -> R) {struct x} : R :=
      match x with
      | ""           => k "" ""
      | String "." x => k "" x
      | String a x   => split_at_dot' x (fun pre => k (String a pre))
      end.

    Definition split_at_dot (x : string) : (string * string) :=
      split_at_dot' x pair.

    Definition parse_number (x : string) : N :=
      match NilEmpty.uint_of_string x with
      | Some n => N.of_uint n
      | None   => 0%N
      end.

    Definition unparse_number (x : N) : string :=
      NilEmpty.string_of_uint (N.to_uint x).

    Definition max_with_base (base : string) (xs : list string) : N :=
      List.fold_left
        (fun o x =>
           match split_at_dot x with
             (pre,suf) => if pre =? base
                          then N.max o (parse_number suf)
                          else o
           end)
        xs 0%N.

    Definition fresh [T : Set] (xs : NCtx string T) (x : option string) : string :=
      let xs := names xs in
      let x := match x with Some x => x | None => "x" end in
      if List.find (String.eqb x) xs
      then let base := fst (split_at_dot x) in
           let n    := N.succ (max_with_base base xs) in
           String.append base (String "."%char (unparse_number n))
      else x.

  End FreshName.

End ctx.
Export ctx (Ctx).
Notation NCtx N T := (Ctx (Binding N T)).
Bind Scope ctx_scope with Ctx.
Bind Scope ctx_scope with NCtx.

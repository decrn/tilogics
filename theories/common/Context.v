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
From Em Require Import
     Prelude.

Local Set Implicit Arguments.
Local Unset Equations Derive Equations.

Declare Scope ctx_scope.
Delimit Scope ctx_scope with ctx.

Module Import ctx.

  (* Type of contexts. This is a list of bindings of type B. This type and
     subsequent types use the common notation of snoc lists. *)
  #[universes(template)]
  Inductive Ctx (B : Type) : Type :=
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

    #[export] Instance eq_dec_ctx (eqB : EqDec B) : EqDec (Ctx B) :=
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

    Definition proof_irrelevance_het_nth_is {b1 b2 : B} :
      forall {Γ n} (p1 : nth_is Γ n b1) (p2 : nth_is Γ n b2),
        existT _ p1 = existT _ p2 :=
       fix pi Γ n {struct Γ} :=
         match Γ with
         | nil => fun p q => match q with end
         | snoc Γ b =>
           match n with
           | O   => fun p q => match p , q with
                                 eq_refl , eq_refl => eq_refl
                               end
           | S n => pi Γ n
           end
         end.

    Definition nth_is_right_exact {Γ : Ctx B} (n : nat) (b1 b2 : B)
      (p1 : nth_is Γ n b1) (p2 : nth_is Γ n b2) : b1 = b2 :=
      f_equal (@projT1 _ _) (proof_irrelevance_het_nth_is p1 p2).

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

      #[export] Instance eqdec_ctx_nth {Γ n b} : EqDec (nth_is Γ n b) :=
        fun p q => left (proof_irrelevance_nth_is n b p q).

      Definition proof_irrelevance_nth_is_refl {Γ} (n : nat) (b : B) (p : nth_is Γ n b) :
        proof_irrelevance_nth_is n b p p = eq_refl := uip _ _.

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

      Set Transparent Obligations.
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

    (* We define several views on [In] which allows us to define mechanisms for
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
    Variant NilView [b : B] (i : In b nil) : Type :=.

    (* A view for membership in a non-empty context. *)
    Variant SnocView {b' : B} (Γ : Ctx B) :
      forall b, In b (snoc Γ b') -> Type :=
    | isZero                  : SnocView in_zero
    | isSucc {b} (i : In b Γ) : SnocView (in_succ i).
    #[global] Arguments SnocView {_ _} [b] _.
    #[global] Arguments isZero {_ _}.

    (* Instead of defining separate view functions, that construct a value
       of the *View datatypes, we use a single definition. This way, we
       avoid definition dummy definitions the other cases like it is usually
       done in small inversions. We simply define inversions for all cases at
       once. *)
    Definition view {b Γ} (bIn : In b Γ) :
      match Γ return forall b, In b Γ -> Type with
      | nil      => NilView
      | snoc _ _ => SnocView
      end b bIn :=
      match bIn with
      | in_zero   => isZero
      | in_succ i => isSucc i
      end.

    (* Left and right membership proofs for context concatenation. *)
    Fixpoint in_cat_left {b Γ} Δ (bIn : In b Γ) : In b (cat Γ Δ) :=
      match Δ with
      | nil      => bIn
      | snoc Δ _ => in_succ (in_cat_left Δ bIn)
      end.

    Fixpoint in_cat_right {b Γ} Δ (bIn : In b Δ) : In b (cat Γ Δ) :=
      match bIn with
      | in_zero   => in_zero
      | in_succ i => in_succ (in_cat_right i)
      end.

    (* A view for case splitting on a proof of membership in a concatenation.
       By pattern matching on this view we get the membership in the left
       respectively right side of the concatenation and refine the original
       membership proof. *)
    Inductive CatView {Γ Δ} [b : B] : In b (cat Γ Δ) -> Type :=
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

    Fixpoint remove (Γ : Ctx B) {b : B} (xIn : In b Γ) : Ctx B :=
      match xIn with
      | @in_zero _ Γ => Γ
      | @in_succ _ _ b' bIn => snoc (remove bIn) b'
      end.
    Arguments remove _ [_] _.

    Equations in_thin {b x} {Σ : Ctx B} (bIn : In b Σ) (xIn : In x (remove Σ bIn)) : In x Σ :=
    | in_zero     , xIn         => in_succ xIn
    | in_succ bIn , in_zero     => in_zero
    | in_succ bIn , in_succ xIn => in_succ (in_thin bIn xIn).

    Inductive OccursCheckView {Σ} {x : B} (xIn : In x Σ) : forall y, In y Σ -> Set :=
    | Same                                 : OccursCheckView xIn xIn
    | Diff {y} (yIn : In y (remove Σ xIn)) : OccursCheckView xIn (in_thin xIn yIn).

    Equations occurs_check_view {Σ} {x y: B} (xIn : In x Σ) (yIn : In y Σ) : OccursCheckView xIn yIn :=
    | in_zero     , in_zero     => Same in_zero
    | in_zero     , in_succ yIn => Diff in_zero yIn
    | in_succ xIn , in_zero     => Diff (in_succ xIn) in_zero
    | in_succ xIn , in_succ yIn => match occurs_check_view xIn yIn with
                                   | Same _     => Same (in_succ xIn)
                                   | Diff _ yIn => Diff (in_succ xIn) (in_succ yIn)
                                   end.

    Lemma occurs_check_view_refl {Σ x} (xIn : In x Σ) :
      occurs_check_view xIn xIn = Same xIn.
    Proof. induction xIn; cbn; now rewrite ?IHxIn. Qed.

    Lemma occurs_check_view_thin {Σ x y} (xIn : In x Σ) (yIn : In y (remove Σ xIn)) :
      occurs_check_view xIn (in_thin xIn yIn) = Diff xIn yIn.
    Proof. induction xIn; [|depelim yIn]; cbn; now rewrite ?IHxIn. Qed.

    Fixpoint length (Γ : Ctx B) : nat :=
      match Γ with
      | nil => 0
      | snoc Γ _ => S (length Γ)
      end.

    Lemma length_remove {x} (Γ : Ctx B) :
      forall (xIn : In x Γ),
        S (length (remove Γ xIn)) = length Γ.
    Proof.
      induction xIn using In_ind.
      - reflexivity.
      - cbn - [remove].
        f_equal. apply IHxIn.
    Qed.

    Import SigTNotations.

    Notation Ref Γ := (sigT (fun x => In x Γ)).

    Definition ref_zero {Γ x} : Ref (snoc Γ x) :=
      (@existT B (fun x0 : B => In x0 (@snoc B Γ x)) x (@in_zero x Γ)).
    Definition ref_succ {Γ x} : Ref Γ -> Ref (snoc Γ x).
    Proof.
      intros [y yIn]. exists y. now constructor.
    Defined.

    Definition ref_zero_neq_succ {Γ x} (r : Ref Γ) :
      ref_zero <> @ref_succ Γ x r :=
      match r with
      | (y;yIn) =>
         eq_rect
           ref_zero
           (fun r =>
              match r with
              | (z;in_zero) => True
              | (z;in_succ _) => False
              end)
           I
           (ref_succ (y; yIn))
      end.

    Set Equations With UIP.

    Lemma rec_succ_inj {eqB : EqDec B} {Γ z} (r1 r2 : Ref Γ) :
      @ref_succ Γ z r1 = @ref_succ Γ z r2 -> r1 = r2.
    Proof.
      destruct r1 as [x xIn], r2 as [y yIn]; cbn. intros e.
      now dependent elimination e.
    Qed.

    #[export] Instance In_eqdec {eqB : EqDec B} : forall Γ, EqDec (Ref Γ) :=
      fix eqdec Γ' :=
        match Γ' with
        | nil       => fun x => match view (projT2 x) with end
        | snoc Γ b => fun '(x;xIn) '(y;yIn) =>
            match view xIn , view yIn with
            | isZero     , isZero     => left eq_refl
            | isZero     , isSucc yIn => right (ref_zero_neq_succ (_; yIn))
            | isSucc xIn , isZero     => right (not_eq_sym (ref_zero_neq_succ (_; xIn)))
            | isSucc xIn , isSucc yIn =>
                match eqdec Γ (_; xIn) (_; yIn) with
                | left e => left (f_equal ref_succ e)
                | right n => right (fun e => (n (rec_succ_inj (_; xIn) (_; yIn) e)))
                end
            end
        end.

    (* In this section we define a generic Bove-Capretta style accessibility
       predicate for functions that recurse on smaller contexts by removing an
       element.

       See: BOVE, ANA, and VENANZIO CAPRETTA. “Modelling General Recursion in
       Type Theory.” Mathematical Structures in Computer Science, vol. 15,
       no. 4, 2005, pp. 671–708., doi:10.1017/S0960129505004822. *)
    Section RemoveAcc.

      (* Coq only generates non-dependent elimination schemes for inductive
         families in Prop. Hence, we disable the automatic generation and
         define the elimination schemes for the predicate ourselves. *)
      #[local] Unset Elimination Schemes.

      Inductive remove_acc (Γ : Ctx B) : Prop :=
        remove_acc_intro :
          (forall x (xIn : In x Γ), remove_acc (remove Γ xIn)) -> remove_acc Γ.

      Definition remove_acc_inv {Γ} (d : remove_acc Γ) :
        forall x (xIn : In x Γ), remove_acc (remove Γ xIn) := let (f) := d in f.

      Definition remove_acc_rect (P : forall Γ, remove_acc Γ -> Type)
        (f : forall Γ (d : forall x (xIn : In x Γ), remove_acc (remove Γ xIn)),
            (forall x (xIn : In x Γ),
                P (remove Γ xIn) (d x xIn)) -> P Γ (remove_acc_intro d)) :=
        fix F Γ (d : remove_acc Γ) {struct d} : P Γ d :=
          let (g) return _ := d in
          f Γ g (fun x xIn => F (remove Γ xIn) (g x xIn)).

      Definition remove_acc_ind (P : forall Γ, remove_acc Γ -> Prop)
        (f : forall Γ (d : forall x (xIn : In x Γ), remove_acc (remove Γ xIn)),
            (forall x (xIn : In x Γ),
                P (remove Γ xIn) (d x xIn)) -> P Γ (remove_acc_intro d)) :=
        fix F Γ (d : remove_acc Γ) {struct d} : P Γ d :=
          let (g) return _ := d in
          f Γ g (fun x xIn => F (remove Γ xIn) (g x xIn)).

      Fixpoint remove_acc_step {Γ x} (d : remove_acc Γ) {struct d} :
        remove_acc (snoc Γ x) :=
        remove_acc_intro
          (fun β (βIn : In β (snoc Γ x)) =>
             match view βIn in SnocView βIn
                   return remove_acc (remove _ βIn) with
             | isZero   => d
             | isSucc i => remove_acc_step (remove_acc_inv d i)
             end).

      Fixpoint remove_acc_all (Γ : Ctx B) : remove_acc Γ :=
        match Γ with
        | nil      => remove_acc_intro
                        (fun x (xIn : In x nil) =>
                           match view xIn with end)
        | snoc Γ b => remove_acc_step (remove_acc_all Γ)
        end.

      (* Calculating the full predicate is costly. It has quadratic running
         time in the size of the context. It's better to keep this opaque and
         not unfold it. To prevent computation from being blocked, clients of
         this code should never pattern match on a witness of the predicate
         directly and instead use [remove_acc_inv] in the recursive call. The
         standard library uses the same style and for examples defines [Fix_F]
         for well-founded induction using [Acc_inv] for recursive calls. *)
      #[global] Opaque remove_acc_all.

    End RemoveAcc.

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

    Notation "'ε'" := nil (only parsing) : ctx_scope.
    Infix "▻" := snoc : ctx_scope.
    Notation "Γ1 ▻▻ Γ2" := (cat Γ1%ctx Γ2%ctx) : ctx_scope.
    Notation "b ∈ Γ" := (In b%ctx Γ%ctx) : type_scope.

    (* Use the same notations as in ListNotations. *)
    Notation "[ ]" := (nil) : ctx_scope.
    Notation "[ctx]" := (nil) : ctx_scope.
    Notation "[ x ]" := (snoc nil x) : ctx_scope.
    Notation "[ x ; y ; .. ; z ]" :=
      (snoc .. (snoc (snoc nil x) y) .. z) : ctx_scope.
    Notation "Γ - x" := (@remove _ Γ x _) : ctx_scope.

  End notations.
  Import notations.

End ctx.
Export ctx (Ctx).
Export (hints) ctx.
Bind Scope ctx_scope with Ctx.

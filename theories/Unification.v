(******************************************************************************)
(* Copyright (c) 2022 Steven Keuchel                                          *)
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
     Arith.PeanoNat
     Classes.CRelationClasses
     Program.Tactics.
From Equations Require Import
     Equations.
From Equations.Type Require
     Classes
     WellFounded.
From Equations.Prop Require
     Classes.
From MasterThesis Require Import
     Context Environment Prelude.
Import ctx.
Import ctx.notations.
Import SigTNotations.

Set Implicit Arguments.

Definition TYPE : Type := Ctx nat -> Type.
Definition Valid (A : TYPE) : Type :=
  forall Σ, A Σ.
Definition Impl (A B : TYPE) : TYPE :=
  fun Σ => A Σ -> B Σ.
Definition Forall {I : Type} (A : I -> TYPE) : TYPE :=
  fun w => forall i : I, A i w.

Definition Unit : TYPE := fun _ => unit.
Definition Option (A : TYPE) : TYPE := fun Σ => option (A Σ).
Definition Prod (A B : TYPE) : TYPE := fun Σ => prod (A Σ) (B Σ).
Definition Sum (A B : TYPE) : TYPE := fun Σ => sum (A Σ) (B Σ).

Inductive Ty (Σ : Ctx nat) : Type :=
  | t_evar (x : nat) (xIn : x ∈ Σ)
  | t_bool
  | t_func (T1 T2 : Ty Σ).
Arguments t_evar {Σ x} xIn.
Arguments t_bool {Σ}.
Arguments t_func {Σ}.

Derive NoConfusion for Ty.

Module Tri.

  Inductive Tri (Σ : Ctx nat) : Ctx nat -> Set :=
  | refl      : Tri Σ Σ
  | cons {Σ' x} (xIn : x ∈ Σ) (t : Ty (Σ - x)%ctx) (ζ : Tri (Σ - x) Σ') : Tri Σ Σ'.
  Global Arguments refl {_}.
  Global Arguments cons {_ _} x {_} t ζ.

  Fixpoint trans [Σ0 Σ1 Σ2] (ζ : Tri Σ0 Σ1) {struct ζ} : Tri Σ1 Σ2 -> Tri Σ0 Σ2 :=
     match ζ with
     | refl       => fun ξ => ξ
     | cons x t ν => fun ξ => cons x t (trans ν ξ)
     end.

  #[export] Instance preorder_tri : CRelationClasses.PreOrder Tri :=
    {| PreOrder_Reflexive Σ := refl;
       PreOrder_Transitive  := trans
    |}.

End Tri.
Notation "Σ1 ⊒ Σ2" := (Tri.Tri Σ1 Σ2) (at level 80).

Definition Box (A : TYPE) : TYPE :=
  fun w0 => forall w1, w0 ⊒ w1 -> A w1.

Unset Printing Notations.
Definition Diamond (A : TYPE) : TYPE :=
  fun w0 => {w1 : Ctx nat & ((w0 ⊒ w1) * A w1)}%type.

Print Diamond.

Definition DiamondT (M : TYPE -> TYPE) : TYPE -> TYPE :=
  fun A => M (fun w0 => {w1 : Ctx nat & ((w0 ⊒ w1) * A w1)}%type).

Definition Later (A : TYPE) : TYPE :=
  fun Γ => forall x (xIn : x ∈ Γ), A (Γ - x).
Definition LaterTm (A : TYPE) : TYPE :=
  fun Γ => forall x (xIn : x ∈ Γ), Ty (Γ - x) -> A (Γ - x).
Definition Sooner (A : TYPE) : TYPE :=
  fun Γ => sigT (fun x => sigT (fun (xIn : x ∈ Γ) => A (Γ - x))).
Definition SoonerTm (A : TYPE) : TYPE :=
  fun Γ => sigT (fun x => sigT (fun (xIn : x ∈ Γ) => Ty (Γ - x) * A (Γ - x)))%type.


Notation "◅ A" := (Sooner A) (at level 9, right associativity).
Notation "◄ A" := (SoonerTm A) (at level 9, right associativity).

Notation "□ A" := (Box A) (at level 9, format "□ A", right associativity).
Notation "◇ A" := (DiamondT id A) (at level 9, format "◇ A", right associativity).
Notation "? A" := (Option A) (at level 9, format "? A", right associativity).
Notation "◆ A" := (DiamondT Option A) (at level 9, format "◆ A", right associativity).
Notation "A * B" := (Prod A B).

Notation "⊢ A" := (Valid A) (at level 100).
Notation "A -> B" := (Impl A B).
Notation "'∀' x .. y , P " :=
  (Forall (fun x => .. (Forall (fun y => P)) ..))
    (at level 99, x binder, y binder, right associativity).
Notation "▻ A" := (Later A) (at level 9, right associativity).
Notation "► A" := (LaterTm A) (at level 9, right associativity).

Section Löb.

  Context (P : TYPE) (step : ⊢ ▻P -> P).

  Obligation Tactic := auto using Nat.eq_le_incl, length_remove.
  Equations(noeqns) Löb {Σ : Ctx nat} : P Σ by wf (length Σ) :=
  Löb := step (fun _ _ => Löb).

End Löb.
Arguments Löb P step Σ : clear implicits.

Definition K {A B} :
  ⊢ □(A -> B) -> (□A -> □B) :=
  fun w0 f a w1 ω01 =>
    f w1 ω01 (a w1 ω01).
Definition T {A} :
  ⊢ □A -> A :=
  fun w0 a => a w0 Tri.refl.
Definition four {A} :
  ⊢ □A -> □□A :=
  fun w0 a w1 ω01 w2 ω12 =>
    a w2 (Tri.trans ω01 ω12).
Global Arguments four : simpl never.
Definition D {A} : ⊢ □A -> ◇A :=
  fun Σ a => existT _ Σ (Tri.refl, T a).

Definition box2later {A} : ⊢ □A -> ►A.
  intros Σ a x xIn t. apply a. econstructor.
  apply t. constructor.
Defined.

Definition sooner2diamond {A} : ⊢ ◄A -> ◇A.
  intros Σ a. destruct a as [σ [σIn [t a]]].
  econstructor. split; try eassumption.
  econstructor 2. auto. constructor 1.
Defined.

Definition sooner2diamondtm {A} : ⊢ ◄A -> ◆A.
  intros Σ a. destruct a as [σ [σIn [t a]]].
  constructor.
  econstructor. split; try eassumption.
  econstructor 2. auto. constructor 1.
Defined.

Definition η {A} : ⊢ A -> ◆A :=
  fun Σ a => Some (existT _ Σ (Tri.refl, a)).
Arguments η {A Σ} a.

Definition η1 {A} {Σ x} {xIn : x ∈ Σ} (t : Ty (Σ - x)) (a : A (Σ - x)) : ◆A Σ :=
  sooner2diamondtm (existT _ x (existT _ xIn (t, a))).

Section Thick.

  Definition thick : ⊢ Ty -> ►Ty :=
    fun Σ =>
      fix thick (S : Ty Σ) (x : nat) (xIn : x ∈ Σ) (T : Ty (Σ - x)) {struct S} : Ty (Σ - x) :=
      match S with
      | t_evar σIn   => match occurs_check_view xIn σIn with
                        | Same _     => T
                        | Diff _ yIn => t_evar yIn
                        end
      | t_bool       => t_bool
      | t_func S1 S2 => t_func (thick S1 x xIn T) (thick S2 x xIn T)
      end.

End Thick.

Arguments thick {_} s x {_} u.
Notation "s [ x ↦ u ]" := (thick s x u)
  (at level 8, left associativity,
   format "s [ x ↦ u ]").

Section Thin.

  Fixpoint thin {Σ x} (xIn : x ∈ Σ) (T : Ty (Σ - x)) : Ty Σ :=
    match T with
    | t_evar yIn => t_evar (in_thin xIn yIn)
    | t_bool => t_bool
    | t_func T1 T2 => t_func (thin xIn T1) (thin xIn T2)
    end.

  Definition fancy_thin : ⊢ ◅Ty -> Ty :=
    fun Σ '(x; (xIn; T)) => thin xIn T.

End Thin.

Lemma thin_thick {Σ y} (yIn : y ∈ Σ) (s t : Ty (Σ - y)) :
  (thin yIn t)[y↦s] = t.
Proof.
  induction t; cbn; f_equal; auto.
  now rewrite occurs_check_view_thin.
Qed.

Section OccursCheck.
  Import option.notations.

  Definition occurs_check_in : ⊢ ∀ x, In x -> ▻(Option (In x)) :=
    fun w x xIn y yIn =>
      match occurs_check_view yIn xIn with
      | Same _      => None
      | Diff _ xIn' => Some xIn'
      end.

  Definition occurs_check : ⊢ Ty -> ▻(Option Ty) :=
    fun w =>
      fix oc (t : Ty w) (y : nat) (yIn : y ∈ w) {struct t} :=
      match t with
      | t_evar xIn   => Some t_evar <*> occurs_check_in xIn yIn
      | t_bool       => Some t_bool
      | t_func T1 T2 => Some t_func <*> oc T1 y yIn <*> oc T2 y yIn
      end.

  Lemma occurs_check_thin {Σ x} (xIn : x ∈ Σ) (t : Ty (Σ - x)) :
    option.wp (eq t) (occurs_check (thin xIn t) xIn).
  Proof.
    induction t; cbn.
    - rewrite option.wp_map. unfold occurs_check_in.
      rewrite occurs_check_view_thin. now constructor.
    - now constructor.
    - repeat rewrite ?option.wp_aplazy, ?option.wp_map.
      repeat option.tactics.mixin. congruence.
  Qed.

  Lemma occurs_check_sound {Σ} (t : Ty Σ) {x} (xIn : x ∈ Σ) :
    option.wlp (fun t' => t = thin xIn t') (occurs_check t xIn).
  Proof.
    induction t; cbn.
    - unfold occurs_check_in.
      now destruct occurs_check_view; constructor.
    - now constructor.
    - repeat rewrite ?option.wlp_aplazy, ?option.wlp_map.
      repeat option.tactics.mixin. cbn. congruence.
  Qed.

End OccursCheck.

Definition box_intro_split {A} :
  ⊢ A -> ►□A -> □A :=
  fun Σ0 a la Σ1 ζ =>
    match ζ with
    | Tri.refl => a
    | Tri.cons x t ζ' => la x _ t _ ζ'
    end.

Definition SUBST : TYPE := Ty -> □Ty.
Section Subst.

  Context [Σ] (lsubst : ▻(Ty -> □Ty) Σ).

  Definition subst_in {x} (xIn : In x Σ) : □Ty Σ :=
    box_intro_split
      (t_evar xIn)
      (fun y yIn s =>
         match occurs_check_view yIn xIn with
         | Same _     => lsubst yIn s
         | Diff _ xIn => lsubst yIn (t_evar xIn)
         end).

  Definition subst : Ty Σ -> □Ty Σ :=
    fix subst (t : Ty Σ) : □Ty Σ :=
      match t with
      | t_evar xIn   => subst_in xIn
      | t_bool       => fun _ _ => t_bool
      | t_func T1 T2 => fun _ ζ => t_func (subst T1 _ ζ) (subst T2 _ ζ)
      end.

End Subst.

Definition realsubst_fast : ⊢ Ty -> □Ty :=
  Löb SUBST subst.

Definition realsubst_slow : ⊢ Ty -> □Ty.
  refine (fix subst {Σ} (t : Ty Σ) {Σ1} ζ1 {struct ζ1} := _).
  destruct ζ1.
  - apply t.
  - refine (subst _ _ _ ζ1).
    apply (thick t).
    apply t0.
Defined.

Definition Hom (A B : TYPE) := ⊢ A -> B.

Definition fmap {A B} (f : Hom A B) : Hom ◆A ◆B.
Proof.
  intros Σ0 [[Σ1 [ζ1 a1]]|].
  - constructor 1. exists Σ1. split. auto. apply f. auto.
  - constructor 2.
Defined.
(* Notation "f <$> a" := (fmap f a) (at level 20). *)

Section Mult.
  Import option.notations.

  Definition μ {A} : Hom ◆◆A ◆A :=
    fun Σ0 a0 =>
      '(Σ1; (ζ1 , a1)) <- a0;;
      '(Σ2; (ζ2 , a2)) <- a1;;
      Some (Σ2; (Tri.trans ζ1 ζ2, a2)).

  Definition ebind {A B} : Hom A ◆B -> Hom ◆A ◆B :=
    fun f Σ0 a0 =>
      '(Σ1; (ζ1, a1)) <- a0 ;;
      '(Σ2; (ζ2, b2)) <- f Σ1 a1 ;;
      Some (Σ2; (Tri.trans ζ1 ζ2, b2)).

  Definition bind {A B} : ⊢ ◆A -> □(A -> ◆B) -> ◆B :=
    fun Σ a0 f =>
      '(Σ1; (ζ1 , a1)) <- a0 ;;
      '(Σ2; (ζ2 , b2)) <- f Σ1 ζ1 a1 ;;
      Some (Σ2; (Tri.trans ζ1 ζ2, b2)).

End Mult.

Notation "⟨ ζ ⟩ x <- ma ;; mb" :=
  (bind ma (fun _ ζ x => mb))
    (at level 80, x at next level,
      ma at next level, mb at level 200,
      right associativity).

(* see Kobayashi, S. (1997). Monad as modality. *)
Definition strength {A B} : Hom (□A * ◆B) (◆(□A * B)) :=
  fun Σ0 '(a0,b0) => bind b0 (fun Σ1 ζ1 b1 => η (four a0 ζ1, b1)).

Definition Assignment : TYPE :=
  @Env nat (fun _ => Ty ctx.nil).
Definition Lift (A : Type) : TYPE :=
  fun Σ => (Assignment Σ -> A)%type.
Definition Const (A : Type) : TYPE :=
  fun _ => A.
Definition PROP : TYPE :=
  fun _ => Prop.

Definition Property : TYPE :=
  □PROP.

Definition Unifies : ⊢ Ty -> Ty -> Property.
  intros Σ s t Σ1 ζ1.
  apply (realsubst_slow s ζ1 = realsubst_slow t ζ1).
Defined.

Notation "ζ ⊨ s ~ t" := (Unifies s t ζ) (at level 90, s at level 69).

Definition wp {A} : ⊢ ◆A -> □(A -> PROP) -> PROP :=
  fun Σ0 a0 POST => option.wp (fun '(Σ1; (ζ1 , a1)) => POST Σ1 ζ1 a1) a0.

Definition wlp {A} : ⊢ ◆A -> □(A -> PROP) -> PROP :=
  fun Σ0 a0 POST => option.wlp (fun '(Σ1; (ζ1 , a1)) => POST Σ1 ζ1 a1) a0.

Lemma wp_η {A Σ} (a : A Σ) (POST : □(A -> PROP) Σ) :
  wp (η a) POST <-> T POST a.
Proof. unfold wp, η. now option.tactics.mixin. Qed.

Lemma wp_μ {A B Σ} (a : ◆A Σ) (f : □(A -> ◆B) Σ) (POST : □(B -> PROP) Σ) :
  wp (bind a f) POST <-> wp a (fun _ ζ1 a1 => wp (f _ ζ1 a1) (four POST ζ1)).
Proof.
  unfold wp, bind.
  now repeat
    (rewrite ?option.wp_bind;
     repeat option.tactics.mixin;
     intros; try destruct_conjs).
Qed.

Lemma wlp_η {A Σ} (a : A Σ) (POST : □(A -> PROP) Σ) :
  wlp (η a) POST <-> T POST a.
Proof. unfold wlp, η. now option.tactics.mixin. Qed.

Lemma wlp_μ {A B Σ} (a : ◆A Σ) (f : □(A -> ◆B) Σ) (POST : □(B -> PROP) Σ) :
  wlp (bind a f) POST <-> wlp a (fun _ ζ1 a1 => wlp (f _ ζ1 a1) (four POST ζ1)).
Proof.
  unfold wlp, bind.
  now repeat
    (rewrite ?option.wlp_bind;
     repeat option.tactics.mixin;
     intros; try destruct_conjs).
Qed.

Section VarView.

  Inductive VarView {Σ} : Ty Σ -> Type :=
  | is_var {x} (xIn : x ∈ Σ) : VarView (t_evar xIn)
  | not_var {t} (H: forall x (xIn : x ∈ Σ), t <> t_evar xIn) : VarView t.

  Definition varview {Σ} (t : Ty Σ) : VarView t :=
    match t with
    | t_evar xIn => is_var xIn
    | _ => ltac:(constructor 2; discriminate)
    end.

  (*     apply noConfusion_inv in e. apply e. *)
  (*     apply noConfusion_inv in e. apply e. *)
  (*   Defined. *)
  (*   Eval cbv [varview] in @varview. *)
  (* Next Obligation *)
  (* | tf_bool *)
  (* | tf_func (T1 T2 : T Σ). *)
  (* Global Arguments tf_bool {_ _}. *)
  (* Global Arguments tf_func {_ _} T1 T2. *)

  (* Definition Var : TYPE := *)
  (*   fun Σ => {x & In x Σ}. *)

  (* Definition unfold : ⊢ Ty -> Sum Var (TyF Ty) := *)
  (*   fun Σ t => match t with *)
  (*              | t_evar xIn   => inl (_;xIn) *)
  (*              | t_bool       => inr (tf_bool) *)
  (*              | t_func t1 t2 => inr (tf_func t1 t2) *)
  (*              end. *)

  (* Definition fold : ⊢ Sum Var (TyF Ty) -> Ty := *)
  (*   fun Σ t => match t with *)
  (*              | inl (_;xIn) => t_evar xIn *)
  (*              | inr (tf_bool) => t_bool *)
  (*              | inr (tf_func t1 t2) => t_func t1 t2 *)
  (*              end. *)

End VarView.

Module Variant1.

  Definition flex : ⊢ Ty -> ∀ x, In x -> ◆Unit :=
    fun Σ t x xIn =>
      match varview t with
      | is_var yIn =>
          match occurs_check_view xIn yIn with
          | Same _      => η tt
          | Diff _ yIn' => Some (sooner2diamond (_; (xIn; (t_evar yIn', tt))))
          end
      | not_var _ =>
          option_map
            (fun t' => sooner2diamond (x; (xIn; (t', tt))))
            (occurs_check t xIn)
      end.

  Import option.notations.
  Set Equations With UIP.
  Lemma flex_sound {Σ y} (t : Ty Σ) (yIn : In y Σ) :
    wlp (flex t yIn) (fun _ ζ1 _ => ζ1 ⊨ t ~ t_evar yIn).
  Proof.
    unfold Unifies, flex, wlp.
    destruct (varview t).
    - destruct (occurs_check_view yIn xIn); cbn.
      + constructor. reflexivity.
      + constructor; cbn.
        now rewrite ?occurs_check_view_refl, ?occurs_check_view_thin.
    - repeat rewrite ?option.wlp_aplazy, ?option.wlp_map.
      generalize (occurs_check_sound t yIn). apply option.wlp_monotonic.
      intros t' ->; cbn. rewrite occurs_check_view_refl.
      apply thin_thick.
  Qed.

  Definition Unifier : TYPE :=
    Ty -> Ty -> ◆Unit.
  Definition BoxUnifier : TYPE :=
    Ty -> Ty -> □◆Unit.

  Section MguO.

    Context [Σ] (lmgu : ▻BoxUnifier Σ).

    Definition boxflex {x} (xIn : x ∈ Σ) (t : Ty Σ) : □◆Unit Σ :=
      box_intro_split (flex t xIn) (fun z zIn u => lmgu _ (t_evar xIn)[z↦u] t[z↦u]).

    Equations boxmgu : BoxUnifier Σ :=
    | t_evar xIn   | t            := boxflex xIn t;
    | s            | t_evar yIn   := boxflex yIn s;
    | t_bool       | t_bool       := fun _ _ => η tt;
    | t_func s1 s2 | t_func t1 t2 := fun _ ζ1 =>
                                       ⟨ ζ2 ⟩ _ <- boxmgu s1 t1 ζ1 ;;
                                       ⟨ ζ3 ⟩ _ <- boxmgu s2 t2 (Tri.trans ζ1 ζ2) ;;
                                       η tt;
    | _            | _            := fun _ _ => None.

  End MguO.

  Definition mgu : ⊢ Unifier :=
    fun Σ s t => T (@Löb _ boxmgu Σ s t).

  Lemma mgu_complete {Σ} (s t : Ty Σ) {Σ2} (ζ2 : Σ ⊒ Σ2) (HU : ζ2 ⊨ s ~ t) :
    wp (mgu s t) (fun Σ1 ζ1 _ => exists ζ12 : Σ1 ⊒ Σ2, ζ2 = Tri.trans ζ1 ζ12).
  Proof.
  Admitted.

End Variant1.

Module Variant2.

  Definition Unifier : TYPE :=
    Ty -> Ty -> ◆Ty.
  Definition BoxUnifier : TYPE :=
    Ty -> Ty -> □◆Ty.

  Definition flex : ⊢ Ty -> ∀ x, In x -> ◆Ty :=
    fun Σ t x xIn =>
      match t with
      | t_evar yIn =>
          match occurs_check_view xIn yIn with
          | Same _      => η (t_evar xIn)
          | Diff _ yIn' => Some (sooner2diamond (x; (xIn; (t_evar yIn', t_evar yIn'))))
          end
      | _ => option_map
               (fun t' => sooner2diamond (x; (xIn; (t', t'))))
               (occurs_check t xIn)
      end.

  Section MguO.

    Context [Σ] (lmgu : ▻BoxUnifier Σ).

    Definition boxflex {x} (xIn : x ∈ Σ) (t : Ty Σ) : □◆Ty Σ :=
      box_intro_split (flex t xIn) (fun z zIn u => lmgu _ (t_evar xIn)[z↦u] t[z↦u]).

    Equations boxmgu : BoxUnifier Σ :=
    | t_evar xIn   | t            := boxflex xIn t;
    | s            | t_evar yIn   := boxflex yIn s;
    | t_bool       | t_bool       := fun _ _ => η t_bool;
    | t_func s1 s2 | t_func t1 t2 := fun _ ζ1 =>
                                       ⟨ ζ2 ⟩ r1 <- boxmgu s1 t1 ζ1 ;;
                                       ⟨ ζ3 ⟩ r2 <- boxmgu s2 t2 (Tri.trans ζ1 ζ2) ;;
                                       η (t_func (realsubst_slow r1 ζ3) r2);
    | _            | _            := fun _ _ => None.

  End MguO.

  Definition mgu : ⊢ Unifier :=
    fun Σ s t => T (@Löb _ boxmgu Σ s t).

End Variant2.

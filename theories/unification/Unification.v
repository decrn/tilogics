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
     Classes.Equivalence
     Classes.Morphisms
     Program.Equality
     Program.Tactics
     Setoid
     Recdef.
From Equations Require Import
     Equations.
From Equations.Type Require
     Classes
     WellFounded.
From Equations.Prop Require
     Classes.
From Em Require Import
     Definitions Context Environment Prelude STLC Triangular Substitution.
Import ctx.
Import ctx.notations.
Import SigTNotations.

Set Implicit Arguments.

#[local] Arguments Ty_hole {Σ i} xIn.
#[local] Arguments Ty_bool {Σ}.
#[local] Arguments Ty_func {Σ}.
#[local] Open Scope indexed_scope.

Reserved Notation "w1 ⊒ w2" (at level 80).

Notation "□ A" := (Box Tri A) (at level 9, format "□ A", right associativity).
Notation "◇ A" := (DiamondT Tri id A) (at level 9, format "◇ A", right associativity).
Notation "? A" := (Option A) (at level 9, format "? A", right associativity).
Notation "◆ A" := (DiamondT Tri Option A) (at level 9, format "◆ A", right associativity).
Notation "A * B" := (Prod A B).

Section Löb.

  Context (A : TYPE) (step : ⊢ ▷A -> A).

  Obligation Tactic := auto using Nat.eq_le_incl, length_remove.
  Equations Löbaux {w : World} : A w by wf (length w) :=
  Löbaux := step (fun _ _ => Löbaux).
  Local Arguments Löbaux : clear implicits.

  Transparent Löbaux.
  Definition Löb : ⊢ A := Löbaux.

  Context (P : forall w : World, A w -> Type).
  Context (pstep : forall w,
        (forall x (xIn : x ∈ w), P (Löb (w - x))) ->
        P (step (fun x xIn => Löb (w - x)))).

  Definition Löb_elim : forall w, P (Löb w) :=
    Löbaux_elim P pstep.

End Löb.

Definition box2later {A} : ⊢ □A -> ▶A.
  intros w a x xIn t. apply a. econstructor.
  apply t. constructor.
Defined.

Definition sooner2diamond {A} : ⊢ ◀A -> ◇A :=
  fun w a =>
    match a with
      existT _ x (existT _ xIn (t , a)) =>
      existT _ (w - x) (pair (Tri.single x t) a)
    end.

Definition sooner2diamondtm {A} : ⊢ ◀A -> ◆A.
  intros w a. destruct a as [σ [σIn [t a]]].
  constructor.
  econstructor. split; try eassumption.
  econstructor 2. auto. constructor 1.
Defined.

Definition η {A} : ⊢ A -> ◆A :=
  fun w a => Some (existT _ w (Tri.refl, a)).
Arguments η {A w} a.

Definition η1 {A} {w x} {xIn : x ∈ w} (t : Ty (w - x)) (a : A (w - x)) : ◆A w :=
  sooner2diamondtm (existT _ x (existT _ xIn (t, a))).


(* Arguments thick {_} s x {_} u. *)
(* Notation "s [ x ↦ u ]" := (thick s x u) *)
(*   (at level 8, left associativity, *)
(*    format "s [ x ↦ u ]"). *)


(* Lemma thin_thick {w y} (yIn : y ∈ w) (s t : Ty (w - y)) : *)
(*   (thin yIn t)[y↦s] = t. *)
(* Proof. *)
(*   induction t; cbn; f_equal; auto. unfold thickIn. *)
(*   now rewrite occurs_check_view_thin. *)
(* Qed. *)

(* Infix "≽⁻" := Tri.geq (at level 80). *)
(* Infix "≽?" := Sub.geqb (at level 80). *)

Section OccursCheck.
  Import option.notations.

  Definition occurs_check_in : ⊢ ∀ x, In x -> ▷(Option (In x)) :=
    fun w x xIn y yIn =>
      match occurs_check_view yIn xIn with
      | Same _      => None
      | Diff _ xIn' => Some xIn'
      end.

  Definition occurs_check : ⊢ Ty -> ▷(Option Ty) :=
    fun w =>
      fix oc (t : Ty w) (y : nat) (yIn : y ∈ w) {struct t} :=
      match t with
      | Ty_hole xIn   => Some Ty_hole <*> occurs_check_in xIn yIn
      | Ty_bool       => Some Ty_bool
      | Ty_func T1 T2 => Some Ty_func <*> oc T1 y yIn <*> oc T2 y yIn
      end.

  Lemma occurs_check_thin {w x} (xIn : x ∈ w) (t : Ty (w - x)) :
    option.wp (eq t) (occurs_check (thin xIn t) xIn).
  Proof.
    induction t; cbn.
    - now constructor.
    - repeat rewrite ?option.wp_aplazy, ?option.wp_map.
      repeat option.tactics.mixin. congruence.
    - rewrite option.wp_map. unfold occurs_check_in.
      rewrite occurs_check_view_thin. now constructor.
  Qed.

  Lemma occurs_check_sound {w} (t : Ty w) {x} (xIn : x ∈ w) :
    option.wlp (fun t' => t = thin xIn t') (occurs_check t xIn).
  Proof.
    induction t; cbn.
    - now constructor.
    - repeat rewrite ?option.wlp_aplazy, ?option.wlp_map.
      repeat option.tactics.mixin. cbn. congruence.
    - unfold occurs_check_in.
      now destruct occurs_check_view; constructor.
  Qed.

  Lemma occurs_check_spec {w x} (xIn : x ∈ w) (t : Ty w) :
    option.spec
      (fun t' => t = thin xIn t')
      (t = Ty_hole xIn \/ Ty_subterm (Ty_hole xIn) t)
      (occurs_check t xIn).
  Proof.
    induction t; cbn.
    - constructor. reflexivity.
    - repeat option.tactics.mixin; subst; auto; right;
        match goal with
        | H: _ \/ Ty_subterm _ ?t |- _ =>
            destruct H;
            [ subst; constructor; constructor
            | constructor 2 with t; auto; constructor; constructor
            ]
        end.
    - unfold occurs_check_in.
      destruct (occurs_check_view xIn i0); constructor.
      + left. reflexivity.
      + reflexivity.
  Qed.

End OccursCheck.

Definition box_intro_split {A} :
  ⊢ A -> ▶□A -> □A :=
  fun w0 a la w1 ζ =>
    match ζ with
    | Tri.refl => a
    | Tri.cons x t ζ' => la x _ t _ ζ'
    end.

Definition SUBST : TYPE := Ty -> □Ty.
Section Subst.

  Context [w] (lsubst : ▷(Ty -> □Ty) w).

  Definition subst_in {x} (xIn : In x w) : □Ty w :=
    box_intro_split
      (Ty_hole xIn)
      (fun y yIn s =>
         match occurs_check_view yIn xIn with
         | Same _     => lsubst yIn s
         | Diff _ xIn => lsubst yIn (Ty_hole xIn)
         end).

  Definition subst : Ty w -> □Ty w :=
    fix subst (t : Ty w) : □Ty w :=
      match t with
      | Ty_hole xIn   => subst_in xIn
      | Ty_bool       => fun _ _ => Ty_bool
      | Ty_func T1 T2 => fun _ ζ => Ty_func (subst T1 _ ζ) (subst T2 _ ζ)
      end.

End Subst.

(* Definition realsubst_fast : ⊢ Ty -> □Ty := *)
(*   Löb SUBST subst. *)

Definition realsubst_slow : ⊢ Ty -> □Ty.
  refine (fix subst {w} (t : Ty w) {w1} ζ1 {struct ζ1} := _).
  destruct ζ1.
  - apply t.
  - refine (subst _ _ _ ζ1).
    apply (thick t).
    apply t0.
Defined.

Definition Hom (A B : TYPE) := ⊢ A -> B.

Definition fmap {A B} (f : Hom A B) : Hom ◆A ◆B.
Proof.
  intros w0 [[w1 [ζ1 a1]]|].
  - constructor 1. exists w1. split. auto. apply f. auto.
  - constructor 2.
Defined.
(* Notation "f <$> a" := (fmap f a) (at level 20). *)

Local Notation "s [ ζ ]" :=
  (Sub.subst s ζ)
    (at level 8, left associativity,
      format "s [ ζ ]").
(* Local Coercion Sub.triangular : Tri.Tri >-> Sub.Sub. *)

Section Mult.
  Import option.notations.

  Definition acc {A} {w0 w1} (ζ1 : w0 ⊒⁻ w1) : ◆A w1 -> ◆A w0 :=
    option.map (fun '(existT _ w2 (ζ2 , a)) => existT _ w2 (ζ1 ⊙⁻ ζ2, a)).

  Definition μ {A} : Hom ◆◆A ◆A :=
    fun w0 a0 => '(w1; (ζ1 , a1)) <- a0;; acc ζ1 a1.

  Definition ebind {A B} : Hom A ◆B -> Hom ◆A ◆B :=
    fun f w0 a0 => '(w1; (ζ1, a1)) <- a0 ;; acc ζ1 (f w1 a1).

  Definition bind {A B} : ⊢ ◆A -> □(A -> ◆B) -> ◆B :=
    fun w a0 f => '(w1; (ζ1 , a1)) <- a0 ;; acc ζ1 (f w1 ζ1 a1).

End Mult.

Notation "⟨ ζ ⟩ x <- ma ;; mb" :=
  (bind ma (fun _ ζ x => mb))
    (at level 80, x at next level,
      ma at next level, mb at level 200,
      right associativity).

(* see Kobayashi, S. (1997). Monad as modality. *)
Definition strength {A B} : Hom (□A * ◆B) (◆(□A * B)) :=
  fun w0 '(a0,b0) => bind b0 (fun w1 ζ1 b1 => η (_4 a0 ζ1, b1)).

(* Notation "ζ1 ≽ ζ2" := (Subgeq ζ1 ζ2) (at level 80). *)
(* Notation "ζ1 ≲ ζ2" := (Subleq ζ1 ζ2) (at level 80). *)
(* Notation "ζ1 ≼ ζ2" := (Trileq ζ1 ζ2) (at level 80). *)

Definition Property : TYPE :=
  fun w => forall w', w ⊒ˢ w' -> Prop.
  (* □PROP. *)

Module P.

  Section Instances.

    Context {w : World}.

    Definition iff (P Q : Property w) : Prop :=
      forall Δ ζ, P Δ ζ <-> Q Δ ζ.
    Infix "<->" := iff.

    Instance iff_refl : Reflexive iff.
    Proof. unfold Reflexive, iff. intros. reflexivity. Qed.
    Instance iff_sym : Symmetric iff.
    Proof. unfold Symmetric, iff. intros. now symmetry. Qed.
    Instance iff_trans : Transitive iff.
    Proof. unfold Transitive, iff. intros. now transitivity (y Δ ζ). Qed.

    Instance iff_equiv : Equivalence iff.
    Proof. constructor; auto with typeclass_instances. Qed.

    Definition and (P Q : Property w) : Property w :=
      fun _ ζ => P _ ζ /\ Q _ ζ.
    Instance proper_and : Proper (iff ==> iff ==> iff) and.
    Proof. firstorder. Qed.

    Definition impl (P Q : Property w) : Property w :=
      (fun w' ζ => P w' ζ -> Q w' ζ)%type.

    Definition nothing (P : Property w) : Prop :=
      forall w' ζ, P w' ζ -> False.
    Instance proper_nothing : Proper (iff ==> Logic.iff) nothing.
    Proof. intros ? ? ?. do 2 (apply forall_proper; intros ?). intuition. Qed.

    Definition max (P : Property w) : Property w :=
      and P (fun w1 ζ1 => forall w2 ζ2, P w2 ζ2 -> ζ1 ≽ˢ ζ2).
    Instance proper_max : Proper (iff ==> iff) max.
    Proof. firstorder. Qed.
    Instance proper_max' : Proper (iff ==> forall_relation (fun w => eq ==> Basics.flip Basics.impl)) max.
    Proof. repeat intro; subst; firstorder. Qed.

  End Instances.
  #[export] Existing Instance iff_refl.
  #[export] Existing Instance iff_sym.
  #[export] Existing Instance iff_trans.
  #[export] Existing Instance iff_equiv.
  #[export] Existing Instance proper_and.
  #[export] Existing Instance proper_nothing.
  #[export] Existing Instance proper_max.
  #[export] Existing Instance proper_max'.


  Notation "P <-> Q" := (iff P Q).

  Definition unifies : ⊢ Ty -> Ty -> Property :=
    fun w s t w1 (ζ1 : w ⊒ˢ w1) => s[ζ1] = t[ζ1].

  Definition unifiesX : ⊢ Ty -> Ty -> Property :=
    fun w0 s t =>
      match s , t with
      | Ty_hole xIn as s , t               => unifies s t
      | s               , Ty_hole yIn as t => unifies s t
      | Ty_bool          , Ty_bool          => fun _ _ => True
      | Ty_func s1 s2    , Ty_func t1 t2    => and (unifies s1 t1) (unifies s2 t2)
      | s               , t               => fun _ _ => False
      end.

  Definition unifiesY : ⊢ Ty -> Ty -> Property :=
    fun w0 =>
      fix ufs s t {struct s} :=
      match s , t with
      | Ty_hole xIn as s , t               => unifies s t
      | s               , Ty_hole yIn as t => unifies s t
      | Ty_bool          , Ty_bool          => fun _ _ => True
      | Ty_func s1 s2    , Ty_func t1 t2    => and (ufs s1 t1) (ufs s2 t2)
      | _               , _               => fun _ _ => False
      end.

  Lemma unifies_sym {w} (s t : Ty w) : iff (unifies s t) (unifies t s).
  Proof. now unfold iff, unifies. Qed.

  Lemma unifiesX_equiv {w} (s t : Ty w) : iff (unifies s t) (unifiesX s t).
  Proof.
    destruct s; cbn; [| |reflexivity]; try now destruct t.
    destruct t; auto.
    - split; intuition discriminate.
    - unfold iff, unifies, and; cbn. intuition congruence.
    - reflexivity.
  Qed.

  Lemma unifiesY_equiv {w} (s t : Ty w) : iff (unifies s t) (unifiesY s t).
  Proof.
    revert t; induction s; intros t; destruct t; cbn in *;
      try reflexivity;
      try (unfold iff, unifies; cbn; intuition congruence).
    - rewrite <- IHs1, <- IHs2.
      unfold iff, unifies, and; cbn.
      intuition congruence.
  Qed.

  Definition DClosed {w} (P : Property w) : Prop :=
    forall w1 w2 (ζ1 : w ⊒ˢ w1) (ζ2 : w ⊒ˢ w2),
      ζ1 ≽ˢ ζ2 -> P w1 ζ1 -> P w2 ζ2.

  Lemma dclosed_unifies {w} (s t : Ty w) : DClosed (P.unifies s t).
  Proof.
    unfold DClosed, P.unifies.
    intros ? ? ? ? [? ->] ?.
    Set Printing Coercions.
    rewrite ?Sub.subst_comp.
    now f_equal.
  Qed.

  Definition extend {w1 w2} (P : Property w1) (ζ1 : w1 ⊒ˢ w2) : Property w2 :=
    fun Δ ζ2 => P Δ (ζ1 ⊙ ζ2).

  Lemma extend_id {w0} (P : Property w0) :
    iff (extend P refl) P.
  Proof.
    unfold iff, extend. intros.
    now rewrite trans_refl_l.
  Qed.

  Lemma extend_and {w0 w1} (P Q : Property w0) (ζ1 : w0 ⊒ˢ w1) :
    iff (extend (and P Q) ζ1) (and (extend P ζ1) (extend Q ζ1)).
  Proof. reflexivity. Qed.

  Lemma extend_unifies {w0 w1} (s t : Ty w0) (ζ : w0 ⊒ˢ w1) :
    iff (unifies s[ζ] t[ζ]) (extend (unifies s t) ζ).
  Proof.
    unfold iff, extend, unifies. intros.
    now rewrite ?Sub.subst_comp.
  Qed.

  Lemma optimists {w0 w1 w2 w3} (P Q : Property w0) (ζ1 : w0 ⊒ˢ w1) (ζ2 : w1 ⊒ˢ w2) (ζ3 : w2 ⊒ˢ w3) :
    DClosed P ->
    max (extend P ζ1) ζ2 ->
    max (extend Q (ζ1 ⊙ ζ2)) ζ3 ->
    max (extend (and P Q) ζ1) (ζ2 ⊙ ζ3).
  Proof.
    unfold DClosed, extend.
    intros dcp [p12 pmax] [q123 qmax].
    split.
    split.
    - revert p12. apply dcp.
      apply Sub.geq_precom.
      apply Sub.geq_extend.
    - revert q123. now rewrite trans_assoc.
    - intros ? f [H1 H2].
      apply pmax in H1.
      destruct H1 as [g ?].
      subst f.
      apply Sub.geq_precom.
      apply qmax.
      now rewrite trans_assoc.
  Qed.

  Lemma optimists_unifies {w w1 w2 w3} {s1 s2 t1 t2 : Ty w}
    (ζ1 : w ⊒ˢ w1) (ζ2 : w1 ⊒ˢ w2) (ζ3 : w2 ⊒ˢ w3) :
    max (unifies s1[ζ1] t1[ζ1]) ζ2 ->
    max (unifies s2[ζ1 ⊙ ζ2] t2[ζ1 ⊙ ζ2]) ζ3 ->
    max (and (unifies s1[ζ1] t1[ζ1]) (unifies s2[ζ1] t2[ζ1])) (ζ2 ⊙ ζ3).
  Proof.
    unfold max, and, unifies. rewrite ?Sub.subst_comp.
    intros [p12 pmax] [q123 qmax]. split. split; congruence.
    intros w4 ζ4 [H1 H2].
    apply pmax in H1. destruct H1 as [ζ24 ->]. rewrite ?Sub.subst_comp in H2.
    apply qmax in H2. destruct H2 as [ζ34 ->].
    apply Sub.geq_precom.
    apply Sub.geq_extend.
  Qed.

End P.

(* Notation "ζ ⊨ s ~ t" := (Unifies s t ζ) (at level 90, s at level 69). *)

(* Fixpoint models' {w1 w2} (ι : Assignment w1) (ζ : w1 ⊒⁻ w2) : Prop := *)
(*   match ζ with *)
(*   | Tri.refl       => True *)
(*   | Tri.cons x t ζ => *)
(*       let ι' := env.remove _ ι _ in *)
(*       env.lookup ι _ = Sub.subst t ι' /\ models' ι' ζ *)
(*   end. *)

(* Definition models {w1 w2} (ι1 : Assignment w1) (ζ : w1 ⊒⁻ w2) : Prop. *)
(*   refine (exists (ι2 : Assignment w2), ι1 = _). *)
(*   apply env.tabulate. *)
(*   intros x xIn. *)
(*   refine (Sub.subst _ ι2). *)
(*   refine (realsubst_slow (Ty_hole xIn) ζ). *)
(* Defined. *)

Definition wp {A} : ⊢ ◆A -> □(A -> PROP) -> PROP :=
  fun w0 a0 POST => option.wp (fun '(w1; (ζ1 , a1)) => POST w1 ζ1 a1) a0.

Definition wlp {A} : ⊢ ◆A -> □(A -> PROP) -> PROP :=
  fun w0 a0 POST => option.wlp (fun '(w1; (ζ1 , a1)) => POST w1 ζ1 a1) a0.

Definition spec {A} : ⊢ ◆A -> □(A -> PROP) -> PROP -> PROP :=
  fun w0 a0 SPOST NPOST => option.spec (fun '(w1; (ζ1 , a1)) => SPOST w1 ζ1 a1) NPOST a0.

Lemma wp_η {A w} (a : A w) (POST : □(A -> PROP) w) :
  wp (η a) POST <-> T POST a.
Proof. unfold wp, η. now option.tactics.mixin. Qed.

Lemma wp_μ {A B w} (a : ◆A w) (f : □(A -> ◆B) w) (POST : □(B -> PROP) w) :
  wp (bind a f) POST <-> wp a (fun _ ζ1 a1 => wp (f _ ζ1 a1) (_4 POST ζ1)).
Proof.
  unfold wp, bind, acc, Diamond.
  now repeat
    (rewrite ?option.wp_bind, ?option.wp_map;
     repeat option.tactics.mixin;
     intros; try destruct_conjs).
Qed.

Lemma wlp_η {A w} (a : A w) (POST : □(A -> PROP) w) :
  wlp (η a) POST <-> T POST a.
Proof. unfold wlp, η. now option.tactics.mixin. Qed.

Lemma wlp_μ {A B w} (a : ◆A w) (f : □(A -> ◆B) w) (POST : □(B -> PROP) w) :
  wlp (bind a f) POST <-> wlp a (fun _ ζ1 a1 => wlp (f _ ζ1 a1) (_4 POST ζ1)).
Proof.
  unfold wlp, bind, acc, Diamond.
  now repeat
    (rewrite ?option.wlp_bind, ?option.wlp_map;
     repeat option.tactics.mixin;
     intros; try destruct_conjs).
Qed.

Lemma spec_η {A w} (a : A w) (SPOST : □(A -> PROP) w) (NPOST : PROP w) :
  spec (η a) SPOST NPOST <-> T SPOST a.
Proof.
  unfold spec, η. now option.tactics.mixin.
Qed.

Lemma spec_μ {A B w} (a : ◆A w) (f : □(A -> ◆B) w) (SPOST : □(B -> PROP) w) (NPOST : PROP w) :
  spec (bind a f) SPOST NPOST <->
  spec a (fun _ ζ1 a1 => spec (f _ ζ1 a1) (_4 SPOST ζ1) NPOST) NPOST.
Proof.
  unfold spec, bind, acc, Diamond.
  repeat
    (rewrite ?option.spec_bind, ?option.spec_map;
     repeat option.tactics.mixin;
     intros; try destruct_conjs); try reflexivity.
Qed.

Section VarView.

  Inductive VarView {w} : Ty w -> Type :=
  | is_var {x} (xIn : x ∈ w) : VarView (Ty_hole xIn)
  | not_var {t} (H: forall x (xIn : x ∈ w), t <> Ty_hole xIn) : VarView t.

  Definition varview {w} (t : Ty w) : VarView t :=
    match t with
    | Ty_hole xIn => is_var xIn
    | _ => ltac:(constructor 2; discriminate)
    end.

  (*     apply noConfusion_inv in e. apply e. *)
  (*     apply noConfusion_inv in e. apply e. *)
  (*   Defined. *)
  (*   Eval cbv [varview] in @varview. *)
  (* Next Obligation *)
  (* | tf_bool *)
  (* | tf_func (T1 T2 : T w). *)
  (* Global Arguments tf_bool {_ _}. *)
  (* Global Arguments tf_func {_ _} T1 T2. *)

  (* Definition Var : TYPE := *)
  (*   fun w => {x & In x w}. *)

  (* Definition unfold : ⊢ Ty -> Sum Var (TyF Ty) := *)
  (*   fun w t => match t with *)
  (*              | Ty_hole xIn   => inl (_;xIn) *)
  (*              | Ty_bool       => inr (tf_bool) *)
  (*              | Ty_func t1 t2 => inr (tf_func t1 t2) *)
  (*              end. *)

  (* Definition fold : ⊢ Sum Var (TyF Ty) -> Ty := *)
  (*   fun w t => match t with *)
  (*              | inl (_;xIn) => Ty_hole xIn *)
  (*              | inr (tf_bool) => Ty_bool *)
  (*              | inr (tf_func t1 t2) => Ty_func t1 t2 *)
  (*              end. *)

End VarView.

Lemma trivialproblem {w} (t : Ty w) :
  P.max (P.unifies t t) refl.
Proof.
  unfold P.max. split.
  - reflexivity.
  - intros ? ζ ?. exists ζ.
    now rewrite trans_refl_l.
Qed.

Lemma varelim {w x} (xIn : x ∈ w) (t : Ty (w - x)) :
  P.max (P.unifies (Ty_hole xIn) (thin xIn t)) (Sub.thick xIn t).
Proof.
  rewrite Sub.subst_thin.
  split.
  - unfold P.unifies. cbn.
    rewrite Sub.lookup_thick.
    unfold thickIn.
    rewrite occurs_check_view_refl.
    rewrite <- Sub.subst_comp.
    rewrite Sub.comp_thin_thick.
    rewrite Sub.subst_refl.
    reflexivity.
  - unfold P.unifies, Sub.geq. cbn. intros * Heq.
    exists (Sub.thin xIn ⊙ ζ2).
    apply env.lookup_extensional. intros y yIn.
    rewrite ?Sub.lookup_trans.
    rewrite Sub.lookup_thick.
    rewrite Sub.subst_comp.
    unfold thickIn.
    destruct (occurs_check_view xIn yIn); cbn.
    + apply Heq.
    + now rewrite Sub.lookup_thin.
Qed.

Lemma no_cycle {w} (t : Ty w) : ~ Ty_subterm t t.
Proof. induction (wellfounded (R:=@Ty_subterm w) t). intuition. Qed.

Lemma Ty_subterm_subst {w1 w2} (s t : Ty w1) (ζ : Sub.Sub w1 w2) :
  Ty_subterm s t -> Ty_subterm (Sub.subst s ζ) (Sub.subst t ζ).
Proof.
  unfold Ty_subterm. induction 1; cbn.
  - constructor 1; destruct H; constructor.
  - econstructor 2; eauto.
Qed.

Lemma nothing_unifies_occurs_strictly {w x} (xIn : x ∈ w) (t : Ty w) :
  Ty_subterm (Ty_hole xIn) t ->
  P.nothing (P.unifies (Ty_hole xIn) t).
Proof.
  unfold P.nothing, P.unifies; intros.
  apply no_cycle with (Sub.subst t ζ).
  rewrite <- H0 at 1.
  now apply Ty_subterm_subst.
Qed.

Module Variant1.

  Definition flex : ⊢ Ty -> ∀ x, In x -> ◆Unit :=
    fun w t x xIn =>
      match varview t with
      | is_var yIn =>
          match occurs_check_view xIn yIn with
          | Same _      => η tt
          | Diff _ yIn' => Some (sooner2diamond (_; (xIn; (Ty_hole yIn', tt))))
          end
      | not_var _ =>
          option_map
            (fun t' => sooner2diamond (x; (xIn; (t', tt))))
            (occurs_check t xIn)
      end.


  Lemma flex_sound {w y} (t : Ty w) (yIn : y ∈ w) :
    wlp (flex t yIn) (fun _ ζ1 _ => P.unifies t (Ty_hole yIn) (Sub.triangular ζ1)).
  Proof.
    unfold P.unifies, flex, wlp.
    destruct (varview t).
    - destruct (occurs_check_view yIn xIn).
      + constructor. reflexivity.
      + constructor. cbn - [Sub.subst].
        rewrite trans_refl_r. cbn.
        rewrite ?Sub.lookup_thick. unfold thickIn.
        now rewrite ?occurs_check_view_refl, ?occurs_check_view_thin.
    - repeat rewrite ?option.wlp_aplazy, ?option.wlp_map.
      generalize (occurs_check_sound t yIn).
      apply option.wlp_monotonic.
      intros t' ->. cbn.
      rewrite trans_refl_r.
      rewrite Sub.subst_thin.
      rewrite <- Sub.subst_comp.
      rewrite Sub.comp_thin_thick.
      rewrite Sub.subst_refl.
      rewrite Sub.lookup_thick.
      unfold thickIn.
      now rewrite occurs_check_view_refl.
  Qed.

  Lemma flex_complete {w0 w1 y} (ζ1 : w0 ⊒ˢ w1) (t : Ty w0) (yIn : y ∈ w0) :
    P.unifies t (Ty_hole yIn) ζ1 ->
    wp (flex t yIn) (fun mgw mgζ _ => Sub.triangular mgζ ≽ˢ ζ1).
  Proof.
    intros. unfold flex.
    destruct (varview t).
    - destruct (occurs_check_view yIn xIn).
      + constructor. apply Sub.geq_max.
      + constructor; cbn.
        rewrite trans_refl_r.
        apply (@varelim _ _ yIn).
        now symmetry.
    - unfold wp. apply option.wp_map.
      destruct (occurs_check_spec yIn t).
      + constructor. cbn. subst.
        rewrite trans_refl_r.
        apply varelim. now symmetry.
      + exfalso. destruct H1.
        * specialize (H0 _ yIn). contradiction.
        * apply nothing_unifies_occurs_strictly in H1.
          now apply (H1 _ ζ1).
  Qed.

  Lemma flex_spec {w x} (xIn : x ∈ w) (t : Ty w) :
    let P := P.unifies (Ty_hole xIn) t in
    spec
      (flex t xIn)
      (fun w' ζ' _ => P.max P (Sub.triangular ζ'))
      (P.nothing P).
  Proof.
    unfold flex.
    destruct (varview t).
    - destruct (occurs_check_view xIn xIn0); subst.
      + constructor. apply trivialproblem.
      + constructor. cbn.
        rewrite trans_refl_r.
        change (Ty_hole (in_thin xIn yIn)) with (thin xIn (Ty_hole yIn)).
        apply varelim.
    - unfold spec. rewrite option.spec_map.
      generalize (occurs_check_spec xIn t).
      apply option.spec_monotonic.
      + intros t' ->. cbn.
        rewrite trans_refl_r.
        apply varelim.
      + specialize (H _ xIn).
        intros []. contradiction.
        now apply nothing_unifies_occurs_strictly.
  Qed.

  Definition spec' {A} : ⊢ ◆A -> □(Option A -> PROP) -> PROP.
    refine (fun w0 a0 POST => _).
    destruct a0 as [[w1 [ζ1 a]]|].
    cbv. apply (POST w1 ζ1 (Some a)).
    apply (POST w0 Tri.refl None).
  Defined.

  Definition Wpure : TYPE -> TYPE :=
    fun A => □(A -> PROP) -> PROP.
  Definition DiamondT (M : TYPE -> TYPE) : TYPE -> TYPE :=
    fun A => M (fun w0 => {w1 : World & ((w0 ⊒⁻ w1) * A w1)}%type).
  Definition OptionT (M : TYPE -> TYPE) : TYPE -> TYPE :=
    fun A => M (Option A).

  Definition W := DiamondT (OptionT Wpure).

  Definition flexspecw : ⊢ Ty -> ∀ x, In x -> W Unit.
  Proof.
    cbv [Impl Valid Box Forall PROP W OptionT DiamondT Wpure Option].
    intros w0 t x xIn POST.
    refine (exists w1 : World, exists ζ1 : w0 ⊒⁻ w1, POST w1 ζ1 _).
    destruct (eq_dec (Ty_hole xIn)[Sub.triangular ζ1] t[Sub.triangular ζ1]).
    apply Some. exists w1. split. apply refl. apply tt.
    apply None.
  Defined.

  Definition flexspec : ⊢ Ty -> ∀ x, In x -> □(Option Unit -> PROP) -> PROP.
  Proof.
    cbv [Impl Valid Box Forall PROP].
    intros w0 t x xIn POST.
    refine (exists w1 : World, exists ζ1 : w0 ⊒⁻ w1, POST w1 ζ1 _).
    destruct (eq_dec (Ty_hole xIn)[Sub.triangular ζ1] t[Sub.triangular ζ1]).
    apply (Some tt).
    apply None.
  Defined.

  Definition order {Unit} : ⊢ (□(Option Unit -> PROP) -> PROP) -> (□(Option Unit -> PROP) -> PROP) -> PROP :=
    fun w0 PT QT =>
      forall (P Q : □(Option Unit -> PROP) w0),
        (forall w1 (ζ1 : w0 ⊒⁻ w1) (x : Option Unit w1),
            P w1 ζ1 x -> Q w1 ζ1 x) ->
        PT P -> QT Q.

  Lemma flexverify {w} (t : Ty w) {x} (xIn : x ∈ w) :
    order (spec' (flex t xIn)) (flexspec t xIn).
  Proof.
    unfold flex. destruct (varview t) as [y yIn|].
    - destruct (occurs_check_view xIn yIn); unfold order, spec', flexspec, η;
        cbn - [eq_dec]; intros P Q PQ HP.
      + exists w. exists Tri.refl. rewrite eq_dec_refl. auto.
      + exists (w - x). exists (Tri.single x (Ty_hole yIn)).
  Admitted.

  Definition cflex : ⊢ Ty -> Ty -> Option Unit :=
    fun w s t => if eq_dec s t then Some tt else None.

  Definition mg : ⊢ ◆Unit -> □(Option Unit -> PROP) :=
    fun w0 d w1 ζ1 o =>
      match o , d with
      | Some _ , Some (existT _ mgw (mgζ , _)) => Sub.triangular mgζ ≽ˢ Sub.triangular ζ1
      | None   , _                             => True
      | Some _ , None                          => False
      end.

  Module Related.
    Definition DUM {w0 w1} (ζ1 : w0 ⊒⁻ w1) (spec : Option Unit w1) : Type :=
      { m : ◆Unit w0 | mg m ζ1 spec }.

    Definition dret {w0 w1} (ζ1 : w0 ⊒⁻ w1) (a : Unit w0) : DUM ζ1 (Some a) :=
      exist _ (Some (w0; (Tri.refl, a))) (Sub.geq_max (Sub.triangular ζ1)).

    Definition flexspec {w0} (t : Ty w0) {x} (xIn : x ∈ w0) {w1} (ζ1 : w0 ⊒⁻ w1) : Option Unit w1 :=
      if eq_dec (Ty_hole xIn)[Sub.triangular ζ1] t[Sub.triangular ζ1] then Some tt else None.

    Program Definition dflex {w0} (t : Ty w0) {x} (xIn : x ∈ w0) {w1} (ζ1 : w0 ⊒⁻ w1) : DUM ζ1 (flexspec t xIn ζ1) :=
        match varview t with
        | is_var yIn =>
            match occurs_check_view xIn yIn with
            | Same _      => η tt
            | Diff _ yIn' => Some (sooner2diamond (_; (xIn; (Ty_hole yIn', tt))))
            end
        | not_var _ =>
            option_map
              (fun t' => sooner2diamond (x; (xIn; (t', tt))))
              (occurs_check t xIn)
        end.
    Admit Obligations.

  End Related.

  (* Module DijkstraM. *)
  (*   Definition obs {w} (m : ◆Unit w) {w2} (ζ2 : w ⊒ˢ w2) : Option Unit w2 := *)
  (*     match m with *)
  (*     | Some (x; (ζ1, a)) => if ζ1 ≽? ζ2 then Some a else None *)
  (*     | None              => None *)
  (*     end. *)

  (*   Definition DUM {w0 w1} (ζ1 : w0 ⊒⁻ w1) (spec : Option Unit w1) : Type := *)
  (*     { m : ◆Unit w0 | obs m ζ1 = spec }. *)

  (*   Definition dret {w0 w1} (ζ1 : w0 ⊒⁻ w1) (a : Unit w0) : DUM ζ1 (Some a) := *)
  (*     exist _ (Some (w0; (Tri.refl, a))) eq_refl. *)
  (* End DijkstraM. *)

  (* Lemma mg_bind {w0} (da : ◆Unit w0) (dk : □(Unit -> ◆Unit) w0) *)
  (*   {w1} (ζ1 : w0 ⊒⁻ w1) (oa : Option Unit w1) (ok : Unit w1 -> Option Unit w1) : *)
  (*   mg da ζ1 oa -> *)
  (*   (forall {w2} (ζ2 : w ⊒⁻ w2), ζ2 ≽ˢ ζ1 -> mg (dk w1 ζ1 tt) (ok tt) ζ2) -> *)
  (*   mg (bind da dk) ζ2 (option.bind oa ok). *)
  (* Proof. *)
  (*   unfold bind, option.bind, mg at 1. intros mga mgk. *)
  (*   destruct da as [[? []]|], oa; try easy. *)
  (*   destruct u, u0. now apply mgk. *)
  (* Qed. *)

  (* Lemma mg_acc {w w1} (ζ1 : w ⊒⁻ w1) (d : ◆Unit w1) (o : Option Unit w) {w2} (ζ2 : w ⊒⁻ w2) : *)
  (*   (* mg da oa ζ2 -> *) *)
  (*   (* (forall {w1} (ζ1 : w ⊒⁻ w1), ζ2 ≲ ζ1 -> mg (acc ζ1 (dk w1 ζ1 tt)) (ok tt) ζ2) -> *) *)
  (*   mg (acc ζ1 d) o ζ2. *)
  (* Proof. *)
  (*   destruct o; cbn; auto. *)
  (*   destruct d as [[? []]|]; cbn. admit. ; try easy. *)
  (*   destruct u, u0. now apply mgk. *)
  (* Qed. *)

  Lemma flexcorrect {w} (t : Ty w) {x} (xIn : x ∈ w) {w2} (ζ2 : w ⊒⁻ w2) :
    mg (flex t xIn) ζ2 (cflex (Ty_hole xIn)[Sub.triangular ζ2] t[Sub.triangular ζ2]).
  Proof.
    unfold cflex, mg. destruct (eq_dec (Ty_hole xIn)[Sub.triangular ζ2] t[Sub.triangular ζ2]).
    - unfold flex. destruct (varview t) as [y yIn|].
      + destruct (occurs_check_view xIn yIn); cbn.
        * apply Sub.geq_max.
        * rewrite trans_refl_r. now apply varelim.
      + destruct (occurs_check_spec xIn t) as [|[]]; cbn.
        * rewrite trans_refl_r. subst. now apply varelim.
        * now apply H in H0.
        * apply nothing_unifies_occurs_strictly in H0.
          apply (H0 _ _ e).
    - destruct (flex t xIn) as [[? [? []]]|]; auto.
  Qed.

  Definition CMGU : TYPE := Ty -> Ty -> □(Option Unit).

  Section CMgu.
    Import option.notations.
    (* Context [w] (lcmgu : ▻CMGU w). *)

    Definition cmgu : ⊢ CMGU :=
      fun w => fix cmgu s t :=
        match s , t with
        | Ty_hole xIn as s , t               => fun _ ζ => cflex s[Sub.triangular ζ] t[Sub.triangular ζ]
        | s               , Ty_hole yIn as t => fun _ ζ => cflex s[Sub.triangular ζ] t[Sub.triangular ζ]
        | Ty_bool          , Ty_bool          => fun _ _ => Some tt
        | Ty_func s1 s2    , Ty_func t1 t2    => fun _ ζ => 'tt <- cmgu s1 t1 _ ζ ;; 'tt <- cmgu s2 t2 _ ζ ;; Some tt
        | _               , _               => fun _ _ => None
        end.
  End CMgu.

  (* Definition cmgu : ⊢ CMGU. *)
  (*   intros w. apply Löb. unfold Valid, Impl. intros w1. Check gcmgu. *)
  (*   fun w s t => T (@Löb _ @gcmgu w s t). *)

  Definition Unifier : TYPE :=
    Ty -> Ty -> ◆Unit.
  Definition BoxUnifier : TYPE :=
    Ty -> Ty -> □◆Unit.

  Definition UnifierSpec : ⊢ Unifier -> PROP :=
    fun w u =>
      forall t1 t2,
        let P := P.unifies t1 t2 in
        spec
          (u t1 t2)
          (fun w2 ζ2 _ => P.max P (Sub.triangular ζ2))
          (P.nothing P).

  Definition BoxUnifierSpec : ⊢ BoxUnifier -> PROP :=
    fun w bu =>
      forall t1 t2 w1 (ζ1 : w ⊒⁻ w1),
        let P := P.unifies t1[Sub.triangular ζ1] t2[Sub.triangular ζ1] in
        spec
          (bu t1 t2 w1 ζ1)
          (fun w2 ζ2 _ => P.max P (Sub.triangular ζ2))
          (P.nothing P).

  Section MguO.

    Context [w] (lmgu : ▷BoxUnifier w).
    Context (lmgu_spec : forall x (xIn : x ∈ w),
                BoxUnifierSpec (lmgu xIn)).

    Definition boxflex {x} (xIn : x ∈ w) (t : Ty w) : □◆Unit w :=
      box_intro_split
        (flex t xIn)
        (fun z zIn u =>
           let ζ := Sub.thick zIn u in
           lmgu _ (Ty_hole xIn)[ζ] t[ζ]).

    Import P.

    Lemma boxflex_spec {x} (xIn : x ∈ w) (t : Ty w) (w1 : World) (ζ1 : w ⊒⁻ w1) :
      let P := P.unifies (Ty_hole xIn)[Sub.triangular ζ1] t[Sub.triangular ζ1] in
      spec (boxflex xIn t ζ1) (fun w2 ζ2 _ => P.max P (Sub.triangular ζ2)) (P.nothing P).
    Proof.
      destruct ζ1; cbn - [Sub.subst].
      - rewrite ?Sub.subst_refl. apply flex_spec.
      - rewrite ?Sub.subst_comp. apply lmgu_spec.
    Qed.

    Definition boxmgu : BoxUnifier w :=
      fix bmgu s t {struct s} :=
        match s , t with
        | Ty_hole xIn   , t            => boxflex xIn t
        | s            , Ty_hole yIn   => boxflex yIn s
        | Ty_bool       , Ty_bool       => fun _ _ => η tt
        | Ty_func s1 s2 , Ty_func t1 t2 =>
            fun _ ζ1 =>
              ⟨ ζ2 ⟩ _ <- bmgu s1 t1 _ ζ1 ;;
              ⟨ ζ3 ⟩ _ <- bmgu s2 t2 _ (ζ1 ⊙⁻ ζ2) ;;
              η tt
        | _            , _            => fun _ _ => None
        end.

    Section boxmgu_elim.

      Context (P : Ty w -> Ty w -> □◆Unit w -> Type).
      Context (fflex1 : forall (x : nat) (xIn : x ∈ w) (t : Ty w), P (Ty_hole xIn) t (boxflex xIn t)).
      Context (fflex2 : forall (x : nat) (xIn : x ∈ w) (t : Ty w), P t (Ty_hole xIn) (boxflex xIn t)).
      Context (fbool : P Ty_bool Ty_bool (fun (w1 : World) (_ : w ⊒⁻ w1) => η tt)).
      Context (fbool_func : forall T1 T2 : Ty w, P Ty_bool (Ty_func T1 T2) (fun (w1 : World) (_ : w ⊒⁻ w1) => None)).
      Context (ffunc_bool : forall T1 T2 : Ty w, P (Ty_func T1 T2) Ty_bool (fun (w1 : World) (_ : w ⊒⁻ w1) => None)).
      Context (ffunc : forall s1 s2 t1 t2 : Ty w,
        (P s1 t1 (boxmgu s1 t1)) ->
        (P s2 t2 (boxmgu s2 t2)) ->
        P (Ty_func s1 s2) (Ty_func t1 t2)
          (fun (w1 : World) (ζ1 : w ⊒⁻ w1) =>
           bind (boxmgu s1 t1 ζ1)
             (fun (w2 : World) (ζ2 : w1 ⊒⁻ w2) (_ : Unit w2) =>
              bind (boxmgu s2 t2 (ζ1 ⊙⁻ ζ2)) (fun (w3 : World) (_ : w2 ⊒⁻ w3) (_ : Unit w3) => η tt)))).

      Lemma boxmgu_elim : forall (t1 t2 : Ty w), P t1 t2 (boxmgu t1 t2).
      Proof. induction t1; intros t2; cbn; auto; destruct t2; auto. Qed.

    End boxmgu_elim.

    (* Lemma boxmgu_correct (t1 t2 : Ty w) : *)
    (*   forall {w1} (ζ1 : w ⊒⁻ w1) {w2} (ζ2 : w1 ⊒⁻ w2), *)
    (*     mg (boxmgu t1 t2 ζ1) (cmgu t1 t2 (ζ1 ⊙ ζ2)) ζ2. *)
    (* Proof. *)
    (*   pattern (boxmgu t1 t2). apply boxmgu_elim; clear t1 t2. *)
    (*   - admit. *)
    (*   - admit. *)
    (*   - intros. exists ζ2. cbn - [Sub.comp]. now rewrite Sub.comp_id_left. *)
    (*   - intros. constructor. *)
    (*   - intros. constructor. *)
    (*   - intros * IH1 IH2 *. cbn. *)
    (*     (* apply (mg_bind (boxmgu s1 t1 ζ1) _ (cmgu s1 t1 (ζ1 ⊙ ζ2))); auto. *) *)
    (* Admitted. *)

    (* Lemma boxmgu_spec : BoxUnifierSpec boxmgu. *)
    (* Proof. *)
    (*   intros s t. pattern (boxmgu s t). *)
    (*   apply boxmgu_elim; clear s t. *)
    (*   - cbn. intros. apply boxflex_spec. *)
    (*   - cbn. intros x xIn t w1 ζ1. *)
    (*     generalize (boxflex_spec xIn t ζ1). cbn. *)
    (*     apply option.spec_monotonic. *)
    (*     + intros [w2 [ζ2 []]] H. *)
    (*       now rewrite unifies_sym. *)
    (*     + intros H. *)
    (*       now rewrite unifies_sym. *)
    (*   - constructor. apply trivialproblem. *)
    (*   - constructor. discriminate. *)
    (*   - constructor. discriminate. *)
    (*   - cbn. intros. *)
    (*     rewrite spec_μ. *)
    (*     generalize (H w1 ζ1). clear H. *)
    (*     apply option.spec_monotonic. *)
    (*     intros [w2 [ζ2 _]] ?. *)
    (*     rewrite spec_μ. *)
    (*     generalize (H0 w2 (Tri.trans ζ1 ζ2)). clear H0. *)
    (*     apply option.spec_monotonic. *)
    (*     intros [w3 [ζ3 _]] ?. *)
    (*     constructor. unfold four. *)
    (*     + rewrite Tri.trans_refl, unifiesX_equiv; cbn. *)
    (*       rewrite Sub.triangular_trans. *)
    (*       rewrite Sub.triangular_trans in H0. *)
    (*       now apply optimists_unifies. *)
    (*     + admit. *)
    (*     + admit. *)
    (* Admitted. *)

    Lemma boxmgu_sound (t1 t2 : Ty w) :
      forall {w1} (ζ1 : w ⊒⁻ w1),
        wlp
          (boxmgu t1 t2 ζ1)
          (fun w2 ζ2 _ => P.unifies t1[Sub.triangular ζ1] t2[Sub.triangular ζ1] (Sub.triangular ζ2)).
    Proof.
      pattern (boxmgu t1 t2).
      apply boxmgu_elim; clear t1 t2; cbn; intros; try (now constructor).
      - destruct (boxflex_spec xIn t ζ1); constructor.
        destruct a as [w2 [ζ2 []]]. apply H.
      - destruct (boxflex_spec xIn t ζ1); constructor.
        destruct a as [w2 [ζ2 []]]. apply unifies_sym. apply H.
      - rewrite wlp_μ. generalize (H _ ζ1). clear H.
        apply option.wlp_monotonic. intros [w2 [ζ2 _]] ?.
        rewrite wlp_μ. generalize (H0 _ (ζ1 ⊙⁻ ζ2)).
        apply option.wlp_monotonic. intros [w3 [ζ3 _]] ?.
        constructor. unfold _4. cbn.
        rewrite ?Sub.triangular_trans. cbn.
        rewrite trans_refl_r.
        apply unifiesX_equiv. cbn.
        split.
        + revert H. apply dclosed_unifies. apply Sub.geq_extend.
        + revert H1. unfold unifies.
          now rewrite ?Sub.triangular_trans, ?Sub.subst_comp.
    Qed.

    Lemma boxmgu_complete (t1 t2 : Ty w) :
      forall {w0} (ζ0 : w ⊒⁻ w0) [w1] (ζ1 : w0 ⊒ˢ w1),
        P.unifies t1[Sub.triangular ζ0] t2[Sub.triangular ζ0] ζ1 ->
        wp (boxmgu t1 t2 ζ0) (fun mgw mgζ _ => Sub.triangular mgζ ≽ˢ ζ1).
    Proof.
      pattern (boxmgu t1 t2).
      apply boxmgu_elim; clear t1 t2;
        cbn - [Sub.subst]; intros; try (now constructor);
        try discriminate.
      - destruct (boxflex_spec xIn t ζ0).
        + constructor. destruct a as [w2 [ζ2 []]]. now apply H0.
        + now apply H0 in H.
      - destruct (boxflex_spec xIn t ζ0).
        + constructor. destruct a as [w2 [ζ2 []]]. now apply H0.
        + now apply unifies_sym, H0 in H.
      - constructor. apply Sub.geq_max.
      - apply P.unifiesX_equiv in H1. destruct H1 as [HU1 HU2].
        rewrite wp_μ. generalize (H _ ζ0 _ ζ1 HU1). clear H.
        apply option.wp_monotonic. intros [mgw1 [mgζ1 _]] [ζ1' ->].
        assert (P.unifies s2[Sub.triangular (ζ0 ⊙⁻ mgζ1)] t2[Sub.triangular (ζ0 ⊙⁻ mgζ1)] ζ1') as HU2'.
        { revert HU2. unfold unifies.
          now rewrite ?Sub.triangular_trans, ?Sub.subst_comp.
        }
        rewrite wp_μ. generalize (H0 _ (ζ0 ⊙⁻ mgζ1) _ ζ1' HU2').
        apply option.wp_monotonic. intros [mgw2 [mgζ2 _]] [ζ2' ->].
        constructor. unfold _4.
        rewrite ?Sub.triangular_trans.
        apply Sub.geq_precom.
        apply Sub.geq_precom.
        apply Sub.geq_max.
    Qed.

    Lemma boxmgu_spec' : BoxUnifierSpec boxmgu.
    Proof.
      unfold BoxUnifierSpec. intros *.
      pose proof (boxmgu_complete t1 t2 ζ1) as Hcompl.
      destruct (boxmgu_sound t1 t2 ζ1); constructor.
      - destruct a as [w2 [ζ2 []]]. split; auto.
        intros w3 ζ3 Hζ3. specialize (Hcompl w3 ζ3 Hζ3). revert Hcompl.
        unfold wp. now rewrite option.wp_match.
      - intros w3 ζ3 Hζ3. specialize (Hcompl w3 ζ3 Hζ3). revert Hcompl.
        unfold wp. now rewrite option.wp_match.
    Qed.

  End MguO.

  Definition bmgu : ⊢ BoxUnifier :=
    fun w s t => Löb boxmgu _ s t.

  Definition mgu : ⊢ Unifier :=
    fun w s t => T (@bmgu w s t).

  Lemma bmgu_spec w : @BoxUnifierSpec w (@bmgu w).
  Proof.
    pattern (@bmgu w). revert w. apply Löb_elim.
    intros w IH. now apply boxmgu_spec'.
  Qed.

  Definition mgu_spec w : UnifierSpec (@mgu w).
  Proof.
    unfold UnifierSpec, mgu. intros t1 t2.
    specialize (bmgu_spec t1 t2 Tri.refl).
    apply option.spec_monotonic; cbn.
    - intros [w1 [ζ1 []]]. now rewrite ?Sub.subst_refl.
    - now rewrite ?Sub.subst_refl.
  Qed.

  Definition boxsolve : ⊢ List (Prod Ty Ty) -> □◆Unit :=
    fix solve {w} cs {struct cs} :=
      match cs with
      | List.nil => fun w1 ζ1 => η tt
      | List.cons (t1,t2) cs =>
          fun w1 ζ1 =>
            ⟨ ζ2 ⟩ _ <- bmgu t1 t2 ζ1 ;;
            solve cs _ (ζ1 ⊙⁻ ζ2)
         end.

  Definition solve : ⊢ List (Prod Ty Ty) -> ◆Unit :=
    fun w cs => boxsolve cs Tri.refl.

  Import option.notations.

  Definition prenex {A} :
    ⊢ FreeM A -> ?◇⁺(List (Ty * Ty) * A) :=
    fix pr {w} m {struct m} :=
    match m with
    | Ret_Free _ _ a => Some (w; (refl, (List.nil, a)))
    | Fail_Free _ _ => None
    | Bind_AssertEq_Free _ _ t1 t2 m =>
        '(w1; (r1, (cs, a))) <- pr m;;
        let t1' := persist w t1 w1 r1 in
        let t2' := persist w t2 w1 r1 in
        let c   := (t1', t2') in
        Some (w1; (r1, (cons c cs, a)))
    | Bind_Exists_Free _ _ i m =>
        '(w1; (r1, csa)) <- pr m ;;
        Some (w1; (step ⊙ r1, csa))
    end.

  Definition solve_ng {A} {pA : Persistent Tri.Tri A} :
    FreeM A ctx.nil -> ?◇⁺ A ctx.nil :=
    fun m =>
      '(w1; (r, (cs, a))) <- prenex m ;;
      '(w2; (ζ, tt))      <- solve cs;;
      Some (w2; (alloc.nil_l,persist _ a _ ζ)).

End Variant1.
Export Variant1.

Module Variant2.

  Definition Unifier : TYPE :=
    Ty -> Ty -> ◆Ty.
  Definition BoxUnifier : TYPE :=
    Ty -> Ty -> □◆Ty.

  Definition flex : ⊢ Ty -> ∀ x, In x -> ◆Ty :=
    fun w t x xIn =>
      match t with
      | Ty_hole yIn =>
          match occurs_check_view xIn yIn with
          | Same _      => η (Ty_hole xIn)
          | Diff _ yIn' => Some (sooner2diamond (x; (xIn; (Ty_hole yIn', Ty_hole yIn'))))
          end
      | _ => option_map
               (fun t' => sooner2diamond (x; (xIn; (t', t'))))
               (occurs_check t xIn)
      end.

  Section MguO.

    Context [w] (lmgu : ▷BoxUnifier w).

    Definition boxflex {x} (xIn : x ∈ w) (t : Ty w) : □◆Ty w :=
      box_intro_split
        (flex t xIn)
        (fun z zIn u =>
           let ζ := Sub.thick zIn u in
           lmgu _ (Ty_hole xIn)[ζ] t[ζ]).

    Equations boxmgu : BoxUnifier w :=
    | Ty_hole xIn   | t            := boxflex xIn t;
    | s            | Ty_hole yIn   := boxflex yIn s;
    | Ty_bool       | Ty_bool       := fun _ _ => η Ty_bool;
    | Ty_func s1 s2 | Ty_func t1 t2 := fun _ ζ1 =>
                                       ⟨ ζ2 ⟩ r1 <- boxmgu s1 t1 ζ1 ;;
                                       ⟨ ζ3 ⟩ r2 <- boxmgu s2 t2 (ζ1 ⊙⁻ ζ2) ;;
                                       η (Ty_func (realsubst_slow r1 ζ3) r2);
    | _            | _            := fun _ _ => None.

  End MguO.

  Definition mgu : ⊢ Unifier :=
    fun w s t => T (@Löb _ boxmgu w s t).


End Variant2.

Fixpoint compose {w0 w1} (ζ : w0 ⊒⁻ w1) : Assignment w1 -> Assignment w0 :=
  match ζ in (_ ⊒⁻ c) return (Assignment c -> Assignment w0) with
  | Tri.refl => fun ass : Assignment w0 => ass
  | @Tri.cons _ w' x xIn t ζ =>
      fun ass  =>
        let ass' := compose ζ ass in
        env.insert xIn ass' (inst t ass')
  end.

Definition compose' {w0 w1} (ζ : w0 ⊒⁻ w1) : Assignment w1 -> Assignment w0.
Proof.
  intros ass.
  apply env.tabulate.
  intros x xIn.
  apply (inst (env.lookup (Sub.triangular ζ) xIn) ass).
Defined.

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
  Arith.PeanoNat.
From Equations Require Import
  Equations.
From Em Require Import
  Definitions
  Context
  Prelude
  STLC
  Triangular.

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

Ltac folddefs :=
  repeat
    match goal with
    | H: context[@Tri.refl ?w] |- _ =>
        change_no_check (@Tri.refl w) with (@refl Tri _ w) in H
    | |- context[@Tri.refl ?w] =>
        change_no_check (@Tri.refl w) with (@refl Tri _ w)
    | |- context[Tri.cons ?x ?t ?r] =>
        change_no_check (Tri.cons x t r) with (thick x t ⊙⁻ r)
    end.

Section MoveMe.

  Import (hints) Tri.

  Lemma persist_thin_thick {w x} (xIn : x ∈ w) (s t : Ty (w - x)) :
    persist _ (thin xIn t) _ (thick (R := Tri) x s) = t.
  Proof.
    induction t; cbn - [thick]; try rewrite Tri.persist_fix; f_equal; auto.
    cbn. unfold thickIn. now rewrite ctx.occurs_check_view_thin.
  Qed.

End MoveMe.

Module BoveCapretta.

  Set Case Analysis Schemes.
  Inductive dom (w : World) : Type :=
  | domstep : (forall x (xIn : x ∈ w), dom (w - x)) -> dom w.

  Obligation Tactic := auto using Nat.eq_le_incl, ctx.length_remove.
  Equations indom {w : World} : dom w by wf (ctx.length w) :=
  indom := domstep (fun _ _ => indom).
  #[global] Arguments indom w : clear implicits.

  Definition dom_inv w (d : dom w) :
    (forall x (xIn : x ∈ w), dom (w - x)) :=
    match d with domstep x => x end.

End BoveCapretta.

Section Löb.

  Context (A : TYPE) (step : ⊢ ▷A -> A).

  Obligation Tactic := auto using Nat.eq_le_incl, ctx.length_remove.
  Equations Löbaux {w : World} : A w by wf (ctx.length w) :=
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

Section Operations.
  Import (hints) Tri.

  Definition box2later {A} : ⊢ □A -> ▶A.
    intros w a x xIn t. apply a. econstructor.
    apply t. constructor.
  Defined.

  Definition sooner2diamond {A} : ⊢ ◀A -> ◇A :=
    fun w a =>
      match a with
        existT _ x (existT _ xIn (t , a)) =>
        existT _ (w - x) (pair (thick (R := Tri) x t) a)
      end.

  Definition sooner2diamondtm {A} : ⊢ ◀A -> ◆A.
    intros w a. destruct a as [σ [σIn [t a]]].
    constructor.
    econstructor. split; try eassumption.
    econstructor 2. auto. constructor 1.
  Defined.

  Definition η {A} : ⊢ A -> ◆A :=
    fun w a => Some (existT _ w (refl, a)).
  #[global] Arguments η {A w} a.

  Definition η1 {A} {w x} {xIn : x ∈ w} (t : Ty (w - x)) (a : A (w - x)) : ◆A w :=
    sooner2diamondtm (existT _ x (existT _ xIn (t, a))).

  Definition tell {w0 w1} (r : Tri w0 w1) : ◆Unit w0 :=
    Some (w1; (r, tt)).

  Definition tell1 {w x} (xIn : x ∈ w) (t : Ty (w - x)) : ◆Unit w :=
    Some ((w - x); (thick (R := Tri) x t, tt)).

End Operations.

Section OccursCheck.
  Import option.notations.

  Definition occurs_check_in : ⊢ ∀ x, ctx.In x -> ▷(Option (ctx.In x)) :=
    fun w x xIn y yIn =>
      match ctx.occurs_check_view yIn xIn with
      | ctx.Same _      => None
      | ctx.Diff _ xIn' => Some xIn'
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
      rewrite ctx.occurs_check_view_thin. now constructor.
  Qed.

  Lemma occurs_check_sound {w} (t : Ty w) {x} (xIn : x ∈ w) :
    option.wlp (fun t' => t = thin xIn t') (occurs_check t xIn).
  Proof.
    induction t; cbn.
    - now constructor.
    - repeat rewrite ?option.wlp_aplazy, ?option.wlp_map.
      repeat option.tactics.mixin. cbn. congruence.
    - unfold occurs_check_in.
      now destruct ctx.occurs_check_view; constructor.
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
      destruct (ctx.occurs_check_view xIn i0); constructor.
      + left. reflexivity.
      + reflexivity.
  Qed.

End OccursCheck.

Definition Hom (A B : TYPE) := ⊢ A -> B.

Definition fmap {A B} (f : Hom A B) : Hom ◆A ◆B.
Proof.
  intros w0 [[w1 [ζ1 a1]]|].
  - constructor 1. exists w1. split. auto. apply f. auto.
  - constructor 2.
Defined.
(* Notation "f <$> a" := (fmap f a) (at level 20). *)

Local Notation "s [ ζ ]" :=
  (persist _ s _ ζ)
    (at level 8, left associativity,
      format "s [ ζ ]").
(* Local Coercion Sub.triangular : Tri.Tri >-> Sub.Sub. *)

Section Mult.
  Import option.notations.
  Import (hints) Tri.

  Definition acc {A} {w0 w1} (ζ1 : w0 ⊒⁻ w1) : ◆A w1 -> ◆A w0 :=
    option.map (fun '(existT _ w2 (ζ2 , a)) => existT _ w2 (ζ1 ⊙⁻ ζ2, a)).

  Definition μ {A} : Hom ◆◆A ◆A :=
    fun w0 a0 => '(w1; (ζ1 , a1)) <- a0;; acc ζ1 a1.

  Definition ebind {A B} : Hom A ◆B -> Hom ◆A ◆B :=
    fun f w0 a0 => '(w1; (ζ1, a1)) <- a0 ;; acc ζ1 (f w1 a1).

  Definition bind {A B} : ⊢ ◆A -> □(A -> ◆B) -> ◆B :=
    fun w a0 f => '(w1; (ζ1 , a1)) <- a0 ;; acc ζ1 (f w1 ζ1 a1).

  (* see Kobayashi, S. (1997). Monad as modality. *)
  Definition strength {A B} : Hom (□A * ◆B) (◆(□A * B)) :=
    fun w0 '(a0,b0) => bind b0 (fun w1 ζ1 b1 => η (_4 a0 ζ1, b1)).

End Mult.

#[local] Notation "⟨ ζ ⟩ x <- ma ;; mb" :=
  (bind ma (fun _ ζ x => mb))
    (at level 80, x at next level,
      ma at next level, mb at level 200,
      right associativity).

Section VarView.

  Inductive VarView {w} : Ty w -> Type :=
  | is_var {x} (xIn : x ∈ w) : VarView (Ty_hole xIn)
  | not_var {t} (H: forall x (xIn : x ∈ w), t <> Ty_hole xIn) : VarView t.

  Definition varview {w} (t : Ty w) : VarView t :=
    match t with
    | Ty_hole xIn => is_var xIn
    | _ => ltac:(constructor 2; discriminate)
    end.

End VarView.

Module Variant1.

  Import (hints) Tri.

  Definition Flex : TYPE :=
    Ty -> ∀ x, ctx.In x -> ◆Unit.
  Definition Unifier : TYPE :=
    Ty -> Ty -> ◆Unit.
  Definition BoxFlex : TYPE :=
    Ty -> ∀ x, ctx.In x -> □◆Unit.
  Definition BoxUnifier : TYPE :=
    Ty -> Ty -> □◆Unit.

  Definition flex : ⊢ Flex :=
    fun w t x xIn =>
      match varview t with
      | is_var yIn =>
          match ctx.occurs_check_view xIn yIn with
          | ctx.Same _      => η tt
          | ctx.Diff _ yIn' => tell1 xIn (Ty_hole yIn')
          end
      | not_var _ =>
          match occurs_check t xIn with
          | Some t' => tell1 xIn t'
          | None    => None
          end
      end.

  Section MguO.

    Import (hints) Tri.

    Context [w] (lmgu : ▷BoxUnifier w).

    Definition boxflex (t : Ty w) {x} (xIn : x ∈ w) : □◆Unit w :=
      Tri.box_intro_split
        (flex t xIn)
        (fun z zIn u =>
           let ζ := thick (R := Tri) z u in
           lmgu _ (Ty_hole xIn)[ζ] t[ζ]).

    Definition boxmgu : BoxUnifier w :=
      fix bmgu s t {struct s} :=
        match s , t with
        | Ty_hole xIn   , t            => boxflex t xIn
        | s            , Ty_hole yIn   => boxflex s yIn
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
      Context (fflex1 : forall (x : nat) (xIn : x ∈ w) (t : Ty w), P (Ty_hole xIn) t (boxflex t xIn)).
      Context (fflex2 : forall (x : nat) (xIn : x ∈ w) (t : Ty w), P t (Ty_hole xIn) (boxflex t xIn)).
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


  End MguO.

  Definition bmgu : ⊢ BoxUnifier :=
    fun w s t => Löb boxmgu _ s t.

  Definition mgu : ⊢ Unifier :=
    fun w s t => T (@bmgu w s t).


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

  Import (hints) Tri.

  Definition Unifier : TYPE :=
    Ty -> Ty -> ◆Ty.
  Definition BoxUnifier : TYPE :=
    Ty -> Ty -> □◆Ty.

  Definition flex : ⊢ Ty -> ∀ x, ctx.In x -> ◆Ty :=
    fun w t x xIn =>
      match t with
      | Ty_hole yIn =>
          match ctx.occurs_check_view xIn yIn with
          | ctx.Same _      => η (Ty_hole xIn)
          | ctx.Diff _ yIn' => Some (sooner2diamond (x; (xIn; (Ty_hole yIn', Ty_hole yIn'))))
          end
      | _ => option_map
               (fun t' => sooner2diamond (x; (xIn; (t', t'))))
               (occurs_check t xIn)
      end.

  Section MguO.

    Context [w] (lmgu : ▷BoxUnifier w).

    Definition boxflex {x} (xIn : x ∈ w) (t : Ty w) : □◆Ty w :=
      Tri.box_intro_split
        (flex t xIn)
        (fun z zIn u =>
           let ζ := thick (R := Tri) z u in
           lmgu _ (Ty_hole xIn)[ζ] t[ζ]).

    Equations boxmgu : BoxUnifier w :=
    | Ty_hole xIn   | t            := boxflex xIn t;
    | s            | Ty_hole yIn   := boxflex yIn s;
    | Ty_bool       | Ty_bool       := fun _ _ => η Ty_bool;
    | Ty_func s1 s2 | Ty_func t1 t2 := fun _ ζ1 =>
                                       ⟨ ζ2 ⟩ r1 <- boxmgu s1 t1 ζ1 ;;
                                       ⟨ ζ3 ⟩ r2 <- boxmgu s2 t2 (ζ1 ⊙⁻ ζ2) ;;
                                       η (Ty_func (persist _ r1 _ ζ3) r2);
    | _            | _            := fun _ _ => None.

  End MguO.

  Definition mgu : ⊢ Unifier :=
    fun w s t => T (@Löb _ boxmgu w s t).

End Variant2.

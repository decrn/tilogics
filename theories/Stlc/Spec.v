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
  Strings.String.
From Equations Require Import
  Equations.
From stdpp Require Import
  gmap.

#[local] Set Implicit Arguments.
#[local] Set Transparent Obligations.

Reserved Notation "Γ |-- E ∷ T ~> EE"
  (at level 80).

(* =================================== *)
(*  The Simply-Typed Lambda Calculus   *)
(*      extended with Booleans         *)
(* =================================== *)

(* ===== Types ===== *)
Module ty.

  Inductive Ty : Type :=
  | bool
  | func (t1 t2 : Ty).

  Derive NoConfusion EqDec Subterm for Ty.

  Lemma no_cycle (t : Ty) : ~ Ty_subterm t t.
  Proof.
    induction (well_founded_Ty_subterm t) as [? _ IH].
    intros Hx. apply (IH _ Hx Hx).
  Qed.

End ty.
Export ty (Ty).
Export (hints) ty.

(* ===== Typing Environment ===== *)
Notation Env := (gmap string Ty).
Notation "Γ ,, x ∷ t":=
  (@insert string _
     _
     (@map_insert string _
        _
        (@gmap_partial_alter string strings.string_eq_dec strings.string_countable _))
     x t Γ)
    (at level 60, format "Γ  ,,  x ∷ t").

(* ===== Terms / Expressions ===== *)
Module exp.
  Inductive Exp : Type :=
  | var (x : string)
  | true
  | false
  | ifte (e1 e2 e3 : Exp)
  | absu (x : string) (e : Exp)
  | abst (x : string) (t : Ty) (e : Exp)
  | app (e1 e2 : Exp).

  Derive NoConfusion for Exp.

End exp.
Export exp (Exp).
Export (hints) exp.

(* ===== Typing relation ===== *)
Module tpb.
  Import exp ty.

  Inductive tpb (Γ : Env) : Exp -> Ty -> Exp -> Prop :=
  | var x t : Γ !! x = Some t ->
              Γ |-- var x ∷ t    ~> var x
  | true :    Γ |-- true  ∷ bool ~> true
  | false :   Γ |-- false ∷ bool ~> false

  | ifte t e1 e1' e2 e2' e3 e3' :
    Γ         |-- e1            ∷ bool    ~> e1' ->
    Γ         |-- e2            ∷ t       ~> e2' ->
    Γ         |-- e3            ∷ t       ~> e3' ->
    Γ         |-- ifte e1 e2 e3 ∷ t       ~> ifte e1' e2' e3'

  | tpb_absu x t1 t2 e e' :
    Γ ,, x∷t1 |-- e             ∷ t2         ~> e' ->
    Γ         |-- absu x e      ∷ func t1 t2 ~> abst x t1 e'
  | tpb_abst x t1 t2 e e' :
    Γ ,, x∷t1 |-- e             ∷ t2         ~> e' ->
    Γ         |-- abst x t1 e   ∷ func t1 t2 ~> abst x t1 e'
  | tpb_app e1 t1 e1' e2 t2 e2' :
    Γ         |-- e1            ∷ func t2 t1 ~> e1' ->
    Γ         |-- e2            ∷ t2         ~> e2' ->
    Γ         |-- app e1 e2     ∷ t1         ~> app e1' e2'

  where "Γ |-- e ∷ t ~> e'" := (tpb Γ e t e').

  (* (λx . x) : Bool → Bool  ... is well-typed *)
  Example id_bool_well_typed :
    let e  := exp.absu "x" (exp.var "x") in
    let t  := ty.func ty.bool ty.bool in
    let e' := exp.abst "x" ty.bool (exp.var "x") in
    ∅ |-- e ∷ t ~> e'.
  Proof. repeat constructor. Qed.

End tpb.
Export (notations) tpb.
Export tpb (tpb).




(* Inductive SolvedM (A : TYPE) (Σ : World) : Type := *)
(*   | Ret_Solved           : A Σ -> SolvedM A Σ *)
(*   | Fail_Solved          : SolvedM A Σ *)
(*   | Bind_Exists_Solved   : forall (i : nat), SolvedM A (Σ ▻ i) -> SolvedM A Σ. *)

(* #[export] Instance lk_alloc : Lk Alloc := *)
(*   fun w1 w2 r x xIn => Ty_hole _ x (persist _ xIn _ r). *)

(* #[export] Instance PersistLaws_Ty : PersistLaws Ty. *)
(* Proof. *)
(*   constructor. *)
(*   - induction V; cbn; f_equal; auto. *)
(*   - induction V; cbn; f_equal; auto. *)
(*     unfold lk, lk_alloc. f_equal. *)
(*     apply assoc_persist. *)
(* Qed. *)

(* #[export] Instance PersistLaws_Env : PersistLaws Env. *)
(* Proof. *)
(*   constructor. *)
(*   - induction V as [|[]]; cbn; f_equal; auto. *)
(*     f_equal. apply refl_persist. *)
(*   - induction V as [|[]]; cbn; f_equal; auto. *)
(*     f_equal. apply assoc_persist. *)
(* Qed. *)

(* #[export] Instance InstAlloc : forall w, Inst (Alloc w) (Assignment w) := *)
(*   fix installoc {w0 w1} (r : Alloc w0 w1) := *)
(*     match r with *)
(*     | alloc.refl _        => fun ι => ι *)
(*     | alloc.fresh _ α w r => fun ι => let (r',_) := env.view (inst (Inst := @installoc _) r ι) in r' *)
(*     end. *)




(* Class LkPreOrder {R} `{Lk R, Persistent R Ty, Refl R, Trans R} : Prop := *)
(*   { lk_refl {w x} (xIn : x ∈ w) : *)
(*       lk refl xIn = Ty_hole w x xIn; *)
(*     lk_trans {w1 w2 w3 x} (xIn : x ∈ w1) (ζ1 : R w1 w2) (ζ2 : R w2 w3) : *)
(*       lk (trans ζ1 ζ2) xIn = persist _ (lk ζ1 xIn) _ ζ2; *)
(*   }. *)
(* #[global] Arguments LkPreOrder R {_ _ _ _}. *)

(* Class PersistPreOrder {R A} `{Persistent R A, Refl R, Trans R} : Prop := *)
(*   { persist_refl {w} (a : A w) : *)
(*       persist _ a _ refl = a; *)
(*     persist_trans {w1} (a : A w1) {w2 w3} (ζ1 : R w1 w2) (ζ2 : R w2 w3) : *)
(*       persist _ a _ (trans ζ1 ζ2) = persist _ (persist _ a _ ζ1) _ ζ2; *)
(*   }. *)
(* #[global] Arguments PersistPreOrder R A {_ _ _}. *)


(* Section Thin. *)

(*   Fixpoint thin {w x} (xIn : x ∈ w) (T : Ty (w - x)) : Ty w := *)
(*     match T with *)
(*     | Ty_hole _ _ yIn => Ty_hole _ _ (ctx.in_thin xIn yIn) *)
(*     | Ty_bool _ => Ty_bool _ *)
(*     | Ty_func _ T1 T2 => Ty_func _ (thin xIn T1) (thin xIn T2) *)
(*     end. *)

(*   (* Definition fancy_thin : ⊢ ◁Ty -> Ty := *) *)
(*   (*   fun w '(x; (xIn; T)) => thin xIn T. *) *)

(* End Thin. *)

(* Section ShallowConstraints. *)
(*   Import World.notations. *)

(*   Inductive TyF (w : World) : Type := *)
(*   | TyF_bool       : TyF w *)
(*   | TyF_func {x y} : x ∈ w -> y ∈ w -> TyF w. *)
(*   #[global] Arguments TyF_bool {w}. *)
(*   #[global] Arguments TyF_func {w x y}. *)

(*   Definition inj : ⊢ʷ TyF -> Ty := *)
(*     fun w t => *)
(*       match t with *)
(*       | TyF_bool     => Ty_bool _ *)
(*       | TyF_func x y => Ty_func _ (Ty_hole _ _ x) (Ty_hole _ _ y) *)
(*       end. *)

(*   Variant ShallowConstraint (w : World) : Type := *)
(*     | FlexFlex {x y} (xIn : x ∈ w) (yIn : y ∈ w) *)
(*     | FlexRigid {x} (xIn : x ∈ w) (t : TyF w). *)

(* End ShallowConstraints. *)

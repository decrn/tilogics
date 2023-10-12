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
From Equations Require Import Equations.
From stdpp Require Import gmap.

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

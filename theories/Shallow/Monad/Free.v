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
  Classes.Morphisms_Prop
(*   Lists.List *)
  Program.Tactics
  Strings.String.
(* From Equations Require Import *)
(*   Equations. *)
From stdpp Require Import
  base gmap.
From Em Require Import
  Prelude
  Shallow.Monad.Interface
  Spec.

#[local] Set Implicit Arguments.

Inductive Free (A : Type) : Type :=
| Ret (a : A)
| Fail
| Equalsk (t1 t2 : Ty) (k : Free A)
| Pickk (f : Ty -> Free A).
#[global] Arguments Fail {A}.

#[export] Instance mret_free : MPure Free :=
  Ret.

#[export] Instance mbind_free : MBind Free :=
  fun A B =>
    fix bind (m : Free A) f : Free B :=
    match m with
    | Ret a           => f a
    | Fail            => Fail
    | Equalsk t1 t2 k => Equalsk t1 t2 (bind k f)
    | Pickk g       => Pickk (fun t => bind (g t) f)
    end.

#[export] Instance mfail_free : MFail Free :=
  fun A => Fail.

#[export] Instance tcm_free : TypeCheckM Free :=
  {| equals t1 t2 := Equalsk t1 t2 (pure tt);
    pick         := Pickk (@pure Free _ _);
  |}.

(* Eval vm_compute in *)
(*   let e := exp.app (exp.abst "x" ty.bool (exp.var "x")) exp.true *)
(*   in synth (M := Free) empty e. *)

(* Eval vm_compute in *)
(*   let e := exp.app (exp.absu "x" (exp.var "x")) exp.true *)
(*   in synth (M := Free) empty e. *)

(* Example K1 := exp.absu "k1" (exp.absu "l" (exp.var "k1")). *)
(* Example K2 := exp.absu "k2" (exp.absu "l" (exp.var "k2")). *)
(* Example I  := exp.absu "i" (exp.var "i"). *)

(* Example KKI := (exp.app K1 (exp.app K2 I)). *)
(* Eval vm_compute in *)
(*   synth (M := Free) empty KKI. *)

#[export] Instance wp_free : WeakestPre Free :=
  fix wp [A] (m : Free A) (Q: A -> Prop) : Prop :=
    match m with
    | Ret a           => Q a
    | Fail            => False
    | Equalsk t1 t2 k => t1 = t2 /\ wp k Q
    | Pickk f         => exists t, wp (f t) Q
    end.

#[export] Instance wlp_free : WeakestLiberalPre Free :=
  fix wlp [A] (m : Free A) (Q: A -> Prop) : Prop :=
    match m with
    | Ret a           => Q a
    | Fail            => True
    | Equalsk t1 t2 k => t1 = t2 -> wlp k Q
    | Pickk f         => forall t, wlp (f t) Q
    end.

#[export] Instance tcl_free: TypeCheckLogicM Free.
Proof.
  constructor; try (induction m; cbn; firstorder; fail); auto.
  - cbn. intros. exists τ. auto.
Qed.

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
  base gmap.
From Em Require Import
  Context
  Prelude
  Stlc.Alloc
  Stlc.Instantiation
  Stlc.Persistence
  Stlc.Predicates
  Stlc.Spec
  Stlc.Substitution
  Stlc.Symbolic.Free
  Stlc.Worlds.

Import World.notations.

Set Implicit Arguments.

Section Generate.
  Import MonadNotations.
  Import World.notations.

  #[local] Notation "s [ ζ ]" :=
    (persist s ζ)
      (at level 8, left associativity,
        format "s [ ζ ]").

  Definition generate : Exp -> ⊢ʷ Ėnv -> Free Ṫy :=
    fix gen e {w} Γ :=
      match e with
      | exp.var x =>
          match lookup x Γ with
          | Some t => Ret t
          | None   => Fail
          end
      | exp.true => Ret ṫy.bool
      | exp.false => Ret ṫy.bool
      | exp.ifte e1 e2 e3 =>
          [ θ1 ] t1 <- gen e1 Γ ;;
          [ θ2 ] _  <- assert ṫy.bool t1 ;;
          [ θ3 ] t2 <- gen e2 (Γ[θ1 ⊙ θ2]) ;;
          [ θ4 ] t3 <- gen e3 Γ[θ1 ⊙ θ2 ⊙ θ3] ;;
          [ θ5 ] _  <- assert t2[θ4] t3 ;;
          Ret t3[θ5]
      | exp.absu x e =>
          [ θ1 ] t1 <- choose ;;
          [ θ2 ] t2 <- gen e (Γ[θ1] ,, x∷t1) ;;
          Ret (ṫy.func t1[θ2] t2)
      | exp.abst x t1 e =>
          let t1 := lift t1 w in
          [ θ1 ] t2 <- gen e (Γ ,, x∷t1) ;;
          Ret (ṫy.func t1[θ1] t2)
      | exp.app e1 e2 =>
          [ θ1 ] tf <- gen e1 Γ ;;
          [ θ2 ] t2 <- gen e2 Γ[θ1] ;;
          [ θ3 ] t1 <- choose ;;
          [ θ4 ] _  <- assert tf[θ2⊙θ3] (ṫy.func t1 t2[θ3]) ;;
          Ret t2[θ3 ⊙ θ4]
      end.

End Generate.

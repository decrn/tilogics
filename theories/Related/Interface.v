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

Require Import Coq.Classes.RelationClasses.
From iris Require Import proofmode.tactics.
From Em Require Import BaseLogic Prefix Spec.
From Em Require Monad.Interface Shallow.Interface.

Module S := Shallow.Interface.
Module D := Monad.Interface.

Import Pred Pred.notations Pred.Sub Pred.proofmode world.notations.

#[local] Set Implicit Arguments.

Definition Rel (DA : OType) (SA : Type) : Type :=
  forall (w : World) , DA w -> SA -> Pred w.

Definition RTy : Rel OTy Ty :=
  fun w (T : OTy w) (t : Ty) (ass : Assignment w) =>
    inst T ass = t.

(* For functions/impl: related inputs go to related outputs *)
Definition RArr {DA SA DB SB} (RA : Rel DA SA) (RB : Rel DB SB) : Rel (DA ⇢ DB) (SA -> SB) :=
  fun w df sf ass => forall (da : DA w) (sa : SA)
                            (ra : RA w da sa ass),
      RB w (df da) (sf sa) ass.

Definition RBox {DA SA} (RA : Rel DA SA) : Rel (Box Prefix DA) SA :=
  fun (w : World) (bda : (◻⁺DA)%W w) (sa : SA) =>
         PBox (λ (w' : World) (θ : w ⊑⁺ w'), RA w' (bda w' θ) sa).

Definition RPred : Rel Pred Prop.
unfold Rel, Pred. intros w DP SP ass. refine (DP ass <-> SP). Defined.

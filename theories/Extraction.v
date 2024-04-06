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

From Coq Require Import ExtrHaskellBasic ExtrHaskellNatInt ExtrHaskellString Bool.
From Em Require Import Composition.

Extraction Language Haskell.
Extraction Inline Bool.Bool.iff_reflect Environment.env.view
  Init.Datatypes.nat_rec Init.Logic.False_rec Init.Logic.and_rec
  Init.Logic.and_rect Init.Logic.eq_rec_r Init.Specif.sumbool_rec
  Init.Specif.sumbool_rect Unification.atrav Unification.flex
  UnificationGeneric.loeb UnificationGeneric.remove_acc_rect Unification.varview
  Worlds.Box Worlds.Impl Worlds.Impl Worlds.Valid Worlds.lk Worlds._4
  Worlds.world.view stdpp.base.empty stdpp.base.insert stdpp.base.fmap
  stdpp.base.decide_rel stdpp.gmap.gmap_fmap stdpp.option.option_fmap.

Extract Inductive reflect => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inlined Constant Init.Datatypes.fst => "Prelude.fst".
Extract Inlined Constant Init.Datatypes.snd => "Prelude.snd".
Extraction "Extract" ground_type ground_expr infer.

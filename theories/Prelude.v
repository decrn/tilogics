(******************************************************************************)
(* Copyright (c) 2020 Steven Keuchel, Dominique Devriese                      *)
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

From stdpp Require Export base.

Module option.

  Definition map {A B} (f : A → B) (o : option A) : option B :=
    match o with Some a => Some (f a) | None => None end.
  Definition bind {A B} (a : option A) (f : A → option B) : option B :=
    match a with Some x => f x | None => None end.
  (* Not lazy in (a : option A). *)
  Definition ap {A B} (f : option (A → B)) (a : option A) : option B :=
    match f with Some f => map f a | None => None end.

  Module Import notations.

    Notation "' x <- ma ;; mb" :=
      (bind ma (fun x => mb))
        (at level 80, x pattern, ma at next level, mb at level 200, right associativity,
          format "' x  <-  ma  ;;  mb").
    Notation "x <- ma ;; mb" :=
      (bind ma (fun x => mb))
        (at level 80, ma at next level, mb at level 200, right associativity).
    Notation "f <$> a" := (map f a) (at level 61, left associativity).
    Notation "f <*> a" := (ap f a) (at level 61, left associativity).

  End notations.

End option.

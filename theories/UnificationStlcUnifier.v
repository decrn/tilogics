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

Definition atrav : AUnifier w :=
  fix atrav s t {struct s} :=
    match s , t with
    | @oty.evar _ α _  , t               => aflex α t
    | s                , @oty.evar _ β _ => aflex β s
    | oty.bool         , oty.bool        => ctrue
    | oty.func s1 s2   , oty.func t1 t2  => cand (atrav s1 t1) (atrav s2 t2)
    | _                , _               => cfalse
    end.

Section atrav_elim.

  Context (P : OTy w → OTy w → C w → Type).
  Context (fflex1 : ∀ α (αIn : α ∈ w) (t : OTy w), P (oty.evar αIn) t (aflex α t)).
  Context (fflex2 : ∀ α (αIn : α ∈ w) (t : OTy w), P t (oty.evar αIn) (aflex α t)).
  Context (fbool : P oty.bool oty.bool ctrue).
  Context (fbool_func : ∀ T1 T2 : OTy w, P oty.bool (oty.func T1 T2) cfalse).
  Context (ffunc_bool : ∀ T1 T2 : OTy w, P (oty.func T1 T2) oty.bool cfalse).
  Context (ffunc : ∀ s1 s2 t1 t2 : OTy w,
    (P s1 t1 (atrav s1 t1)) →
    (P s2 t2 (atrav s2 t2)) →
    P (oty.func s1 s2) (oty.func t1 t2)
      (cand (atrav s1 t1) (atrav s2 t2))).

  Lemma atrav_elim : ∀ (t1 t2 : OTy w), P t1 t2 (atrav t1 t2).
  Proof. induction t1; intros t2; cbn; auto; destruct t2; auto. Qed.

End atrav_elim.

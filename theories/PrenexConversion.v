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

From Em Require Export Monad.Free Monad.Prenex.
Import option.notations Pred Pred.Acc Pred.notations.

#[local] Set Implicit Arguments.

Definition prenex {A} : ⊧ Free A ⇢ Prenex A :=
  fix pr {w} m {struct m} :=
    match m with
    | Free.Ret a => pure a
    | Free.Fail => None
    | Free.Equalsk t1 t2 m =>
        '(existT w1 (r1, (cs, a))) <- pr m;;
        let t1' := persist t1 r1 in
        let t2' := persist t2 r1 in
        let c   := (t1', t2') in
        Some (existT w1 (r1, (cons c cs, a)))
    | Free.Pickk α m =>
        '(existT w1 (r1, csa)) <- pr m ;;
        Some (existT w1 (step ⊙ r1, csa))
    end.

Lemma prenex_correct {A w} (m : Free A w) (Q : Box Prefix (A ⇢ Pred) w) :
  WP (prenex m) Q ⊣⊢ₚ WP m Q.
Proof.
  induction m; predsimpl.
  - rewrite <- IHm. clear IHm.
    destruct (prenex m) as [(w1 & θ1 & C1 & a1)|]; predsimpl.
    rewrite Acc.and_wp_r. apply Acc.proper_wp_bientails. predsimpl.
    now rewrite and_assoc.
  - rewrite <- IHm. clear IHm.
    destruct (prenex m) as [(w1 & θ1 & C1 & a1)|]; predsimpl.
Qed.

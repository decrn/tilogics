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


Definition occurs_check : ⊧ OTy ↠ ▹(Option OTy) :=
  fun w =>
    fix oc (t : OTy w) β (βIn : β ∈ w) {struct t} :=
    match t with
    | oty.evar αIn   => oty.evar <$> occurs_check_in αIn βIn
    | oty.bool       => Some oty.bool
    | oty.func t1 t2 => oty.func <$> oc t1 β βIn <*> oc t2 β βIn
    end.

Lemma occurs_check_spec {w α} (αIn : α ∈ w) (t : OTy w) :
  match occurs_check t αIn with
  | Some t' => t = t'[thin α]
  | None => t = oty.evar αIn \/ oty.OTy_subterm (oty.evar αIn) t
  end.
Proof.
  induction t; cbn.
  - unfold occurs_check_in. destruct world.occurs_check_view; cbn.
    + now left.
    + now rewrite lk_thin.
  - reflexivity.
  - destruct (occurs_check t1 αIn), (occurs_check t2 αIn);
      cbn; subst; auto; right;
      match goal with
      | H: _ \/ oty.OTy_subterm _ ?t |- _ =>
          destruct H;
          [ subst; constructor; constructor
          | constructor 2 with t; auto; constructor; constructor
          ]
      end.
Qed.

Inductive VarView {w} : OTy w → Type :=
| is_var {x} (xIn : x ∈ w) : VarView (oty.evar xIn)
| not_var {t} (H: ∀ x (xIn : x ∈ w), t <> oty.evar xIn) : VarView t.
#[global] Arguments not_var {w t} &.

Definition varview {w} (t : OTy w) : VarView t :=
  match t with
  | oty.evar xIn => is_var xIn
  | _            => not_var (fun _ _ e => noConfusion_inv e)
  end.

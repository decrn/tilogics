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
  Classes.Morphisms
(*   Program.Basics *)
  Relations.Relation_Definitions.
From Em Require Import
  Context
  Environment
  Stlc.Persistence
  Stlc.Spec
  Stlc.Worlds.

Import ctx.notations.
Import World.notations.

#[local] Set Implicit Arguments.

(* #[local] Open Scope indexed_scope. *)

Reserved Notation "w1 ⊒⁻ w2" (at level 80).

Definition Later (A : TYPE) : TYPE :=
  fun w => forall x (xIn : x ∈ w), A (w - x).
Definition LaterTm (A : TYPE) : TYPE :=
  fun w => forall x (xIn : x ∈ w), Ṫy (w - x) -> A (w - x).

Definition Sooner (A : TYPE) : TYPE :=
  fun w => sigT (fun x => sigT (fun (xIn : x ∈ w) => A (w - x))).
Definition SoonerTm (A : TYPE) : TYPE :=
  fun w => sigT (fun x => sigT (fun (xIn : x ∈ w) => Ṫy (w - x) * A (w - x)))%type.

(* Module Sng. *)

(*   Inductive Sng (w : World) : World -> Set := *)
(*   | sng {x} (xIn : x ∈ w) (t : Ṫy (w - x)) : Sng w (w - x). *)

(*   #[export] Instance lk_sng : Lk Sng := *)
(*     fun w0 w1 r => match r with sng xIn t => thickIn xIn t end. *)

(* End Sng. *)

Module Tri.

  (* #[local] Unset Elimination Schemes. *)

  Inductive Raw (w : World) : World -> Set :=
  | refl      : Raw w w
  | cons {w' x} (xIn : x ∈ w) (t : Ṫy (w - x)) (ζ : Raw (w - x) w') : Raw w w'.
  #[global] Arguments refl {_}.
  #[global] Arguments cons {_ _} x {_} t ζ.

  Section InnerRecursion.

    Context [w w' : World] (rec : forall y (yIn : y ∈ w), Ṫy w').

    Fixpoint persist_inner (t : Ṫy w) : Ṫy w' :=
      match t with
      | ṫy.var xIn    => rec xIn
      | ṫy.bool       => ṫy.bool
      | ṫy.func t1 t2 => ṫy.func (persist_inner t1) (persist_inner t2)
      end.

  End InnerRecursion.

  #[export] Instance proper_persist_inner {w0 w1} :
    Proper (forall_relation (fun y => pointwise_relation (y ∈ w0) eq) ==> pointwise_relation _ eq) (@persist_inner w0 w1).
  Proof. intros r1 r2 Hr t; induction t; cbn; now f_equal; auto. Qed.

  Fixpoint persist_outer {w0} t {w1} (r : Raw w0 w1) {struct r} : Ṫy w1 :=
    match r with
    | refl       => t
    | cons α s r => persist_inner
                      (fun b βIn => persist_outer (thickIn _ s βIn) r)
                      t
    end.

  Canonical Structure Tri : ACC :=
    {| acc              := Raw;
       lk w1 w2 θ α αIn := persist_outer (ṫy.var αIn) θ;
    |}.
  Notation "w1 ⊒⁻ w2" := (acc Tri w1 w2).

  #[export] Instance thick_tri : Thick Tri :=
    fun w x xIn t => cons x t refl.
  #[export] Instance refl_tri : Refl Tri :=
    fun w => refl.
  #[export] Instance trans_tri : Trans Tri :=
    fix trans [w0 w1 w2] (ζ1 : w0 ⊒⁻ w1) {struct ζ1} : w1 ⊒⁻ w2 -> w0 ⊒⁻ w2 :=
      match ζ1 with
      | refl        => fun ζ2 => ζ2
      | cons x t ζ1 => fun ζ2 => cons x t (trans ζ1 ζ2)
      end.

  (* Definition Raw_case [w] (P : forall w', w ⊒⁻ w' -> Type) *)
  (*   (p_refl : P w Worlds.refl) *)
  (*   (p_cons : forall w' x (xIn : x ∈ w) t r, P w' (thick x t ⊙ r)) *)
  (*   {w'} (r : w ⊒⁻ w') : P w' r := *)
  (*   match r with *)
  (*   | refl       => p_refl *)
  (*   | cons x t r => p_cons _ x _ t r *)
  (*   end. *)

  (* Definition Raw_rect (P : forall w w', Tri w w' -> Type) *)
  (*   (p_refl : forall w : World, P w w Worlds.refl) *)
  (*   (p_cons : forall w w' x (xIn : x ∈ w) t r, *)
  (*       P (w - x) w' r -> P w w' (thick x t ⊙ r)) : *)
  (*   forall w w' (r : w ⊒⁻ w'), P w w' r := *)
  (*   fix rect w w' (r : w ⊒⁻ w') {struct r} : P w w' r := *)
  (*     Raw_case (P w) (p_refl w) *)
  (*       (fun _ x _ t r' => *)
  (*          p_cons _ _ x _ t r' (rect _ _ r')) r. *)
  (* Definition Raw_ind (P : forall w w', Tri w w' -> Prop) := Raw_rect P. *)
  (* Definition Raw_rec (P : forall w w', Tri w w' -> Set) := Raw_rect P. *)

  (* Definition Raw_sind (P : forall w w' : World, Raw w w' -> Type) *)
  (*   (p_refl : forall w : World, P w w Worlds.refl) *)
  (*   (p_cons : forall w w' x (xIn : x ∈ w) t r, *)
  (*       P (w - x) w' r -> P w w' (thick x t ⊙ r)) := *)
  (*   fix sind {w w'} (r : w ⊒⁻ w') {struct r} : P w w' r := *)
  (*     match r with *)
  (*     | refl => p_refl w *)
  (*     | cons x t r => p_cons _ _ x _ t r (sind r) *)
  (*     end. *)

  (* Inductive onsubterms (P : forall w w', Raw w w' -> Type) {w} : *)
  (*   forall w', w ⊒⁻ w' -> Type := *)
  (* | on_refl : onsubterms P refl *)
  (* | on_cons {x} (xIn : x ∈ w) (t : Ṫy (w - x)) {w'} (r : Tri (w - x) w') : *)
  (*   P (w - x) w' r -> onsubterms P (cons x t r). *)
  (* Arguments on_refl {P w}. *)
  (* Arguments on_cons {P w} x {xIn} t {w' r} _. *)

  (* Definition Tri_löb (P : forall w w', Raw w w' -> Type) *)
  (*   (step : forall w w' r, onsubterms P r -> P w w' r) : *)
  (*   forall w w' r, P w w' r := *)
  (*   fix löb w w' (r : w ⊒⁻ w') {struct r} : P w w' r := *)
  (*     Raw_case (P w) (step w w Worlds.refl on_refl) *)
  (*       (fun w' x xIn t r => step w w' (thick x t ⊙ r) (on_cons x t (löb (w - x) w' r))) r. *)

  Module Import notations.
    Notation "▷ A" := (Later A) (at level 9, right associativity).
    Notation "▶ A" := (LaterTm A) (at level 9, right associativity).
    Notation "◁ A" := (Sooner A) (at level 9, right associativity).
    Notation "◀ A" := (SoonerTm A) (at level 9, right associativity).
    Notation "□⁻ A" := (Box Tri A) (at level 9, format "□⁻ A", right associativity).
  End notations.

  Definition box_intro_split {A} :
    ⊢ʷ A -> ▶□⁻A -> □⁻A :=
    fun w0 a la w1 ζ =>
      match ζ with
      | Tri.refl => a
      | Tri.cons x t ζ' => la x _ t _ ζ'
      end.

  (* Arguments Raw_ind (P p_refl p_cons)%function_scope (w w')%ctx_scope r. *)
  (* Check @Raw_ind. *)
  #[export] Instance refltrans_tri : ReflTrans Tri.
  Proof.
    constructor.
    - easy.
    - induction r; cbn; [|rewrite IHr]; easy.
    - induction r1; cbn; congruence.
  Qed.

  (* #[export] Instance InstTri : forall w, Inst (Tri w) (Assignment w) := *)
  (*   fix insttri {w0 w1} (r : Tri w0 w1) := *)
  (*     match r with *)
  (*     | Tri.refl => fun ι => ι *)
  (*     | @Tri.cons _ w' x xIn t r => *)
  (*         fun ι => *)
  (*           let ι' := inst (Inst := @insttri _) r ι in *)
  (*           env.insert xIn ι' (inst t ι') *)
  (*     end. *)

  (* #[export] Instance instrefl_tri : InstRefl Tri := *)
  (*   fun _ _ => eq_refl. *)

  (* Definition geq {w0 w1} (ζ1 : w0 ⊒⁻ w1) [w2] (ζ2 : w0 ⊒⁻ w2) : Prop := *)
  (*   exists ζ12 : w1 ⊒⁻ w2, ζ2 = ζ1 ⊙ ζ12. *)
  (* Notation "ζ1 ≽ ζ2" := (geq ζ1 ζ2) (at level 80). *)

  (* Lemma geq_refl {w1 w2} (ζ : w1 ⊒⁻ w2) : ζ ≽ ζ. *)
  (* Proof. exists refl. symmetry. apply trans_refl. Qed. *)

  (* Lemma geq_trans {w0 w1 w2 w3} (ζ1 : w0 ⊒⁻ w1) (ζ2 : w0 ⊒⁻ w2) (ζ3 : w0 ⊒⁻ w3) : *)
  (*   ζ1 ≽ ζ2 -> ζ2 ≽ ζ3 -> ζ1 ≽ ζ3. *)
  (* Proof. *)
  (*   intros [ζ12 H12] [ζ23 H23]. exists (ζ12 ⊙ ζ23). *)
  (*   rewrite H23, H12. apply trans_assoc. *)
  (* Qed. *)

  (* Lemma geq_precom {w0 w1 w2 w3} (ζ1 : w0 ⊒⁻ w1) (ζ2 : w1 ⊒⁻ w2) (ζ3 : w1 ⊒⁻ w3) : *)
  (*   ζ2 ≽ ζ3 -> ζ1 ⊙ ζ2 ≽ ζ1 ⊙ ζ3. *)
  (* Proof. intros [ζ23 ->]. exists ζ23. symmetry. apply trans_assoc. Qed. *)

  (* Lemma geq_max {w1 w2} (ζ : w1 ⊒⁻ w2) : refl ≽ ζ. *)
  (* Proof. exists ζ. reflexivity. Qed. *)

  (* Lemma geq_extend {w0 w1 w2} (ζ1 : w0 ⊒⁻ w1) (ζ2 : w1 ⊒⁻ w2) : ζ1 ≽ ζ1 ⊙ ζ2. *)
  (* Proof. now exists ζ2. Qed. *)

  (* Definition geqb1 [w0 z] (zIn : z ∈ w0) (tz : Ṫy (w0 - z)) [w1] (ζ : w0 ⊒⁻ w1) : *)
  (*   option (w0 - z ⊒⁻ w1). *)
  (* Proof. *)
  (*   rename w1 into wend. *)
  (*   induction ζ. *)
  (*   + apply None. *)
  (*   + rename w' into wend. rename t into tx. *)
  (*     destruct (occurs_check_view xIn zIn). *)
  (*     * refine (if Ty_eqdec tx tz then Some ζ else None). *)
  (*     * rename y into z. rename yIn into zIn. *)
  (*       specialize (IHζ zIn). *)
  (*       Check (thick (thin _ tz) _ tx). *)
  (* Admitted. *)

  (* Fixpoint geqb (w0 w1 : World) (ζ1 : w0 ⊒⁻ w1) {w2} (ζ2 : w0 ⊒⁻ w2) {struct ζ1} : *)
  (*   option (w1 ⊒⁻ w2) := *)
  (*   match ζ1 with *)
  (*   | refl => Some ζ2 *)
  (*   | cons x t__X ζ1' => *)
  (*       option.bind (geqb1 _ t__X ζ2) (geqb ζ1') *)
  (*   end. *)

  (* Lemma geqb_spec {w0 w1} (ζ1 : w0 ⊒⁻ w1) : *)
  (*   forall [w2] (ζ2 : w0 ⊒ˢ w2), *)
  (*     Bool.reflect (triangular ζ1 ≽ ζ2) (ζ1 ≽? ζ2). *)
  (* Proof. *)
  (*   induction ζ1; cbn [geqb triangular]; intros w2 ζ2. *)
  (*   - constructor. apply geq_max. *)
  (*   - destruct Ty_eqdec. *)
  (*     + destruct (IHζ1 _ (thin xIn ⊙ˢ ζ2)); constructor; clear IHζ1. *)
  (*       * destruct g as [ζ2']. exists ζ2'. *)
  (*         rewrite comp_assoc. rewrite <- H. clear - e. *)
  (*         apply env.lookup_extensional. *)
  (*         intros y yIn. *)
  (*         rewrite lookup_comp. *)
  (*         rewrite lookup_thick. unfold thickIn. *)
  (*         destruct (occurs_check_view xIn yIn). apply e. *)
  (*         cbn. rewrite lookup_comp. unfold thin. *)
  (*         now rewrite env.lookup_tabulate. *)
  (*       * intros [ζ2' ->]. apply n. clear n. exists ζ2'. *)
  (*         rewrite <- ?comp_assoc. *)
  (*         rewrite comp_thin_thick. *)
  (*         rewrite comp_id_left. *)
  (*         reflexivity. *)
  (*     + constructor. intros [ζ2' ->]. apply n. clear n. *)
  (*       rewrite <- ?comp_assoc. *)
  (*       rewrite comp_thin_thick. *)
  (*       rewrite comp_id_left. *)
  (*       cbn. rewrite ?lookup_comp, lookup_thick. *)
  (*       unfold thickIn. rewrite occurs_check_view_refl. *)
  (*       now rewrite subst_comp. *)
  (* Qed. *)


  #[export] Instance lkrefl_tri : LkRefl Tri.
  Proof. intros w α αIn. reflexivity. Qed.

  Lemma persist_outer_fix {w0 w1} (θ : Tri w0 w1) (t : Ṫy w0) :
     persist_outer t θ =
     match t with
     | ṫy.var αIn    => lk θ αIn
     | ṫy.bool       => ṫy.bool
     | ṫy.func t1 t2 => ṫy.func (persist_outer t1 θ) (persist_outer t2 θ)
     end.
  Proof. induction θ; destruct t; cbn; auto. Qed.

  Lemma persist_outer_refl {w} (t : Ṫy w) : persist_outer t Worlds.refl = t.
  Proof. reflexivity. Qed.

  Lemma persist_persist_inner {w0 w1} (t : Ṫy w0) (rec : forall y (yIn : y ∈ w0), Ṫy w1) {w2} (r : Tri w1 w2) :
    persist (persist_inner rec t) r = persist_inner (fun y yIn => persist (rec y yIn) r) t.
  Proof. induction t; cbn; f_equal; auto. Qed.

  Lemma persist_outer_persist_inner {w0 w1} (t : Ṫy w0) (rec : forall y (yIn : y ∈ w0), Ṫy w1) {w2} (r : Tri w1 w2) :
    persist_outer (persist_inner rec t) r = persist_inner (fun y yIn => persist_outer (rec y yIn) r) t.
  Proof.
    induction t; cbn; auto; rewrite persist_outer_fix at 1; f_equal; auto.
  Qed.

  Lemma persist_outer_trans {w0} (t : Ṫy w0) {w1 w2} (θ1 : Tri w0 w1) (θ2 : Tri w1 w2) :
    persist_outer t (θ1 ⊙ θ2) = persist_outer (persist_outer t θ1) θ2.
  Proof.
    induction θ1; cbn.
    - reflexivity.
    - rewrite persist_outer_persist_inner.
      now apply proper_persist_inner.
  Qed.

  Lemma persist_outer_persist {w0 w1} (θ : w0 ⊒⁻ w1) (t : Ṫy w0) :
    persist_outer t θ = persist t θ.
  Proof. induction t; cbn; rewrite persist_outer_fix; f_equal; auto. Qed.

  #[export] Instance lktrans_tri : LkTrans Tri.
  Proof.
    intros w0 w1 w2 θ1 θ2 α αIn. unfold lk; cbn.
    generalize (ṫy.var αIn). clear. intros t.
    now rewrite persist_outer_trans, persist_outer_persist.
  Qed.

  (* Corollary persist_bool {w0 w1} (r : Tri w0 w1) : *)
  (*   persist _ Ty_bool _ r = Ty_bool. *)
  (* Proof. apply (persist_fix r). Qed. *)

  (* Corollary persist_func {w0 w1} (r : Tri w0 w1) (t1 t2 : Ṫy w0) : *)
  (*   persist _ (Ty_func t1 t2) _ r = Ty_func (persist _ t1 _ r) (persist _ t2 _ r). *)
  (* Proof. apply (persist_fix r). Qed. *)


  (* #[export] Instance persist_preorder_tri : PersistPreOrder Tri Ty. *)
  (* Proof. *)
  (*   constructor. *)
  (*   - reflexivity. *)
  (*   - intros w0 t w1 w2 ζ1 ζ2. *)
  (*     induction ζ1; cbn; intros *. *)
  (*     + reflexivity. *)
  (*     + rewrite persist_persist_inner. *)
  (*       now apply proper_persist_inner. *)
  (* Qed. *)

  (* #[export] Instance inst_thick : InstThick Tri. *)
  (* Proof. easy. Qed. *)

End Tri.
Export Tri (Tri).
Notation "w1 ⊒⁻ w2" := (Tri w1 w2) (at level 80).
Infix "⊙⁻" := (trans (Θ := Tri)) (at level 60, right associativity).

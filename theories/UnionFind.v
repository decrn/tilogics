(******************************************************************************)
(* Copyright (c) 2023 Steven Keuchel                                          *)
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
  Arith.PeanoNat
  Classes.Morphisms
  Relations.Relation_Definitions
  Relations.Relation_Operators
  Wellfounded.Transitive_Closure
  Wellfounded.Wellfounded.
From Equations Require Import
  Equations.
From iris Require
  bi.interface.

From Em Require Import
  Environment
  Context
  Prelude
  Stlc.Instantiation
  Stlc.Persistence
  Stlc.Predicates
  Stlc.Spec
  Stlc.Triangular
  Stlc.Worlds.

Import ctx.notations.
Import World.notations.

Set Implicit Arguments.

#[local] Open Scope indexed_scope.

Ltac folddefs :=
  repeat
    match goal with
    | H: context[@Tri.refl ?w] |- _ =>
        change_no_check (@Tri.refl w) with (@refl Tri _ w) in H
    | |- context[@Tri.refl ?w] =>
        change_no_check (@Tri.refl w) with (@refl Tri _ w)
    | |- context[Tri.cons ?x ?t ?r] =>
        change_no_check (Tri.cons x t r) with (thick x t ⊙⁻ r)
    end.

Definition Ref : TYPE :=
  fun w => { x & x ∈ w }.

Module DS.

  (* #[export] Instance persistent_ref : Persistent Ref. *)
  (* Proof. *)
  (*   intros Θ w0 [x xIn] w1 r. *)
  (*   refine (existT x (persist _ xIn _ r)). *)
  (* Defined. *)

  Set Equations With UIP.

  (* Lemma persist_ref_step_inj {w b} (r1 r2 : Ref w) : *)
  (*   persist w r1 (w ▻ b) step = persist w r2 (w ▻ b) step -> *)
  (*   r1 = r2. *)
  (* Proof. *)
  (*   destruct r1 as [x xIn], r2 as [y yIn]. cbv. *)
  (*   refine (ctx.rec_succ_inj (x;xIn) (y;yIn)). *)
  (* Qed. *)

  Definition IsRepr {w} (fnd : Ref w -> Ref w) (x : Ref w) : Prop :=
    fnd x = x.

  Lemma proof_irrelevance_isrepr {w} (fnd : Ref w -> Ref w) (x : Ref w) :
    forall p q : IsRepr fnd x, p = q.
  Proof. intros p q. apply uip. Qed.

  Definition FindWf {w} (fnd : Ref w -> Ref w) : Prop :=
    forall x, IsRepr fnd (fnd x).

  Record DS (A : TYPE) (w : World) : Type :=
    { find    : Ref w -> Ref w;
      find_wf : FindWf find;

      cont    : forall x, IsRepr find x -> A w;

      get (x : Ref w)     : A w := cont (find_wf x);
      equiv (x y : Ref w) : bool  :=
        if eq_dec (find x) (find y)
        then true else false;
    }.
  #[global] Arguments cont [A]%indexed_scope [w]%ctx_scope d x _.

  Definition set {A} : ⊢ʷ DS A -> Ref -> A -> DS A :=
    fun w d x a =>
      {| find      := find d;
         find_wf   := find_wf d;
         cont r rr := if equiv d r x then a else cont d r rr;
      |}.

  Definition mergeFind :
    ⊢ʷ (Ref -> Ref) -> Ref -> Ref -> Ref -> Ref :=
    fun w fnd rx ry z =>
      (* Replace every mention of y's representative by x's representative. *)
      if eq_dec ry (fnd z) then rx else fnd z.

  Lemma mergeFind_wf {w} (fnd : Ref w -> Ref w) (rx ry : Ref w) :
    FindWf fnd ->
    IsRepr fnd rx ->
    IsRepr fnd ry -> (* Unused *)
    FindWf (mergeFind fnd rx ry).
  Proof.
    unfold FindWf, mergeFind, IsRepr. intros fnd_wf rx_wf _ z.
    destruct (eq_dec ry (fnd z)); destruct eq_dec; try congruence.
  Qed.

  Lemma mergeFind_wf_inverse {w} (fnd : Ref w -> Ref w) (rx ry : Ref w) :
    forall z, rx <> z -> IsRepr (mergeFind fnd rx ry) z -> IsRepr fnd z.
  Proof.
    unfold FindWf, mergeFind, IsRepr. intros z neq e.
    destruct (eq_dec ry (fnd z)). destruct (neq e). auto.
  Defined.

  Definition mergeCont {A w} (fnd : Ref w -> Ref w)
    (cnt : forall r, IsRepr fnd r -> A w) (rx ry : Ref w) (a : A w) :
    forall z, IsRepr (mergeFind fnd rx ry) z -> A w :=
    fun z z_wf =>
      match eq_dec rx z with
      | left _  => a
      | right n => cnt z (mergeFind_wf_inverse n z_wf)
      end.
  #[global] Arguments mergeCont {A w} fnd cnt rx ry a [z] _.

  (* Variant MergeResult (A B : TYPE) (w : World) : Type := *)
  (* | merge_none *)
  (* | merge_fail *)
  (* | merge_done (d : DS A w) (b : B w). *)

  (* Definition merge {A B} : *)
  (*   ⊢ʷ (A -> A -> Option (Prod A B)) -> DS A -> Ref -> Ref -> MergeResult A B := *)
  (*   fun w f d x y => *)
  (*     let rx := find d x in *)
  (*     let ry := find d y in *)
  (*     if eq_dec rx ry then merge_none A B w *)
  (*     else *)
  (*       let rx_wf := find_wf d x in *)
  (*       let ry_wf := find_wf d y in *)
  (*       match f (cont d rx rx_wf) (cont d ry ry_wf) with *)
  (*       | Some (a,b) => *)
  (*           merge_done _ *)
  (*             {| find    := mergeFind (find d) rx ry; *)
  (*                find_wf := mergeFind_wf (find_wf d) rx_wf ry_wf; *)
  (*                cont    := @mergeCont A w (find d) (cont d) rx ry a; *)
  (*             |} *)
  (*             b *)
  (*       | None => merge_fail A B w *)
  (*       end. *)

  Definition Space : TYPE := env.Env (fun _ => bool).
  Definition measure : ⊢ʷ (Ref -> Ref) -> Space.
  Proof.
    intros w fnd.
    apply env.tabulate. intros x xIn.
    refine (if eq_dec (fnd (existT x xIn)) (existT x xIn) then true else false).
  Defined.

  Fixpoint lessthan {w} : relation (Space w) :=
    match w with
    | ctx.nil      => fun _ _ => False
    | ctx.snoc w b =>
        fun f g =>
          symprod (Space w) bool lessthan Bool.lt
            (env.tail f, env.head f) (env.tail g, env.head g)
    end.

  Lemma wf_bool_lt : well_founded Bool.lt.
  Proof.
    intros b.
    constructor; intros []; cbn; [intros []|intros ->].
    constructor; intros [] ?; [contradiction|discriminate].
  Qed.

  #[export] Instance lessthan_wellfounded {w} : WellFounded (lessthan (w:=w)).
  Proof.
    unfold WellFounded. induction w; cbn.
    - hnf. intros f. constructor. intros g. intros [].
    - auto using wf_inverse_image, wf_symprod, wf_bool_lt.
  Qed.

  Definition removeRepr {w} (m : Space w) (y : Ref w) : Space w :=
    env.update m (projT2 y) false.

  Lemma lessthan_removeRepr {w} (m : Space w) (x : Ref w) :
    env.lookup m (projT2 x) = true ->
    lessthan (removeRepr m x) m.
  Proof.
    unfold removeRepr. destruct x as [x xIn]; cbn.
    induction m; cbn; intros H.
    - destruct (ctx.view xIn).
    - destruct (ctx.view xIn) as [|x xIn]; cbn.
      + now constructor 2.
      + now constructor 1; apply IHm.
  Qed.

  Lemma measure_mergeFind {w} (fnd : Ref w -> Ref w) (rx ry : Ref w)
    (rx_wf : IsRepr fnd rx)
    (ry_wf : IsRepr fnd ry)
    (H : rx <> ry) :
    measure (mergeFind fnd rx ry) = removeRepr (measure fnd) ry.
  Proof.
    apply env.lookup_extensional. intros z zIn.
    unfold measure, mergeFind, removeRepr.
    rewrite ?env.lookup_tabulate.
    rewrite env.lookup_update.
    rewrite env.lookup_tabulate.
    destruct (eq_dec ry (fnd (existT z zIn))).
    - destruct (eq_dec (existT (projT1 ry) (projT2 ry)) (existT z zIn)).
      rewrite rew_const.
      + destruct (eq_dec rx (existT z zIn)). congruence. easy.
      + rewrite <- sigT_eta in n.
        destruct (eq_dec rx (existT z zIn)).
        exfalso. rewrite <- e0, rx_wf in e. congruence.
        destruct (eq_dec (fnd (existT z zIn)) (existT z zIn)). congruence. easy.
    - destruct (eq_dec (existT (projT1 ry) (projT2 ry)) (existT z zIn)).
      + exfalso. rewrite <- sigT_eta in e. now rewrite <- e, ry_wf in n.
      + easy.
  Qed.

  Lemma mergeFind_lt {w} (fnd : Ref w -> Ref w) (rx ry : Ref w)
    (rx_wf : IsRepr fnd rx)
    (ry_wf : IsRepr fnd ry)
    (H : rx <> ry) :
    lessthan (measure (mergeFind fnd rx ry)) (measure fnd).
  Proof.
    rewrite measure_mergeFind; auto. apply lessthan_removeRepr.
    unfold measure. rewrite env.lookup_tabulate.
    now rewrite <- sigT_eta, ry_wf, eq_dec_refl.
  Qed.

  Lemma refl {A w} (d : DS A w) (x : Ref w) :
    equiv d x x = true.
  Proof. unfold equiv. now rewrite eq_dec_refl. Qed.

  Lemma sym {A w} (d : DS A w) (x y : Ref w) :
    equiv d x y = true ->
    equiv d y x = true.
  Proof. unfold equiv. do 2 destruct eq_dec; congruence. Qed.

  (* Lemma equiv_union {A w} (f : A w -> A w -> A w) *)
  (*   (d : DS A w) (x y : Ref w) : *)
  (*   equiv (merge f d x y) x y = true. *)
  (* Proof. *)
  (*   unfold equiv, merge, mergeFind, equiv; cbn. *)
  (*   rewrite eq_dec_refl. *)
  (*   destruct (eq_dec (find d y) (find d x)); *)
  (*     now rewrite eq_dec_refl. *)
  (* Qed. *)

  (* Lemma equiv_monotone {A w} (f : A w -> A w -> A w) *)
  (*   (d : DS A w) (x y u v : Ref w) : *)
  (*   equiv d x y               = true -> *)
  (*   equiv (merge f d u v) x y = true. *)
  (* Proof. *)
  (*   unfold merge, mergeFind, equiv; cbn. *)
  (*   destruct (eq_dec (find d x) (find d y)); cbn; [intros _|easy]. *)
  (*   rewrite e. clear x e. *)
  (*   destruct (eq_dec (find d v) (find d y)); cbn; *)
  (*     now rewrite eq_dec_refl. *)
  (* Qed. *)

End DS.

Section ShallowConstraints.
  Import World.notations.

  Inductive TyF (w : World) : Type :=
  | TyF_bool
  | TyF_func (x y : Ref w).
  #[global] Arguments TyF_bool {w}.
  #[global] Arguments TyF_func {w} x y.

  Definition inj : ⊢ʷ TyF -> Ṫy :=
    fun w t =>
      match t with
      | TyF_bool     => ṫy.bool
      | TyF_func x y => ṫy.func (ṫy.var (projT2 x)) (ṫy.var (projT2 y))
      end.

  Variant ShallowConstraint (w : World) : Type :=
    | FlexFlex (x y : Ref w)
    | FlexRigid (x : Ref w) (t : TyF w).

End ShallowConstraints.

Import DS.
Section Solve.

  Import (notations) iris.bi.interface.
  Import Pred Pred.notations Pred.proofmode.

  #[export] Instance inst_ref : Inst Ref Ty :=
    fun w x ι => env.lookup ι (projT2 x).

  #[export] Instance inst_tyf : Inst TyF Ty :=
    fun w t => inst (inj t).

  Definition compatible_find : ⊢ʷ (Ref -> Ref) -> Pred :=
    fun w fnd => (∀ (x : Ref w), x =ₚ fnd x)%P%I.

  Definition compatible_cont {w} (fnd : Ref w -> Ref w)
    (cnt : forall x, IsRepr fnd x -> Option TyF w) : Pred w :=
    (∀ (x : Ref w) (rx : IsRepr fnd x) t,
        ⌜cnt x rx = Some t⌝ ->ₚ
        ṫy.var (projT2 x) =ₚ inj t)%P%I.

  #[export] Instance instpred_ds : InstPred (DS (Option TyF)) :=
    fun w d => andₚ (compatible_find (find d)) (compatible_cont (cont d)).

  Definition StateT (S : TYPE) (M : TYPE -> TYPE) (A : TYPE) : TYPE :=
    S -> M (Prod A S).

  Definition Id (A : TYPE) : TYPE := A.

  Definition Cont (R : ACC) (P A : TYPE) : TYPE :=
    Box R (A -> P) -> P.

  Definition M := StateT (DS (Option TyF)) Option.

  Definition pure {A} : ⊢ʷ A -> M A :=
    fun w a s => Some (a, s).

  Definition fail {A} : ⊢ʷ M A :=
    fun w s => None.
  #[global] Arguments fail {A w}.

  Definition bind {A B} : ⊢ʷ M A -> (A -> M B) -> M B :=
    fun w m f s => option.bind (m s) (fun '(a,s') => f a s').

  (* Variant ShallowConstraint (w : World) : Type := *)
  (* | FlexFlex (x y : Ref w) *)
  (* | FlexRigid (x : Ref w) (t : TyF w). *)

  Variant CFlex (w : World) : Type :=
  | cflex (x y : Ref w).

  #[export] Instance instpred_cflex : InstPred CFlex.
  Proof.
    intros w [x y]. apply (Pred.eqₚ x y).
  Defined.

  Definition mergeCell :
    ⊢ʷ Option TyF -> Option TyF -> Option (Prod (Option TyF) (List CFlex)) :=
    fun w ot1 ot2 =>
      match ot1 , ot2 with
      | Some t1 , Some t2 =>
          match t1 , t2 with
          | TyF_bool         , TyF_bool => Some (ot1, [])
          | TyF_func r11 r12 , TyF_func r21 r22 =>
              let c1 := cflex r11 r21 in
              let c2 := cflex r12 r22 in
              Some (ot1, [c1;c2])
          | _                , _ => None
          end
      | Some _ , None   => Some (ot1, [])
      | None   , Some _ => Some (ot2, [])
      | None   , None   => Some (None, [])
      end%list.

  Definition sim {w} (x y : Option TyF w) : Pred w :=
    match x , y with
    | Some x , Some y => inj x =ₚ inj y
    | _      , _      => Trueₚ
    end.

  Lemma mergeCell_spec {w} (t1 t2 : Option TyF w) :
    option.spec
      (fun '(t,cs) => sim t1 t2 ⊣⊢ₚ sim t1 t /\ₚ sim t2 t /\ₚ instpred cs)
      (sim t1 t2 ⊢ₚ Falseₚ)
      (mergeCell t1 t2).
  Proof.
    destruct t1 as [t1|], t2 as [t2|]; cbn.
    - destruct t1, t2; constructor; cbn.
      + now rewrite eqₚ_refl, !and_true_l.
      + now rewrite peq_ty_noconfusion.
      + now rewrite peq_ty_noconfusion.
      + rewrite !eq_func. constructor; intros ι.
        pred_unfold. unfold Trueₚ. intuition.
    - constructor. easy.
    - constructor. easy.
    - constructor. easy.
  Qed.

  Definition merge {w} (d : DS (Option TyF) w)
    {rx ry : Ref w} (rx_wf : IsRepr (find d) rx)
    (ry_wf : IsRepr (find d) ry) (v : Option TyF w) : DS (Option TyF) w :=
    {| find    := mergeFind (find d) rx ry;
       find_wf := mergeFind_wf (find_wf d) rx_wf ry_wf;
       cont    := mergeCont (find d) (cont d) rx ry v
    |}.

  Section OpenRecursion.

    Context {w} (d : DS (Option TyF) w)
      (orec : forall d' : DS (Option TyF) w,
          MR lessthan (fun d => measure (find d)) d' d ->
          List CFlex w -> Option (DS (Option TyF)) w).

    Definition mergeRepr (cs' : List CFlex w) {rx ry : Ref w} (n : rx <> ry)
      (rx_wf : IsRepr (find d) rx) (ry_wf : IsRepr (find d) ry) :=
      match mergeCell (cont d rx rx_wf) (cont d ry ry_wf) with
      | Some (ot, cs'') =>
          orec
            (merge d rx_wf ry_wf ot)
            (mergeFind_lt rx_wf ry_wf n)
            (app cs'' cs')
      | None => None
      end.

    Fixpoint osolve (cs : List CFlex w) :
      Option (DS (Option TyF)) w :=
      match cs with
      | nil                  => Some d
      | cons (cflex x y) cs' =>
          let rx := find d x in
          let ry := find d y in
          match eq_dec rx ry with
          | left _ => osolve cs'
          | right n =>
              let rx_wf := find_wf d x in
              let ry_wf := find_wf d y in
              mergeRepr cs' n rx_wf ry_wf
          end
      end.
  End OpenRecursion.

  Definition solve {w} : forall (d : DS (Option TyF) w) (cs : List CFlex w),
      Option (DS (Option TyF)) w :=
    Fix (measure_wf lessthan_wellfounded (fun d => measure (find d))) _ osolve.

  Lemma compatible_mergefind {w} (fnd : Ref w -> Ref w) (x y : Ref w) :
    (⊢ x =ₚ y ->ₚ
       compatible_find fnd ->ₚ
       compatible_find (mergeFind fnd x y))%P%I.
  Proof.
    unfold compatible_find; constructor. intros ι _ Heq Hfind. pred_unfold.
    intros z. rewrite (Hfind z). clear Hfind. unfold mergeFind.
    destruct eq_dec; subst; auto.
  Qed.

  Lemma compatible_mergecont {w} (x y : Ref w) (t : Option TyF w)
    (r : Ref w → Ref w) (rx : IsRepr r x) (ry : IsRepr r y)
    (o : ∀ x0 : Ref w, IsRepr r x0 → Option TyF w) :
    (⊢ x =ₚ y ->ₚ compatible_find r ->ₚ compatible_cont o ->ₚ compatible_cont (mergeCont r o x y t))%P%I.
  Proof.
    constructor. intros ι _ Heq Hfind Hcont. pred_unfold.
    intros z rz ot. pred_unfold. unfold mergeCont.
    destruct eq_dec. intros Heqt. subst. unfold inst, inst_ref in Heq.
  Admitted.

  Import iris.proofmode.tactics.

  Lemma merge_correct {w} (d : DS (Option TyF) w)
    (x y : Ref w)
    (rx : IsRepr (DS.find d) x)
    (ry : IsRepr (DS.find d) y)
    (t : Option TyF w) :
    x =ₚ y ⊢ₚ instpred d ->ₚ instpred (Solve.merge d rx ry t).
  Proof.
    unfold merge, instpred, instpred_ds in *. cbn.
    iIntros "#Heq [#Hfind #Hcont]". iSplit.
    - now iApply compatible_mergefind.
    - iApply compatible_mergecont; auto.
  Qed.

  Lemma solve_sound {w} (d : DS (Option TyF) w) :
    forall (cs : List CFlex w),
      instpred (solve d cs) ⊢ₚ instpred d ->ₚ instpred cs.
  Proof.
    unfold solve, Fix.
    generalize (measure_wf lessthan_wellfounded (fun d => measure (DS.find d)) d) as a.
    induction a as [d a IH] using Acc_inv_dep.
    induction cs; cbn.
    - easy.
    - destruct a0. destruct eq_dec; cbn.
      + rewrite IHcs. constructor. intros ι. pred_unfold. clear - e.
        intros Hcs Hd. specialize (Hcs Hd). split; auto.
        destruct Hd as [Hwf _]. unfold compatible_find in Hwf. pred_unfold.
        now rewrite (Hwf x) (Hwf y) e.
      + clear IHcs. unfold mergeRepr.
        match goal with
          |- context[mergeCell ?t1 ?t2] =>
            destruct (mergeCell_spec t1 t2) as [[t cs'']|]
        end; cbn; [|easy]. rewrite IH. clear IH.
  Admitted.

End Solve.

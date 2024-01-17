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
From Em Require Free_Deep Free_Shallow
  Monad.Interface Shallow.Interface.

Module S := Shallow.Interface.
Module D := Monad.Interface.

Import Pred Pred.notations Pred.Sub Pred.proofmode world.notations.

#[local] Set Implicit Arguments.

Declare Scope rel_scope.
Delimit Scope rel_scope with R.

Module logicalrelation.

  (* We define relations between (D)eep and (S)hallow types *)
  Definition RawRel (DA : OType) (SA : Type) : Type :=
    forall (w : World), DA w -> SA -> Pred w.

  (* We use a typeclass as an interface for these relations.
     These relations are defined using a single constructor MkRel.
     To get the underlying relation out, you can use the projection RSat. *)
  Class Rel (DA : OType) (SA : Type) : Type :=
    MkRel { RSat : forall (w : World), DA w -> SA -> Pred w }.

  Bind Scope rel_scope with Rel.
  #[global] Arguments MkRel [DA SA] &.
  #[global] Arguments RSat {_ _} _ {w} ι _ _.

  (* Given a relation between a (D)eep type DA and a (S)hallow type SA, and evidence d that DA holds in all worlds (i.e. DA is Valid),
     we define a relation between this Valid type DA and its shallow counterpart SA. *)
  Definition RValid {DA SA} (RA : Rel DA SA) (d : Valid DA) (s : SA) : Prop :=
    forall (w : World), (⊢ @RSat DA SA RA w (d w) s).

  (* We use ℛ (\McR) to denote these relations that hold for Valid types *)
  #[local] Notation "ℛ⟦ R ⟧@{ ι }" := (RSat R%R ι) (format "ℛ⟦ R ⟧@{ ι }") .
  #[local] Notation "ℛ⟦ R ⟧" := (RValid R%R) (format "ℛ⟦ R ⟧").

  (* This instance can be used for any (first-class) symbolic data that can be
       instantiated with a valuation, i.e. symbolic terms, stores, heaps etc. *)
  Definition RInst AT A {instA : Inst AT A} : Rel AT A :=
    MkRel (fun w d s ι => s = inst d ι)%P.
  Arguments RInst _ _ {_}.

  (* Similarly, we can "upgrade" a relation between a (D)eep and (S)hallow type,
     to also relate values bda of boxed (D)eep types. *)
  #[export] Instance RBox {DA SA} (RA : Rel DA SA) : Rel (Box Prefix DA) SA :=
    MkRel (fun (w : World) (bda : Box Prefix DA w) (sa : SA) =>
             PBox (fun (w' : World) (θ : w ⊑⁺ w') => RSat RA (bda w' θ) sa)).


  (* For functions/impl: related inputs go to related outputs *)
  #[export] Instance RImpl {DA SA DB SB} (RA : Rel DA SA) (RB : Rel DB SB) :
    Rel (DA ⇢ DB) (SA -> SB) :=
    MkRel
      (fun w df sf =>
         ∀ (da : DA w) (sa : SA),
           RSat RA da sa → RSat RB (df da) (sf sa))%I.

  (* #[export] Instance RForall {𝑲} *)
  (*   {AT : forall K : 𝑲, TYPE} {A : forall K : 𝑲, Type} *)
  (*   (RA : forall K, Rel (AT K) (A K)) : *)
  (*   Rel (@Forall 𝑲 AT) (forall K : 𝑲, A K) := *)
  (*   MkRel (fun w ι fs fc => *)
  (*            forall K : 𝑲, *)
  (*              ℛ⟦RA K⟧@{ι} (fs K) (fc K)). *)

  #[export] Instance RTy : Rel OTy Ty :=
    RInst OTy Ty.

  #[export] Instance RUnit : Rel Unit unit := RInst Unit unit.

  #[export] Instance RConst A : Rel (Const A) A := RInst (Const A) A.

  (* #[export] Instance RProd `(RA : Rel AT A, RB : Rel BT B) : *)
  (*   Rel (WProd AT BT) (A * B)%type := *)
  (*   MkRel (fun w ι '(ta,tb) '(va,vb) => *)
  (*            ℛ⟦RA⟧@{ι} ta va /\ ℛ⟦RB⟧@{ι} tb vb). *)

  Module Import notations.
    Open Scope rel_scope.
    (* Notation "ℛ⟦ R ⟧@{ ι }" := (RSat R%R ι) (format "ℛ⟦ R ⟧@{ ι }"). *)
    Notation "ℛ⟦ R ⟧" := (RValid R%R) (format "ℛ⟦ R ⟧").
    Notation "A ↣ B" :=
      (RImpl A%R B%R)
        (at level 99, B at level 200, right associativity)
        : rel_scope.
    Notation "□ A"    := (RBox A%R) : rel_scope.
    (* Notation "'∀' x .. y , R " := *)
    (*   (RForall (fun x => .. (RForall (fun y => R)) ..)) *)
    (*     (at level 200, x binder, y binder, right associativity, *)
    (*       format "'[  ' '[  ' ∀  x  ..  y ']' ,  '/' R ']'") *)
    (*     : rel_scope. *)
  End notations.

  #[export] Instance RPred : Rel Pred Prop :=
    MkRel (fun w DP SP ι => DP ι <-> SP ).

  Section MonadClasses.

    Context (DM : OType → OType) (SM : Type -> Type)
      (RM : forall {DA SA} (RA : Rel DA SA), Rel (DM DA) (SM SA)).

    Class RPure `{D.Pure DM, MRet SM} : Type :=
      rpure DA SA (RA : Rel DA SA) :
        ℛ⟦RA ↣ RM RA⟧ D.pure (mret).

    (* Relatedness via RImpl? *)
    Class RBind `{D.Bind Prefix DM, S.MBind SM} (M : OType → OType) : Type :=
      rbind DA DB SA SB (RA : Rel DA SA) (RB : Rel DB SB) :
        ℛ⟦RM RA ↣ □(RA ↣ RM RB) ↣ RM RB⟧ D.bind (S.bind).

    Class Fail (M : OType → OType) : Type :=
      fail : ∀ A, ⊧ M A.
    #[global] Arguments fail {M _ A w}.


  End MonadClasses.

End logicalrelation.


(* Module MonadNotations. *)
(*   Notation "' x <- ma ;; mb" := *)
(*     (bind ma (fun _ _ x => mb)) *)
(*       (at level 80, x pattern, ma at next level, mb at level 200, right associativity, *)
(*         format "' x  <-  ma  ;;  mb"). *)
(*   Notation "x <- ma ;; mb" := *)
(*     (bind ma (fun _ _ x => mb)) *)
(*       (at level 80, ma at next level, mb at level 200, right associativity). *)

(*   Existing Class sub. *)
(*   #[export] Existing Instance trans. *)
(*   #[export] Hint Mode sub - + - : typeclass_instances. *)
(* End MonadNotations. *)

(* Import Pred Pred.Sub. *)


(* Class TypeCheckM (M : OType -> OType) : Type := *)
(*   { equals : ⊧ OTy ⇢ OTy ⇢ M Unit; *)
(*     pick   : ⊧ M OTy; *)
(*   }. *)
(* #[global] Arguments fail {_ _ _ w}. *)
(* #[global] Arguments pick {_ _ w}. *)

(* Class WeakestPre (Θ : SUB) (M : OType -> OType) : Type := *)
(*   WP [A] : ⊧ M A ⇢ Box Θ (A ⇢ Pred) ⇢ Pred. *)
(* Class WeakestLiberalPre (Θ : SUB) (M : OType -> OType) : Type := *)
(*   WLP [A] : ⊧ M A ⇢ Box Θ (A ⇢ Pred) ⇢ Pred. *)

(* Class AxiomaticSemantics *)
(*   Θ {reflΘ : Refl Θ} {stepΘ : Step Θ} {transΘ : Trans Θ } {reflTransΘ : ReflTrans Θ} *)
(*     {lkreflΘ : LkRefl Θ} {lkStepθ : LkStep Θ} {lktransΘ : LkTrans Θ} *)
(*   M {pureM : Pure M} {bindM : Bind Θ M} {failM : Fail M} {tcM : TypeCheckM M} *)
(*     {wpM : WeakestPre Θ M} {wlpM : WeakestLiberalPre Θ M} : Type := *)

(*   { ax_wp_pure [A w] (a : A w) (Q : ◻(A ⇢ Pred) w) : *)
(*       WP (pure a) Q ⊣⊢ₚ Q _ refl a; *)
(*     ax_wp_bind [A B w0] (m : M A w0) (f : ◻(A ⇢ M B) w0) (Q : ◻(B ⇢ Pred) w0) : *)
(*       WP (bind m f) Q ⊣⊢ₚ WP m (fun _ θ1 a => WP (f _ θ1 a) (fun _ θ2 => Q _ (θ1⊙θ2))); *)
(*     ax_wp_equals [w] (σ τ : OTy w) (Q : ◻(Unit ⇢ Pred) w) : *)
(*       WP (equals σ τ) Q ⊣⊢ₚ σ =ₚ τ /\ₚ Q _ refl tt; *)
(*     ax_wp_pick [w] (Q : ◻(OTy ⇢ Pred) w) : *)
(*       let α := world.fresh w in *)
(*       WP pick Q ⊣⊢ₚ Sub.wp step (Q (w ، α) step (oty.evar world.in_zero)); *)
(*     ax_wp_fail [A w] (Q : ◻(A ⇢ Pred) w) : *)
(*       WP fail Q ⊣⊢ₚ ⊥ₚ; *)
(*     ax_wp_mono [A w] (m : M A w) (P Q : ◻(A ⇢ Pred) w) : *)
(*       ◼(fun _ θ1 => ∀ a, P _ θ1 a -∗ Q _ θ1 a) ⊢ *)
(*       (WP m P -∗ WP m Q); *)

(*     ax_wlp_pure [A w] (a : A w) (Q : ◻(A ⇢ Pred) w) : *)
(*       WLP (pure a) Q ⊣⊢ₚ Q _ refl a; *)
(*     ax_wlp_bind [A B w0] (m : M A w0) (f : ◻(A ⇢ M B) w0) (Q : ◻(B ⇢ Pred) w0) : *)
(*       WLP (bind m f) Q ⊣⊢ₚ WLP m (fun w1 θ1 a => WLP (f _ θ1 a) (fun _ θ2 => Q _ (trans θ1 θ2))); *)
(*     ax_wlp_equals [w] (σ τ : OTy w) (Q : ◻(Unit ⇢ Pred) w) : *)
(*       WLP (equals σ τ) Q ⊣⊢ₚ σ =ₚ τ ->ₚ Q _ refl tt; *)
(*     ax_wlp_pick [w] (Q : ◻(OTy ⇢ Pred) w) : *)
(*       let α := world.fresh w in *)
(*       WLP pick Q ⊣⊢ₚ Sub.wlp step (Q (w ، α) step (oty.evar world.in_zero)); *)
(*     ax_wlp_fail [A w] (Q : ◻(A ⇢ Pred) w) : *)
(*       WLP fail Q ⊣⊢ₚ ⊤ₚ; *)
(*     ax_wlp_mono [A w] (m : M A w) (P Q : ◻(A ⇢ Pred) w) : *)
(*       ◼(fun _ θ1 => ∀ a, P _ θ1 a -∗ Q _ θ1 a) ⊢ *)
(*       (WLP m P -∗ WLP m Q); *)

(*     ax_wp_impl [A w] (m : M A w) (P : ◻(A ⇢ Pred) w) (Q : Pred w) : *)
(*       (WP m P ->ₚ Q) ⊣⊢ₚ WLP m (fun w1 θ1 a1 => P w1 θ1 a1 ->ₚ Q[θ1]); *)
(*   }. *)
(* #[global] Arguments AxiomaticSemantics Θ {_ _ _ _ _ _ _} _ {_ _ _ _ _ _}. *)


(* (* Alternative rule for pick which substitutes the last variable away *)
(*  as discussed in the papter. *) *)
(* Lemma ax_wp_pick_substitute `{AxiomaticSemantics Θ M, Thick Θ} {lkThickΘ : LkThick Θ} *)
(*   [w] (Q : ◻(OTy ⇢ Pred) w) : *)
(*   WP pick Q ⊣⊢ₚ *)
(*     let α := world.fresh w in *)
(*     (∃ₚ τ : OTy w, (Q (w ، α) step (oty.evar world.in_zero))[thick α (αIn := world.in_zero) τ]). *)
(* Proof. *)
(*   rewrite ax_wp_pick; cbn. constructor; intros ι. *)
(*   unfold Sub.wp; pred_unfold. split. *)
(*   - intros (ι' & Heq & HQ). destruct (env.view ι') as [ι' τ]. *)
(*     erewrite inst_step_snoc in Heq. subst. *)
(*     exists (lift τ). now rewrite inst_thick inst_lift. *)
(*   - intros (τ & HQ). rewrite inst_thick in HQ. *)
(*     exists (env.snoc ι _ (inst τ ι)). *)
(*     now rewrite inst_step_snoc. *)
(* Qed. *)

(* Class TypeCheckLogicM *)
(*   Θ {reflΘ : Refl Θ} {stepΘ : Step Θ} {transΘ : Trans Θ } *)
(*     {lkreflΘ : LkRefl Θ} {lkStepθ : LkStep Θ} *)
(*   M {pureM : Pure M} {bindM : Bind Θ M} {failM : Fail M} {tcM : TypeCheckM M} *)
(*     {wpM : WeakestPre Θ M} {wlpM : WeakestLiberalPre Θ M} : Type := *)

(*   { wp_pure [A] {subA : Subst A} *)
(*       [w] (a : A w) (Q : ◻(A ⇢ Pred) w) : *)
(*       Q _ refl a ⊢ₚ WP (pure a) Q; *)
(*     wp_bind [A B w0] (m : M A w0) (f : ◻(A ⇢ M B) w0) (Q : ◻(B ⇢ Pred) w0) : *)
(*       WP m (fun w1 θ1 a => WP (f _ θ1 a) (fun _ θ2 => Q _ (trans θ1 θ2))) ⊢ₚ WP (bind m f) Q; *)
(*     wp_equals [w] (σ τ : OTy w) (Q : ◻(Unit ⇢ Pred) w) : *)
(*       σ =ₚ τ /\ₚ ◼(fun _ θ => Q _ θ tt) ⊢ₚ WP (equals σ τ) Q; *)
(*     wp_pick [w] [Q : ◻(OTy ⇢ Pred) w] (τ : Ty) : *)
(*       ◼(fun _ θ => ∀ₚ τ', lift τ =ₚ τ' ->ₚ Q _ θ τ') ⊢ₚ WP pick Q; *)
(*     wp_fail [A w] (Q : ◻(A ⇢ Pred) w) : *)
(*       ⊥ₚ ⊢ₚ WP fail Q; *)
(*     wp_mono [A w] (m : M A w) (P Q : ◻(A ⇢ Pred) w) : *)
(*       ◼(fun _ θ => ∀ₚ a, P _ θ a -∗ Q _ θ a)%I ⊢ₚ *)
(*       (WP m P -∗ WP m Q)%I; *)

(*     wlp_pure [A] {subA : Subst A} *)
(*       [w] (a : A w) (Q : ◻(A ⇢ Pred) w) : *)
(*       Q _ refl a ⊢ₚ WLP (pure a) Q; *)
(*     wlp_bind [A B w0] (m : M A w0) (f : ◻(A ⇢ M B) w0) (Q : ◻(B ⇢ Pred) w0) : *)
(*       WLP m (fun w1 θ1 a => WLP (f _ θ1 a) (fun _ θ2 => Q _ (trans θ1 θ2))) ⊢ₚ WLP (bind m f) Q; *)
(*     wlp_equals [w] (σ τ : OTy w) (Q : ◻(Unit ⇢ Pred) w) : *)
(*       σ =ₚ τ ->ₚ ◼(fun _ θ => Q _ θ tt) ⊢ₚ WLP (equals σ τ) Q; *)
(*     wlp_pick [w] (Q : ◻(OTy ⇢ Pred) w) : *)
(*       ◼(fun _ θ => ∀ₚ τ, Q _ θ τ) ⊢ₚ WLP pick Q; *)
(*     wlp_fail [A w] (Q : ◻(A ⇢ Pred) w) : *)
(*       ⊤ₚ ⊢ₚ WLP fail Q; *)
(*     wlp_mono [A w] (m : M A w) (P Q : ◻(A ⇢ Pred) w) : *)
(*       ◼(fun _ θ => ∀ₚ a, P _ θ a -∗ Q _ θ a)%I ⊢ₚ *)
(*       (WLP m P -∗ WLP m Q)%I; *)

(*     wp_impl [A w] (m : M A w) (P : ◻(A ⇢ Pred) w) (Q : Pred w) : *)
(*       WLP m (fun w1 θ1 a1 => P w1 θ1 a1 ->ₚ Q[θ1]) ⊢ₚ (WP m P ->ₚ Q); *)

(*   }. *)
(* #[global] Arguments TypeCheckLogicM Θ {_ _ _ _ _} _ {_ _ _ _ _ _}. *)

(* #[export] Instance axiomatic_tcmlogic `{AxiomaticSemantics Θ M} : *)
(*   TypeCheckLogicM Θ M. *)
(* Proof. *)
(*   constructor; intros. *)
(*   - now rewrite ax_wp_pure. *)
(*   - now rewrite ax_wp_bind. *)
(*   - rewrite ax_wp_equals. iIntros "[#Heq >HQ]". now iSplit. *)
(*   - rewrite ax_wp_pick. rewrite <- (Sub.intro_wp_step τ). *)
(*     iIntros "#H !> #Heq". iMod "H". *)
(*     iSpecialize ("H" $! (oty.evar world.in_zero) with "Heq"). *)
(*     now rewrite trans_refl_r. *)
(*   - now rewrite ax_wp_fail. *)
(*   - apply ax_wp_mono. *)
(*   - now rewrite ax_wlp_pure. *)
(*   - now rewrite ax_wlp_bind. *)
(*   - rewrite ax_wlp_equals. iIntros "#HQ #Heq". *)
(*     iSpecialize ("HQ" with "Heq"). now iMod "HQ". *)
(*   - rewrite ax_wlp_pick. iIntros "#HQ !>". iMod "HQ". *)
(*     iSpecialize ("HQ" $! (oty.evar world.in_zero)). *)
(*     now rewrite trans_refl_r. *)
(*   - now rewrite ax_wlp_fail. *)
(*   - apply ax_wlp_mono. *)
(*   - now rewrite ax_wp_impl. *)
(* Qed. *)

(* Lemma wp_mono' `{TypeCheckLogicM Θ M} {A w} (m : M A w) (P Q : ◻(A ⇢ Pred) w) : *)
(*   (WP m P -∗ ◼(fun _ θ1 => ∀ₚ a1, P _ θ1 a1 -∗ Q _ θ1 a1) -∗ WP m Q)%P. *)
(* Proof. iIntros "WP PQ". iRevert "WP". now rewrite -wp_mono. Qed. *)

(* Lemma wlp_mono' `{TypeCheckLogicM Θ M} {A w} (m : M A w) (P Q : ◻(A ⇢ Pred) w) : *)
(*   (WLP m P -∗ ◼(fun _ θ1 => ∀ₚ a1, P _ θ1 a1 -∗ Q _ θ1 a1) -∗ WLP m Q)%P. *)
(* Proof. iIntros "WP PQ". iRevert "WP". now rewrite -wlp_mono. Qed. *)

(* Definition wp_diamond {Θ : SUB} {A} : *)
(*   ⊧ Diamond Θ A ⇢ ◻(A ⇢ Pred) ⇢ Pred := *)
(*   fun w '(existT w1 (θ, a)) Q => Sub.wp θ (Q w1 θ a). *)

(* Definition wlp_diamond {Θ : SUB} {A} : *)
(*   ⊧ Diamond Θ A ⇢ ◻(A ⇢ Pred) ⇢ Pred := *)
(*   fun w '(existT w1 (θ, a)) Q => Sub.wlp θ (Q w1 θ a). *)

(* Definition wp_option {A w1 w2} : *)
(*   Option A w1 -> (A w1 -> Pred w2) -> Pred w2 := *)
(*   fun o Q => *)
(*     match o with *)
(*     | Some a => Q a *)
(*     | None => ⊥ₚ *)
(*     end%P. *)

(* Definition wlp_option {A w1 w2} : *)
(*   Option A w1 -> (A w1 -> Pred w2) -> Pred w2 := *)
(*   fun o Q => *)
(*     match o with *)
(*     | Some a => Q a *)
(*     | None => ⊤ₚ *)
(*     end%P. *)

(* Definition Solved (Θ : SUB) (A : OType) : OType := Option (Diamond Θ A). *)
(* Definition Prenex (A : OType) : OType := Solved Prefix (List (OTy * OTy) * A). *)

(* Section Solved. *)

(*   #[export] Instance wp_solved {Θ : SUB} : WeakestPre Θ (Solved Θ) := *)
(*     fun A w m Q => wp_option m (fun d => wp_diamond d Q). *)
(*   #[global] Arguments wp_solved {Θ} {A}%indexed_scope [w] _ _%B _. *)
(*   #[export] Instance wlp_solved {Θ : SUB} : WeakestLiberalPre Θ (Solved Θ) := *)
(*     fun A w m Q => wlp_option m (fun d => wlp_diamond d Q). *)
(*   #[global] Arguments wlp_solved {Θ} {A}%indexed_scope [w] _ _%B _. *)

(*   #[global] Instance params_wp_solved : Params (@wp_solved) 3 := {}. *)
(*   #[export] Instance proper_wp_solved_bientails {Θ A w} : *)
(*     Proper *)
(*       (pointwise_relation _ *)
(*          (forall_relation *)
(*             (fun _ => pointwise_relation _ *)
(*                         (pointwise_relation _ (⊣⊢ₚ))) ==> (⊣⊢ₚ))) *)
(*       (@wp_solved Θ A w). *)
(*   Proof. *)
(*     intros d p q pq. destruct d as [(w1 & r01 & a)|]; cbn; [|easy]. *)
(*     apply Sub.proper_wp_bientails. apply pq. *)
(*   Qed. *)

(*   #[export] Instance proper_wp_solved_entails {Θ A w} : *)
(*     Proper *)
(*       (pointwise_relation _ *)
(*          (forall_relation *)
(*             (fun _ => pointwise_relation _ *)
(*                         (pointwise_relation _ entails)) ==> entails)) *)
(*       (@wp_solved Θ A w). *)
(*   Proof. *)
(*     intros d p q pq. destruct d as [(w1 & r01 & a)|]; cbn; [|easy]. *)
(*     apply Sub.proper_wp_entails. apply pq. *)
(*   Qed. *)

(*   Lemma wp_solved_frame {Θ A w} (m : Solved Θ A w) *)
(*     (P : ◻(A ⇢ Pred) w) (Q : Pred w) : *)
(*     WP m P /\ₚ Q ⊣⊢ₚ WP m (fun w1 θ1 a1 => P w1 θ1 a1 /\ₚ subst Q θ1). *)
(*   Proof. *)
(*     destruct m as [(w1 & θ1 & a1)|]; cbn. *)
(*     - now rewrite Sub.and_wp_l. *)
(*     - now rewrite bi.False_and. *)
(*   Qed. *)

(*   #[export] Instance pure_solved {Θ} {reflΘ : Refl Θ} : *)
(*     Pure (Solved Θ) := *)
(*     fun A w a => Some (existT w (refl, a)). *)

(*   #[export] Instance bind_solved {Θ} {transΘ : Trans Θ} : *)
(*     Bind Θ (Solved Θ) := *)
(*     fun A B w m f => *)
(*       option.bind m *)
(*         (fun '(existT w1 (θ1,a1)) => *)
(*            option.bind (f w1 θ1 a1) *)
(*              (fun '(existT w2 (θ2,b2)) => *)
(*                 Some (existT w2 (trans θ1 θ2, b2)))). *)

(*   #[export] Instance fail_solved {Θ} : Fail (Solved Θ) := *)
(*     fun A w => None. *)

(*   Lemma wp_solved_pure {Θ} {reflΘ : Refl Θ} {lkreflΘ : LkRefl Θ} *)
(*     {A w0} (a : A w0) (Q : ◻(A ⇢ Pred) w0) : *)
(*     wp_solved (pure (M := Solved Θ) a) Q ⊣⊢ₚ Q _ refl a. *)
(*   Proof. cbn. now rewrite Sub.wp_refl. Qed. *)

(*   Lemma wp_solved_bind {Θ} {transΘ : Trans Θ} {lkTransΘ : LkTrans Θ} *)
(*     {A B w0} (m : Solved Θ A w0) (f : ◻(A ⇢ Solved Θ B) w0) *)
(*     (Q : ◻(B  ⇢ Pred) w0) : *)
(*     WP (bind m f) Q ⊣⊢ₚ WP m (fun w1 ζ1 a1 => WP (f w1 ζ1 a1) (_4 Q ζ1)). *)
(*   Proof. *)
(*     destruct m as [(w1 & r01 & a)|]; cbn; [|reflexivity]. *)
(*     destruct (f w1 r01 a) as [(w2 & r12 & b2)|]; cbn; *)
(*       now rewrite ?Sub.wp_trans ?Sub.wp_false. *)
(*   Qed. *)

(* End Solved. *)

(* #[export] Instance instpred_diamond {Θ A} `{ipA : InstPred A} : *)
(*   InstPred (Diamond Θ A) := *)
(*   fun w m => wp_diamond m (fun _ _ a => instpred a). *)
(* #[export] Instance instpred_solved {Θ A} `{ipA : InstPred A} : *)
(*   InstPred (Solved Θ A) := *)
(*   fun w m => WP m (fun _ _ a => instpred a). *)

(* Definition solved_hmap `{HMap Θ1 Θ2} {A} : ⊧ Solved Θ1 A ⇢ Solved Θ2 A := *)
(*   fun w => option.map (fun '(existT w (θ, a)) => existT w (hmap θ, a)). *)

(* Lemma instpred_solved_hmap `{LkHMap Θ1 Θ2} {A} `{ipA : InstPred A} *)
(*   {w} (m : Solved Θ1 A w) : *)
(*   instpred (solved_hmap m) ⊣⊢ₚ instpred m. *)
(* Proof. destruct m as [(w' & θ & a)|]; cbn; now rewrite ?Sub.wp_hmap. Qed. *)

(* (* Create HintDb wpeq. *) *)
(* (* #[export] Hint Rewrite *) *)
(* (*   (@subst_eq OEnv _ _ _ _) *) *)
(* (*   (@subst_eq OTy _ _ _ _) *) *)
(* (*   (@subst_trans OEnv _ _) *) *)
(* (*   (@subst_trans OTy _ _) *) *)
(* (*   @subst_lift *) *)
(* (*   @lift_insert *) *)
(* (*   : wpeq. *) *)

(* Ltac wpeq := *)
(*   progress *)
(*     (try done; *)
(*      try progress cbn; *)
(*      (* Unfortunately, autorewrite and rewrite strategy blow up with some long *)
(*         typeclass searches. Simply use rewrite for now. *) *)
(*      rewrite ?(@subst_eq OEnv _ _ _ _) *)
(*        ?(@subst_eq OTy _ _ _ _) *)
(*        ?(@subst_trans OEnv _ _) *)
(*        ?(@subst_trans OTy _ _) *)
(*        ?@subst_lift *)
(*        ?@lift_insert; *)
(*      try done; *)
(*      try match goal with *)
(*        | |- environments.envs_entails _ *)
(*               (eqₚ ?x ?x) => *)
(*            iApply eqₚ_intro *)
(*        | |- environments.envs_entails _ *)
(*               (eqₚ (insert ?x _ _) (insert ?x _ _)) => *)
(*            iApply eqₚ_insert; iSplit *)
(*        end; *)
(*      auto 1 with typeclass_instances; *)
(*      try (iStopProof; pred_unfold; *)
(*           intuition (subst; auto; fail))). *)

(* Ltac wpsimpl := *)
(*   match goal with *)
(*   | |- context[fun w : World => prod (?A w) (?B w)] => *)
(*       change_no_check (fun w : World => prod (A w) (B w)) with (Prod A B) *)

(*   | |- environments.envs_entails _ (bi_impl _ _) => *)
(*       iIntros "#?" *)
(*   | |- environments.envs_entails _ (bi_affinely _) => *)
(*       iModIntro *)
(*   | |- environments.envs_entails _ (bi_and _ _) => *)
(*       iSplit *)
(*   | |- environments.envs_entails _ (eqₚ _ _) => *)
(*       wpeq *)
(*   | |- environments.envs_entails _ (bi_pure True) => *)
(*       done *)
(*   | |- environments.envs_entails _ (WP (pure _) _) => *)
(*       rewrite -wp_pure ?trans_refl_r ?trans_refl_r ?subst_refl *)
(*       (* try (iStopProof; pred_unfold; intuition (subst; auto; fail)) *) *)
(*   | |- environments.envs_entails _ (WP (bind _ _) _) => *)
(*       iApply wp_bind *)
(*   | |- environments.envs_entails _ (WP pick _) => *)
(*       rewrite -wp_pick; iIntros (?w ?θ) "!>"; iIntros (?τ) "#?" *)
(*   | |- environments.envs_entails _ (WP (equals _ _) _) => *)
(*       rewrite -wp_equals; iSplit; *)
(*       [ iStopProof; pred_unfold; intuition (subst; auto; fail) *)
(*       | iIntros (?w ?θ) "!>" *)
(*       ] *)
(*   | |- environments.envs_entails _ (WP fail _) => *)
(*       rewrite -wp_fail *)

(*   | |- environments.envs_entails _ (WLP (pure _) _) => *)
(*       rewrite -wlp_pure ?trans_refl_r ?trans_refl_r ?subst_refl *)
(*   | |- environments.envs_entails _ (WLP (bind _ _) _) => *)
(*       rewrite -wlp_bind *)
(*   | |- environments.envs_entails _ (WLP pick _) => *)
(*       rewrite -wlp_pick; iIntros (?w ?θ) "!>"; iIntros (?τ) *)
(*   | |- environments.envs_entails _ (WLP (equals _ _) _) => *)
(*       rewrite -wlp_equals; iIntros "#?" (?w ?θ) "!>" *)
(*   | |- environments.envs_entails _ (WLP fail _) => *)
(*       rewrite -wlp_fail *)
(*   end. *)

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
From Em Require Monad.Interface Shallow.Monad.Interface.

Module S := Shallow.Monad.Interface.
Module D := Em.Monad.Interface.

Import Pred Pred.notations Pred.Sub Pred.proofmode world.notations.

#[local] Set Implicit Arguments.

Declare Scope rel_scope.
Delimit Scope rel_scope with R.

Module lr.

  (* We define relations between (D)eep and (S)hallow types *)
  Definition RawRel (DA : OType) (SA : Type) : Type :=
    forall (w : World), DA w -> SA -> Pred w.

  (* We define relations between (D)eep and (S)hallow types for which we use a
     typeclass as an interface. These relations are defined using a single
     constructor MkRel. To get the underlying relation out, you can use the
     projection RSat. *)
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
  #[local] Notation "ℛ⟦ R ⟧" := (RValid R%R) (format "ℛ⟦ R ⟧").

  (* This instance can be used for any (first-class) symbolic data that can be
       instantiated with a valuation, i.e. symbolic terms, stores, heaps etc. *)
  Definition RInst DA SA {instA : Inst DA SA} : Rel DA SA :=
    MkRel (fun w d s ι => s = inst d ι)%P.
  #[global] Arguments RInst _ _ {_} : simpl never.

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
           RSat RA da sa -∗ RSat RB (df da) (sf sa))%I.

  (* #[export] Instance RForall {𝑲} *)
  (*   {AT : forall K : 𝑲, TYPE} {A : forall K : 𝑲, Type} *)
  (*   (RA : forall K, Rel (AT K) (A K)) : *)
  (*   Rel (@Forall 𝑲 AT) (forall K : 𝑲, A K) := *)
  (*   MkRel (fun w ι fs fc => *)
  (*            forall K : 𝑲, *)
  (*              ℛ⟦RA K⟧@{ι} (fs K) (fc K)). *)

  Notation RTy := (RInst OTy Ty).
  Notation REnv := (RInst OEnv Env).

  #[export] Instance RExp : Rel OExp Exp :=
    RInst OExp Exp.

  #[export] Instance RUnit : Rel Unit unit :=
    MkRel (fun w _ _ => True%I).

  #[export] Instance RConst A : Rel (Const A) A :=
    MkRel (fun w a1 a2 => ⌜a1 = a2⌝)%I.

  #[export] Instance RProd `(RA : Rel AT A, RB : Rel BT B) :
    Rel (Prod AT BT) (A * B)%type :=
    MkRel (fun w '(ta,tb) '(va,vb) =>
             RSat RA ta va ∧ RSat RB tb vb)%I.

  #[export] Instance ROption `(RA : Rel DA SA) :
    Rel (Option DA) (option SA) :=
    MkRel (fun w do so =>
             match do , so with
             | Some d , Some s => RSat RA d s
             | None   , None   => True%I
             | _      , _      => False %I
             end).

  (* #[export] Instance RPred : Rel Pred Prop := *)
  (*   MkRel (fun w DP SP => DP ↔ ⌜SP⌝)%I. *)
  (*   MkRel (fun w DP SP => DP ∗-∗ ⌜SP⌝)%I. *)

  #[export] Instance RPred : Rel Pred Prop :=
    MkRel (fun w DP SP ι => DP ι <-> SP ).
  #[global] Arguments RPred : simpl never.

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

  #[export] Instance into_rsat_wlp [Θ : SUB] [w0 w1 : World] (θ : Θ w0 w1)
    DA SA `{InstSubst DA SA} (da0 : DA w0) (da1 : DA w1) (sa : SA) :
    IntoSubst θ da0 da1 ->
    IntoWlp θ (RSat (RInst DA SA) da0 sa) (RSat (RInst DA SA) da1 sa).
  Proof.
    intros Hsubst. constructor. intros ι -> ? <-.
    simpl. now rewrite <- Hsubst, inst_subst.
  Qed.

  Lemma rand :
    ⊧ fun w => ⊢ RSat (RPred ↣ RPred ↣ RPred) (@bi_and (@bi_pred w)) and.
  Proof. firstorder. Qed.

  Lemma req [DA SA] {instA : Inst DA SA} w :
    ⊢ RSat (RInst DA SA ↣ RInst DA SA ↣ RPred) (eqₚ (w:=w)) eq.
  Proof. simpl; do 3 (constructor; intros ?); now subst.  Qed.

  Lemma rinsert x w :
    ⊢ RSat (w:=w) (RTy ↣ REnv ↣ REnv) (insert x) (insert x).
  Proof.
    constructor. simpl.
    intros ι _ dτ sτ. constructor.
    intros rτ dΓ sΓ. constructor.
    intros rΓ. rewrite inst_insert.
    now f_equal.
  Qed.

  Lemma rlift `{InstLift DA SA} {sa : SA} :
    ℛ⟦RInst DA SA⟧ (@lift _ _ _ sa) sa.
  Proof. constructor. intros ι _. simpl. now rewrite inst_lift. Qed.

  Lemma rlookup x {w} :
    ⊢ RSat (w := w) (REnv ↣ ROption RTy) (lookup x) (lookup x).
  Proof.
    do 2 constructor. intros ->.
    rewrite lookup_inst. now destruct lookup.
  Qed.

  Section MonadClasses.

    Context (DM : OType → OType) (SM : Type -> Type)
      (RM : forall {DA SA} (RA : Rel DA SA), Rel (DM DA) (SM SA)).

    Class RTypeCheckM `{D.Pure DM, S.MPure SM, D.Bind Prefix DM, S.MBind SM,
        D.Fail DM, S.MFail SM, D.TypeCheckM DM, S.TypeCheckM SM} : Type :=
      { rpure DA SA (RA : Rel DA SA) :
          ℛ⟦RA ↣ RM RA⟧ D.pure (@S.pure SM _ SA);
        rbind DA DB SA SB (RA : Rel DA SA) (RB : Rel DB SB) :
          ℛ⟦RM RA ↣ □(RA ↣ RM RB) ↣ RM RB⟧ D.bind (S.bind);
        rfail DA SA (RA : Rel DA SA) :
          ℛ⟦RM RA⟧ (@D.fail DM _ DA) (S.fail);
        requals :
          ℛ⟦RTy ↣ RTy ↣ RM RUnit⟧ D.equals S.equals;
        rpick :
          ℛ⟦RM RTy⟧ (@D.pick DM _) S.pick
      }.

    Class RTypeCheckLogicM `{D.WeakestPre Prefix DM, S.WeakestPre SM,
        D.WeakestLiberalPre Prefix DM, S.WeakestLiberalPre SM, RTypeCheckM} : Type :=
      { RWP [DA SA] (RA : Rel DA SA) :
          ℛ⟦RM RA ↣ □(RA ↣ RPred) ↣ RPred⟧
            (@D.WP Prefix DM _ DA)
            (@S.WP SM _ SA);
        RWLP [DA SA] (RA : Rel DA SA) :
          ℛ⟦RM RA ↣ □(RA ↣ RPred) ↣ RPred⟧
            (@D.WLP Prefix DM _ DA) (@S.WLP SM _ SA);
      }.

  End MonadClasses.
  #[global] Arguments RTypeCheckM DM SM RM {_ _ _ _ _ _ _ _}.
  #[global] Arguments RTypeCheckLogicM DM SM RM {_ _ _ _ _ _ _ _ _ _ _ _ _}.

End lr.

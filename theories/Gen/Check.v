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

From stdpp Require Import base gmap.
From iris Require Import proofmode.tactics.
From Em Require Import BaseLogic Monad.Interface.

Import Pred Pred.notations Pred.proofmode world.notations.

Set Implicit Arguments.

#[local] Notation "s [ ζ ]" :=
  (persist s ζ)
    (at level 7, left associativity,
      format "s [ ζ ]").

Section Generator.
  Import MonadNotations.

  Context {Θ} {reflΘ : Refl Θ} {stepΘ : Step Θ} {transΘ : Trans Θ}
    {reflTransΘ : ReflTrans Θ} {lkReflΘ : LkRefl Θ} {lkTransΘ : LkTrans Θ}
    {lkStepΘ : LkStep Θ}.
  Context {M} {pureM : Pure M} {bindM : Bind Θ M} {tcM : TypeCheckM M} .

  Definition check : Exp -> ⊧ Ėnv ⇢ Ṫy ⇢ M Ėxp :=
    fix gen e {w} Γ τ :=
      match e with
      | exp.var x =>
          match lookup x Γ with
          | Some τ' => _ <- assert τ τ' ;;
                       pure (ėxp.var x)
          | None    => fail
          end
      | exp.true  =>
          _ <- assert τ ṫy.bool ;;
          pure ėxp.true
      | exp.false =>
          _ <- assert τ ṫy.bool ;;
          pure ėxp.false
      | exp.ifte e1 e2 e3 =>
          e1' <- gen e1 Γ ṫy.bool ;;
          e2' <- gen e2 Γ[_] τ[_] ;;
          e3' <- gen e3 Γ[_] τ[_] ;;
          pure (ėxp.ifte e1'[_] e2'[_] e3')
      | exp.absu x e =>
          t1  <- pick ;;
          t2  <- pick ;;
          e'  <- gen e (Γ[_] ,, x∷t1[_]) t2 ;;
          _   <- assert (τ[_]) (ṫy.func t1[_] t2[_]) ;;
          pure (ėxp.abst x t1[_] e'[_])
      | exp.abst x t1 e =>
          t2  <- pick ;;
          e'  <- gen e (Γ[_] ,, x∷lift t1) t2 ;;
          _   <- assert (τ[_]) (ṫy.func (lift t1) t2[_]) ;;
          pure (ėxp.abst x (lift t1) e'[_])
      | exp.app e1 e2 =>
          t1  <- pick ;;
          e1' <- gen e1 Γ[_] (ṫy.func t1 τ[_]) ;;
          e2' <- gen e2 Γ[_] t1[_] ;;
          pure (ėxp.app e1'[_] e2')
      end.

  Definition synth (e : Exp) :
    ⊧ Ėnv ⇢ M (Prod Ṫy Ėxp) :=
    fun w G =>
      τ  <- pick ;;
      e' <- check e G[_] τ ;;
      pure (τ[_] , e').

  Import Pred.proofmode.
  Import iris.proofmode.tactics.
  Open Scope pred_scope.
  Import Pred Pred.notations.
  (* Import (notations) Open. *)

  Context {wpM : WeakestPre Θ M} {wlpM : WeakestLiberalPre Θ M}
    {tcLogicM : TypeCheckLogicM Θ M}.

  Definition TPB_algo : ⊧ Ėnv ⇢ Const Exp ⇢ Ṫy ⇢ Ėxp ⇢ Pred :=
    fun w0 G0 e τ0 e0 => WP (check e G0 τ0) (fun _ θ1 e1 => e0[θ1] =ₚ e1).

  Ltac wlpauto := repeat (repeat wpsimpl; try
    match goal with
    | IH: ∀ w G τ, bi_emp_valid (WLP (check ?e G τ) _)
      |- environments.envs_entails _ (WLP (check ?e ?G ?τ) _) =>
        iApply (wlp_mono' $! (IH _ G τ));
        iIntros (?w ?θ) "!>"; iIntros (?e') "#?"
    | |- environments.envs_entails _ (TPB _ _ _ _) =>
        predsimpl; iStopProof; pred_unfold;
        intuition (subst; econstructor; eauto; fail)
    end).

  Lemma sound_aux e :
    ∀ w (G : Ėnv w) (t : Ṫy w),
      ⊢ WLP (check e G t) (fun w1 θ ee => G[θ] |--ₚ e; t[θ] ~> ee).
  Proof.
    induction e; cbn; intros w G τ; iStartProof; wlpauto.
    destruct lookup eqn:HGx; wlpauto. iStopProof; pred_unfold.
    intros ->. constructor. now rewrite lookup_inst HGx.
  Qed.

  Lemma sound (e : Exp) (w0 : World) (G0 : Ėnv w0) t0 e0 :
    TPB_algo G0 e t0 e0 ⊢ₚ G0 |--ₚ e; t0 ~> e0.
  Proof.
    iStartProof. rewrite wand_is_impl. rewrite -wp_impl.
    iApply (wlp_mono' $! (@sound_aux e w0 G0 t0)).
    iIntros "%w1 %θ1 !>" (e') "HT". iStopProof. pred_unfold.
    intros HT Heq. now subst.
  Qed.

  Ltac wpauto := repeat (repeat wpsimpl; try
    match goal with
    | IH: ∀ w (G : Ėnv w) (t : Ṫy w),
        bi_emp_valid (bi_impl _ (bi_impl _ (WP (check ?e G t) _)))
        |- environments.envs_entails _ (WP (check ?e ?G ?t) _) =>
        iPoseProof (IH _ G t with "[] []") as "-#IH"; clear IH;
        [ | | iApply (wp_mono' with "IH");
              iIntros (?w ?θ) "!>"; iIntros (?e') "#?"
        ]
    end).

  Lemma complete_aux {G e t ee} (T : G |-- e ∷ t ~> ee) :
    ∀ w0 (G0 : Ėnv w0) (t0 : Ṫy w0),
      ⊢ lift G =ₚ G0 ->ₚ lift t =ₚ t0 ->ₚ
      WP (check e G0 t0) (fun _ _ e' => Open.pure ee =ₚ e')%P.
  Proof.
    induction T; cbn; intros w0 G0 t0; iStartProof; wpauto.
    destruct (G0 !! _) eqn:HGx; wpauto.
    + iApply wp_assert. iSplit.
      * iStopProof; pred_unfold. intros ? [-> ->].
        rewrite lookup_inst HGx in H. now injection H.
      * iIntros (?w ?θ) "!>"; wpauto.
    + iStopProof; pred_unfold. intros ? []. subst.
      rewrite lookup_inst HGx in H. now discriminate H.
  Qed.

  Lemma complete (e : Exp) w0 (G0 : Ėnv w0) t0 e0 :
    G0 |--ₚ e; t0 ~> e0 ⊢ₚ TPB_algo G0 e t0 e0.
  Proof.
    unfold TPB_algo. pred_unfold. intros ι HT.
    pose proof (complete_aux HT G0 t0) as [Hcompl].
    specialize (Hcompl ι (MkEmp _)). pred_unfold.
    rewrite ?inst_lift in Hcompl. specialize (Hcompl eq_refl eq_refl).
    revert Hcompl. apply wp_mono. intros w1 θ1 e1 <-. predsimpl.
  Qed.

  Lemma correct {w} (Γ : Ėnv w) (e : Exp) (τ : Ṫy w) (e' : Ėxp w) :
    Γ |--ₚ e; τ ~> e' ⊣⊢ₚ TPB_algo Γ e τ e'.
  Proof. iSplit. iApply complete. iApply sound. Qed.

End Generator.

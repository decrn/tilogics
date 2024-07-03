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

#[local] Notation "s [ ζ ]" := (subst s ζ)
  (at level 7, left associativity, format "s [ ζ ]").

Section Generator.
  Import MonadNotations.

  (* We would normally like to introduce the typeclass instances using Context,
     but for some reason that causes the fixpoint to stay unfolded in the
     proofs. *)
  Fixpoint ocheck `{lkReflΘ: LkRefl Θ, lkTransΘ: LkTrans Θ, lkStepΘ: LkStep Θ,
    reflTransΘ: !ReflTrans Θ, pureM:Pure M, bindM:Bind Θ M, failM:Fail M,
    tcM:TypeCheckM M} (e : Exp) : ⊧ OEnv ⇢ OTy ⇢ M OExp :=
    fun w Γ τ =>
      match e with
      | exp.var x =>
          match lookup x Γ with
          | Some τ' => _ <- equals τ τ' ;;
                       pure (oexp.var x)
          | None    => fail
          end
      | exp.true  =>
          _ <- equals τ oty.bool ;;
          pure oexp.true
      | exp.false =>
          _ <- equals τ oty.bool ;;
          pure oexp.false
      | exp.ifte e1 e2 e3 =>
          e1' <- ocheck e1 Γ oty.bool ;;
          e2' <- ocheck e2 Γ[_] τ[_] ;;
          e3' <- ocheck e3 Γ[_] τ[_] ;;
          pure (oexp.ifte e1'[_] e2'[_] e3')
      | exp.absu x e =>
          t1  <- pick ;;
          t2  <- pick ;;
          _   <- equals τ[_] (oty.func t1[_] t2) ;;
          e'  <- ocheck e (Γ[_] ,, x∷t1[_]) t2[_] ;;
          pure (oexp.abst x t1[_] e')
      | exp.abst x t1 e =>
          τ2  <- pick ;;
          _   <- equals τ[_] (oty.func (lift t1) τ2) ;;
          e'  <- ocheck e (Γ[_] ,, x∷lift t1) τ2[_] ;;
          pure (oexp.abst x (lift t1) e')
      | exp.app e1 e2 =>
         '(τ2,e2') <- osynth e2 Γ ;;
         e1'       <- ocheck e1 Γ[_] (oty.func τ2 τ[_]) ;;
         pure (oexp.app e1' e2'[_])
      end
  with osynth `{lkReflΘ: LkRefl Θ, lkTransΘ: LkTrans Θ, lkStepΘ: LkStep Θ,
    reflTransΘ: !ReflTrans Θ, pureM:Pure M, bindM:Bind Θ M, failM:Fail M,
    tcM:TypeCheckM M} (e : Exp) : ⊧ OEnv ⇢ M (OTy * OExp) :=
    fun w Γ =>
      match e with
      | exp.var x =>
          match lookup x Γ with
          | Some t => pure (t , oexp.var x)
          | None   => fail
          end
      | exp.true  => pure (oty.bool, oexp.true)
      | exp.false => pure (oty.bool, oexp.false)
      | exp.ifte e1 e2 e3 =>
          e1'        <- ocheck e1 Γ oty.bool ;;
          '(τ,e2')   <- osynth e2 Γ[_] ;;
          e3'        <- ocheck e3 Γ[_] τ ;;
          pure (τ[_], oexp.ifte e1'[_] e2'[_] e3')
      | exp.absu x e =>
          t1         <- pick ;;
          '(t2,e')   <- osynth e (insert (M := OEnv _) x t1 Γ[_]) ;;
          pure (oty.func t1[_] t2, oexp.abst x t1[_] e')
      | exp.abst x t1 e =>
          '(t2,e')   <- osynth e (insert (M := OEnv _) x (lift t1) Γ) ;;
          pure (oty.func (lift t1) t2, oexp.abst x (lift t1) e')
      | exp.app e1 e2 =>
          '(tf, e1') <- osynth e1 Γ ;;
          τ1         <- pick ;;
          τ2         <- pick ;;
          _          <- equals tf[_] (oty.func τ1[_] τ2) ;;
          e2'        <- ocheck e2 Γ[_] τ1[_] ;;
          pure (τ2[_], oexp.app e1'[_] e2')
      end.

  Import Pred Pred.notations Pred.proofmode iris.proofmode.tactics.
  Open Scope pred_scope.

  Context `{lkReflΘ: LkRefl Θ, lkTransΘ: LkTrans Θ, lkStepΘ: LkStep Θ} {reflTransΘ: ReflTrans Θ}.
  Context `{pureM:Pure M, bindM:Bind Θ M, failM:Fail M, tcM:TypeCheckM M}.
  Context {wpM : WeakestPre Θ M} {wlpM : WeakestLiberalPre Θ M}
    {tcLogicM : TypeCheckLogicM Θ M}.

  Definition otyping_algo_synth : ⊧ OEnv ⇢ Const Exp ⇢ OTy ⇢ OExp ⇢ Pred :=
    fun w0 G0 e t0 e0 =>
    WP (osynth e G0)
      (fun w1 (θ1 : Θ w0 w1) '(t1,e1) =>
         t0[θ1] =ₚ t1 /\ₚ e0[θ1] =ₚ e1).
  Notation "Γ |--ₐ e ↓ t ~> e'" := (otyping_algo_synth Γ e t e') (at level 75).

  Goal False. Proof.
  Ltac wlpauto :=
    repeat
      (repeat wpsimpl;
       try
         match goal with
         | H: _ /\ _ |- _ => destruct H
         | IH: forall w G, bi_emp_valid (WLP (osynth ?e G) _)
           |- environments.envs_entails _ (WLP (osynth ?e ?G) _) =>
             iApply (wlp_mono' $! (IH _ G));
             iIntros (?w ?θ) "!>"; iIntros ([?t ?e']) "#?"
         | IH: forall w G τ, bi_emp_valid (WLP (ocheck ?e G τ) _)
           |- environments.envs_entails _ (WLP (ocheck ?e ?G ?τ) _) =>
             iApply (wlp_mono' $! (IH _ G τ));
             iIntros (?w ?θ) "!>"; iIntros (?e') "#?"
         | |- environments.envs_entails _ (TPB _ _ _ _) =>
             predsimpl;
             iStopProof;
             pred_unfold;
             intuition (subst; econstructor; eauto; fail)
         end).
  Ltac wpauto :=
    repeat
      (repeat wpsimpl;
       try
         match goal with
         | H: _ /\ _ |- _ => destruct H
         | IH: forall (w : World) (G : OEnv w) (t : OTy w),
             bi_emp_valid (bi_impl _ (bi_impl _ (WP (ocheck ?e G t) _)))
             |- environments.envs_entails _ (WP (ocheck ?e ?G ?t) _) =>
             iPoseProof (IH _ G t with "[] []") as "-#IH"; clear IH;
             [ | | iApply (wp_mono' with "IH");
                   iIntros (?w ?θ) "!>"; iIntros (?e') "#?"
             ]
         | IH: forall _ G,
             bi_emp_valid (bi_impl _ (WP (osynth ?e G) _))
             |- environments.envs_entails _ (WP (osynth ?e ?G) _) =>
             iPoseProof (IH _ G with "[]") as "-#IH"; clear IH;
             [| iApply (wp_mono' with "IH");
                iIntros (?w ?θ) "!>";
                iIntros ((?t & ?e')) "(#? & #?)"
             ]
         end).
  Abort.

  Lemma osoundness_aux e :
    (∀ w (G : OEnv w) (t : OTy w),
        ⊢ WLP (ocheck e G t) (fun _ θ ee => G[θ] |--ₚ e; t[θ] ~> ee)) /\
    (∀ w (G : OEnv w),
        ⊢ WLP (osynth e G) (fun _ θ '(t,ee) => G[θ] |--ₚ e; t ~> ee)).
  Proof.
    induction e; cbn; (split; [intros w G τ|intros w G]); iStartProof; wlpauto.
    - destruct lookup eqn:HGx; wlpauto. iStopProof; pred_unfold.
      intros ->. constructor. now rewrite lookup_inst HGx.
    - destruct lookup eqn:HGx; wlpauto. iStopProof; pred_unfold.
      constructor. now rewrite lookup_inst HGx.
  Qed.

  Lemma osoundness (e : Exp) (w0 : World) (G0 : OEnv w0) t0 e0 :
    G0 |--ₐ e ↓ t0 ~> e0  ⊢ₚ  G0 |--ₚ e; t0 ~> e0.
  Proof.
    iStartProof. rewrite wand_is_impl. iApply wp_impl.
    destruct (@osoundness_aux e) as [_ Hsound].
    iApply (wlp_mono' $! (@Hsound w0 G0)).
    iIntros "%w1 %θ1 !>" ([t e']) "HT". predsimpl.
    iStopProof; pred_unfold. intros HT Heq1 Heq2. now subst.
  Qed.

  Lemma ocompleteness_aux {G e t ee} (T : G |-- e ∷ t ~> ee) :
    (∀ w0 (G0 : OEnv w0) (t0 : OTy w0),
      ⊢ lift G =ₚ G0 ->ₚ lift t =ₚ t0 ->ₚ
        WP (ocheck e G0 t0) (fun _ _ e' => Open.pure ee =ₚ e')%P) /\
    (∀ w0 (G0 : OEnv w0),
      ⊢ lift G =ₚ G0 →
        WP (osynth e G0) (fun _ _ '(t',e') => lift t =ₚ t' /\ₚ Open.pure ee =ₚ e')%P).
  Proof.
    induction T; cbn; (split; [intros ? G0 ?|intros ? G0]); iStartProof; wpauto.
    - destruct (G0 !! _) eqn:HGx; wpauto.
      + iApply wp_equals. iSplit.
        * iStopProof; pred_unfold. intros ? [-> ->].
          rewrite lookup_inst HGx in H. now injection H.
        * iIntros (?w ?θ) "!>"; wpauto.
      + iStopProof; pred_unfold. intros ? []. subst.
        rewrite lookup_inst HGx in H. now discriminate H.
    - destruct (G0 !! _) eqn:HGx; wpauto; iStopProof; pred_unfold;
        intros ? ->; rewrite lookup_inst HGx in H; cbn in H; congruence.
  Qed.

  Lemma ocompleteness (e : Exp) (w0 : World) (G0 : OEnv w0) t0 e0 :
    G0 |--ₚ e; t0 ~> e0  ⊢ₚ  G0 |--ₐ e ↓ t0 ~> e0.
  Proof.
    pred_unfold. intros ι HT. destruct (ocompleteness_aux HT) as [_ Hcompl].
    specialize (Hcompl _ G0). destruct Hcompl as [Hcompl].
    specialize (Hcompl ι (MkEmp _)). pred_unfold. rewrite inst_lift in Hcompl.
    specialize (Hcompl eq_refl). revert Hcompl. apply wp_mono.
    intros w1 θ1 ι1 <- [τ1 e1]. pred_unfold.
  Qed.

  Lemma ocorrectness {w} (Γ : OEnv w) (e : Exp) (τ : OTy w) (e' : OExp w) :
    Γ |--ₚ e; τ ~> e'  ⊣⊢ₚ  Γ |--ₐ e ↓ τ ~> e'.
  Proof. iSplit. iApply ocompleteness. iApply osoundness. Qed.

End Generator.

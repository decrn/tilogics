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

  Definition generate : Exp -> ⊧ Ėnv ⇢ M (Ṫy * Ėxp) :=
    fix gen e {w} Γ :=
      match e with
      | exp.var x =>
          match lookup x Γ with
          | Some t => pure (t , ėxp.var x)
          | None   => fail
          end
      | exp.true  => pure (ṫy.bool, ėxp.true)
      | exp.false => pure (ṫy.bool, ėxp.false)
      | exp.ifte e1 e2 e3 =>
          '(t1,e1') <- gen e1 Γ ;;
          '(t2,e2') <- gen e2 Γ[_] ;;
          '(t3,e3') <- gen e3 Γ[_] ;;
          _         <- assert ṫy.bool t1[_] ;;
          _         <- assert t2[_] t3[_] ;;
          pure (t3[_], ėxp.ifte e1'[_] e2'[_] e3'[_])
      | exp.absu x e =>
          t1       <- pick ;;
          '(t2,e') <- gen e (insert (M := Ėnv _) x t1 Γ[_]) ;;
          pure (ṫy.func t1[_] t2, ėxp.abst x t1[_] e')
      | exp.abst x t1 e =>
          '(t2,e') <- gen e (insert (M := Ėnv _) x (lift t1) Γ) ;;
          pure (ṫy.func (lift t1) t2, ėxp.abst x (lift t1) e')
      | exp.app e1 e2 =>
          '(tf, e1') <- gen e1 Γ ;;
          '(t1, e2') <- gen e2 Γ[_] ;;
          t2 <- pick ;;
          _  <- assert tf[_] (ṫy.func t1[_] t2) ;;
          pure (t2[_], ėxp.app e1'[_] e2'[_])
      end.

  Import Pred Pred.notations.
  Import Pred.proofmode.
  Import iris.proofmode.tactics.
  Open Scope pred_scope.

  Context {wpM : WeakestPre Θ M} {wlpM : WeakestLiberalPre Θ M}
    {tcLogicM : TypeCheckLogicM Θ M}.

  Definition TPB_algo : ⊧ Ėnv ⇢ Const Exp ⇢ Ṫy ⇢ Ėxp ⇢ Pred :=
    fun w0 G0 e t0 e0 =>
    WP (generate e G0)
      (fun w1 (θ1 : Θ w0 w1) '(t1,e1) =>
         t0[θ1] =ₚ t1 /\ₚ e0[θ1] =ₚ e1).

  Ltac wlpindhyp :=
    match goal with
    | IH: ∀ w G, bi_emp_valid (WLP (generate ?e G) _)
      |- environments.envs_entails _ (WLP (generate ?e ?G) _) =>
        iApply (wlp_mono' $! (IH _ G));
        iIntros (?w ?θ) "!>"; iIntros ([?t ?e']) "#?"; clear IH
    | |- environments.envs_entails _ (TPB _ _ _ _) =>
        iStopProof; pred_unfold;
        intuition (subst; econstructor; eauto; fail)
    end.
  Ltac wlpauto := repeat (repeat wpsimpl; try wlpindhyp).

  Lemma generate_sound_aux e :
    ∀ w (G : Ėnv w),
      ⊢ WLP (generate e G) (fun _ θ '(t,ee) => G[θ] |--ₚ e; t ~> ee).
  Proof.
    induction e; cbn; intros w G; iStartProof; wlpauto.
    destruct lookup eqn:HGx; wlpauto. iStopProof; pred_unfold.
    constructor. now rewrite lookup_inst HGx.
  Qed.

  Lemma generate_sound (e : Exp) {w0} (G0 : Ėnv w0) t0 e0 :
    TPB_algo G0 e t0 e0 ⊢ₚ G0 |--ₚ e; t0 ~> e0.
  Proof.
    iStartProof. rewrite wand_is_impl. iApply wp_impl.
    iApply (wlp_mono' $! (@generate_sound_aux e w0 G0)).
    iIntros "%w1 %θ1 !>" ([t e']) "HT". iStopProof; pred_unfold.
    intros HT [Heq1 Heq2]. now subst.
  Qed.

  Ltac wpindhyp :=
    match goal with
    | IH: forall _ G,
        bi_emp_valid (bi_impl _ (WP (generate ?e G) _))
      |- environments.envs_entails _ (WP (generate ?e ?G) _) =>
        iPoseProof (IH _ G with "[]") as "-#IH"; clear IH;
        [| iApply (wp_mono' with "IH");
           iIntros (?w ?θ) "!>";
           iIntros ((?t & ?e')) "(#? & #?)"
        ]
    end.
  Ltac wpauto := repeat (repeat wpsimpl; try wpindhyp).

  Lemma generate_complete_aux {G e t ee} (T : G |-- e ∷ t ~> ee) :
    ∀ w0 (G0 : Ėnv w0), ⊢ lift G =ₚ G0 →
      WP (generate e G0)
          (fun _ _ '(t',e') => lift t =ₚ t' /\ₚ Open.pure ee =ₚ e')%P.
  Proof.
    induction T; cbn; intros w0 G0; iStartProof; wpauto.
    destruct (G0 !! x) eqn:HGx; wpauto; iStopProof; pred_unfold;
      intros ? ->; rewrite lookup_inst HGx in H; cbn in H; congruence.
  Qed.

  Lemma generate_complete {w} (Γ : Ėnv w) (e : Exp) (τ : Ṫy w) (e' : Ėxp w) :
    Γ |--ₚ e; τ ~> e' ⊢ₚ TPB_algo Γ e τ e'.
  Proof.
    pred_unfold. intros ι HT.
    destruct (generate_complete_aux HT Γ) as [Hcompl].
    specialize (Hcompl ι (MkEmp _)). pred_unfold.
    rewrite inst_lift in Hcompl.
    specialize (Hcompl eq_refl). revert Hcompl.
    apply wp_mono. intros w1 θ1 ι1 <- [τ1 e1].
    pred_unfold.
  Qed.

  Lemma generate_correct {w} (Γ : Ėnv w) (e : Exp) (τ : Ṫy w) (e' : Ėxp w) :
    Γ |--ₚ e; τ ~> e' ⊣⊢ₚ TPB_algo Γ e τ e'.
  Proof. iSplit. iApply generate_complete. iApply generate_sound. Qed.

End Generator.

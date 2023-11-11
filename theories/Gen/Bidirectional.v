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

  Context `{lkReflΘ: LkRefl Θ, lkTransΘ: LkTrans Θ, lkStepΘ: LkStep Θ}
    {reflTransΘ: ReflTrans Θ}.
  Context `{pureM:Pure M, bindM:Bind Θ M, failM:Fail M, tcM:TypeCheckM M}.

  Fixpoint check (e : Exp) : ⊧ Ėnv ⇢ Ṫy ⇢ M Ėxp :=
    fun w Γ τ =>
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
          e1' <- check e1 Γ ṫy.bool ;;
          e2' <- check e2 Γ[_] τ[_] ;;
          e3' <- check e3 Γ[_] τ[_] ;;
          pure (ėxp.ifte e1'[_] e2'[_] e3')
      | exp.absu x e =>
          t1  <- pick ;;
          t2  <- pick ;;
          _   <- assert τ[_] (ṫy.func t1[_] t2) ;;
          e'  <- check e (Γ[_] ,, x∷t1[_]) t2[_] ;;
          pure (ėxp.abst x t1[_] e')
      | exp.abst x t1 e =>
          τ2  <- pick ;;
          _   <- assert τ[_] (ṫy.func (lift t1) τ2) ;;
          e'  <- check e (Γ[_] ,, x∷lift t1) τ2[_] ;;
          pure (ėxp.abst x (lift t1) e')
      | exp.app e1 e2 =>
         '(τ2,e2') <- synth e2 Γ ;;
         e1'       <- check e1 Γ[_] (ṫy.func τ2 τ[_]) ;;
         pure (ėxp.app e1' e2'[_])
      end
  with synth (e : Exp) : ⊧ Ėnv ⇢ M (Ṫy * Ėxp) :=
    fun w Γ =>
      match e with
      | exp.var x =>
          match lookup x Γ with
          | Some t => pure (t , ėxp.var x)
          | None   => fail
          end
      | exp.true  => pure (ṫy.bool, ėxp.true)
      | exp.false => pure (ṫy.bool, ėxp.false)
      | exp.ifte e1 e2 e3 =>
          e1'        <- check e1 Γ ṫy.bool ;;
          '(τ,e2')   <- synth e2 Γ[_] ;;
          e3'        <- check e3 Γ[_] τ ;;
          pure (τ[_], ėxp.ifte e1'[_] e2'[_] e3')
      | exp.absu x e =>
          t1         <- pick ;;
          '(t2,e')   <- synth e (insert (M := Ėnv _) x t1 Γ[_]) ;;
          pure (ṫy.func t1[_] t2, ėxp.abst x t1[_] e')
      | exp.abst x t1 e =>
          '(t2,e')   <- synth e (insert (M := Ėnv _) x (lift t1) Γ) ;;
          pure (ṫy.func (lift t1) t2, ėxp.abst x (lift t1) e')
      | exp.app e1 e2 =>
          '(tf, e1') <- synth e1 Γ ;;
          τ1         <- pick ;;
          τ2         <- pick ;;
          _          <- assert tf[_] (ṫy.func τ1[_] τ2) ;;
          e2'        <- check e2 Γ[_] τ1[_] ;;
          pure (τ2[_], ėxp.app e1'[_] e2')
      end.

  Import Pred Pred.notations.
  Import Pred.proofmode.
  Import iris.proofmode.tactics.
  Open Scope pred_scope.

  Context {wpM : WeakestPre Θ M} {wlpM : WeakestLiberalPre Θ M}
    {tcLogicM : TypeCheckLogicM Θ M}.

  Definition TPB_algo : ⊧ Ėnv ⇢ Const Exp ⇢ Ṫy ⇢ Ėxp ⇢ Pred :=
    fun w0 G0 e t0 e0 =>
    WP (synth e G0)
      (fun w1 (θ1 : Θ w0 w1) '(t1,e1) =>
         t0[θ1] =ₚ t1 /\ₚ e0[θ1] =ₚ e1).

  Ltac wlpauto :=
    repeat
      (repeat wpsimpl;
       try
         match goal with
         | H: _ /\ _ |- _ => destruct H
         | IH: forall w G, bi_emp_valid (WLP (synth ?e G) _)
           |- environments.envs_entails _ (WLP (synth ?e ?G) _) =>
             iApply (wlp_mono' $! (IH _ G));
             iIntros (?w ?θ) "!>"; iIntros ([?t ?e']) "#?"
         | IH: forall w G τ, bi_emp_valid (WLP (check ?e G τ) _)
           |- environments.envs_entails _ (WLP (check ?e ?G ?τ) _) =>
             iApply (wlp_mono' $! (IH _ G τ));
             iIntros (?w ?θ) "!>"; iIntros (?e') "#?"
         | |- environments.envs_entails _ (TPB _ _ _ _) =>
             predsimpl;
             iStopProof;
             pred_unfold;
             intuition (subst; econstructor; eauto; fail)
         end).

  Lemma sound_aux e :
      (∀ w (G : Ėnv w) (t : Ṫy w),
          ⊢ WLP (check e G t) (fun _ θ ee => G[θ] |--ₚ e; t[θ] ~> ee)) /\
      (∀ w (G : Ėnv w),
          ⊢ WLP (synth e G) (fun _ θ '(t,ee) => G[θ] |--ₚ e; t ~> ee)).
  Proof.
    induction e; cbn; (split; [intros w G τ|intros w G]); iStartProof; wlpauto.
    - destruct lookup eqn:HGx; wlpauto. iStopProof; pred_unfold.
      intros ->. constructor. now rewrite lookup_inst HGx.
    - destruct lookup eqn:HGx; wlpauto. iStopProof; pred_unfold.
      constructor. now rewrite lookup_inst HGx.
  Qed.

  Lemma sound (e : Exp) (w0 : World) (G0 : Ėnv w0) t0 e0 :
    TPB_algo G0 e t0 e0 ⊢ₚ G0 |--ₚ e; t0 ~> e0.
  Proof.
    iStartProof. rewrite wand_is_impl. iApply wp_impl.
    destruct (@sound_aux e) as [_ Hsound].
    iApply (wlp_mono' $! (@Hsound w0 G0)).
    iIntros "%w1 %θ1 !>" ([t e']) "HT". predsimpl.
    iStopProof; pred_unfold. intros HT Heq1 Heq2. now subst.
  Qed.

  Ltac wpauto :=
    repeat
      (repeat wpsimpl;
       try
         match goal with
         | H: _ /\ _ |- _ => destruct H
         | IH: forall (w : World) (G : Ėnv w) (t : Ṫy w),
             bi_emp_valid (bi_impl _ (bi_impl _ (WP (check ?e G t) _)))
             |- environments.envs_entails _ (WP (check ?e ?G ?t) _) =>
             iPoseProof (IH _ G t with "[] []") as "-#IH"; clear IH;
             [ | | iApply (wp_mono' with "IH");
                   iIntros (?w ?θ) "!>"; iIntros (?e') "#?"
             ]
         | IH: forall _ G,
             bi_emp_valid (bi_impl _ (WP (synth ?e G) _))
             |- environments.envs_entails _ (WP (synth ?e ?G) _) =>
             iPoseProof (IH _ G with "[]") as "-#IH"; clear IH;
             [| iApply (wp_mono' with "IH");
                iIntros (?w ?θ) "!>";
                iIntros ((?t & ?e')) "(#? & #?)"
             ]
         end).

  Lemma complete_aux {G e t ee} (T : G |-- e ∷ t ~> ee) :
    (∀ w0 (G0 : Ėnv w0) (t0 : Ṫy w0),
      ⊢ lift G =ₚ G0 ->ₚ lift t =ₚ t0 ->ₚ
        WP (check e G0 t0) (fun _ _ e' => Open.pure ee =ₚ e')%P) /\
    (∀ w0 (G0 : Ėnv w0),
      ⊢ lift G =ₚ G0 →
        WP (synth e G0) (fun _ _ '(t',e') => lift t =ₚ t' /\ₚ Open.pure ee =ₚ e')%P).
  Proof.
    induction T; cbn; (split; [intros ? G0 ?|intros ? G0]); iStartProof; wpauto.
    - destruct (G0 !! _) eqn:HGx; wpauto.
      + iApply wp_assert. iSplit.
        * iStopProof; pred_unfold. intros ? [-> ->].
          rewrite lookup_inst HGx in H. now injection H.
        * iIntros (?w ?θ) "!>"; wpauto.
      + iStopProof; pred_unfold. intros ? []. subst.
        rewrite lookup_inst HGx in H. now discriminate H.
    - destruct (G0 !! _) eqn:HGx; wpauto; iStopProof; pred_unfold;
        intros ? ->; rewrite lookup_inst HGx in H; cbn in H; congruence.
  Qed.

  Lemma complete (e : Exp) (w0 : World) (G0 : Ėnv w0) t0 e0 :
    G0 |--ₚ e; t0 ~> e0 ⊢ₚ TPB_algo G0 e t0 e0.
  Proof.
    pred_unfold. intros ι HT.
    destruct (complete_aux HT) as [_ Hcompl].
    specialize (Hcompl _ G0). destruct Hcompl as [Hcompl].
    specialize (Hcompl ι (MkEmp _)). pred_unfold.
    rewrite inst_lift in Hcompl.
    specialize (Hcompl eq_refl). revert Hcompl.
    apply wp_mono. intros w1 θ1 ι1 <- [τ1 e1].
    pred_unfold.
  Qed.

  Lemma correct {w} (Γ : Ėnv w) (e : Exp) (τ : Ṫy w) (e' : Ėxp w) :
    Γ |--ₚ e; τ ~> e' ⊣⊢ₚ TPB_algo Γ e τ e'.
  Proof. iSplit. iApply complete. iApply sound. Qed.

End Generator.

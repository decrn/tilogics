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

  Context `{lkReflΘ: LkRefl Θ, lkTransΘ: LkTrans Θ, lkStepΘ: LkStep Θ}
    {reflTransΘ: ReflTrans Θ}.
  Context `{pureM:Pure M, bindM:Bind Θ M, failM:Fail M, tcM:TypeCheckM M}.

  Definition osynth : Exp -> ⊧ OEnv ⇢ M (OTy * OExp) :=
    fix osynth e {w} Γ :=
      match e with
      | exp.var x =>
          match lookup x Γ with
          | Some t => pure (t , oexp.var x)
          | None   => fail
          end
      | exp.true  => pure (oty.bool, oexp.true)
      | exp.false => pure (oty.bool, oexp.false)
      | exp.ifte e1 e2 e3 =>
          '(t1,e1') <- osynth e1 Γ ;;
          '(t2,e2') <- osynth e2 Γ[_] ;;
          '(t3,e3') <- osynth e3 Γ[_] ;;
          _         <- equals oty.bool t1[_] ;;
          _         <- equals t2[_] t3[_] ;;
          pure (t3[_], oexp.ifte e1'[_] e2'[_] e3'[_])
      | exp.absu x e =>
          t1       <- pick ;;
          '(t2,e') <- osynth e (insert (M := OEnv _) x t1 Γ[_]) ;;
          pure (oty.func t1[_] t2, oexp.abst x t1[_] e')
      | exp.abst x t1 e =>
          '(t2,e') <- osynth e (insert (M := OEnv _) x (lift t1) Γ) ;;
          pure (oty.func (lift t1) t2, oexp.abst x (lift t1) e')
      | exp.app e1 e2 =>
          '(tf, e1') <- osynth e1 Γ ;;
          '(t1, e2') <- osynth e2 Γ[_] ;;
          t2 <- pick ;;
          _  <- equals tf[_] (oty.func t1[_] t2) ;;
          pure (t2[_], oexp.app e1'[_] e2'[_])
      end.

  Import Pred Pred.notations Pred.proofmode iris.proofmode.tactics.
  Open Scope pred_scope.

  Context {wpM : WeakestPre Θ M} {wlpM : WeakestLiberalPre Θ M}
    {tcLogicM : TypeCheckLogicM Θ M}.

  Definition otyping_algo : ⊧ OEnv ⇢ Const Exp ⇢ OTy ⇢ OExp ⇢ Pred :=
    fun w0 G0 e t0 e0 =>
    WP (osynth e G0)
      (fun w1 (θ1 : Θ w0 w1) '(t1,e1) =>
         t0[θ1] =ₚ t1 /\ₚ e0[θ1] =ₚ e1).
  Notation "Γ |--ₐ e ∷ t ~> e'" := (otyping_algo Γ e t e') (at level 75).

  Goal False. Proof.
  Ltac wlpindhyp :=
    match goal with
    | IH: ∀ w G, bi_emp_valid (WLP (osynth ?e G) _)
      |- environments.envs_entails _ (WLP (osynth ?e ?G) _) =>
        iApply (wlp_mono' $! (IH _ G));
        iIntros (?w ?θ) "!>"; iIntros ([?t ?e']) "#?"; clear IH
    | |- environments.envs_entails _ (TPB _ _ _ _) =>
        iStopProof; pred_unfold;
        intuition (subst; econstructor; eauto; fail)
    end.
  Ltac wlpauto := repeat (repeat wpsimpl; try wlpindhyp).
  Ltac wpindhyp :=
    match goal with
    | IH: forall _ G,
        bi_emp_valid (bi_impl _ (WP (osynth ?e G) _))
      |- environments.envs_entails _ (WP (osynth ?e ?G) _) =>
        iPoseProof (IH _ G with "[]") as "-#IH"; clear IH;
        [| iApply (wp_mono' with "IH");
           iIntros (?w ?θ) "!>";
           iIntros ((?t & ?e')) "(#? & #?)"
        ]
    end.
  Ltac wpauto := repeat (repeat wpsimpl; try wpindhyp).
  Abort.

  Lemma osoundness_aux e :
    ∀ w (G : OEnv w),
      ⊢ WLP (osynth e G) (fun _ θ '(t,ee) => G[θ] |--ₚ e; t ~> ee).
  (* Proof with
    iStopProof; pred_unfold; intuition (subst; econstructor; eauto; fail).
    induction e; cbn; intros w G; iStartProof.
    - destruct lookup eqn:HGx; wlpauto.
      iStopProof; pred_unfold. constructor. now rewrite lookup_inst HGx.
    - iApply wlp_pure...
    - iApply wlp_pure...
    - iApply wlp_bind.
      wlpindhyp.
      iApply wlp_bind.
      wlpindhyp.
      iApply wlp_bind.
      wlpindhyp.
      iApply wlp_bind.
      iApply wlp_equals.
      (* Assume that the equality holds on the ghost state (assignment). *)
      iIntros "#?".
      (* The rule for equality is generalized with the ◼ modality to *)
      (* allow different behaviour from the monad. The Free monad implementation *)
      (* of equals always calls the continuation with the identity substitution. *)
      (* However, the solved monad calls the unifier and hence the continuation *)
      (* is called with some substitution that we cannot know upfront. Of course, *)
      (* we do not want to make the unifier part of the semantics of the wlp rule *)
      (* for equals either. Hence the use of the ◼ modality that requires us to *)
      (* show the postcondition for any substitution. *)
      unfold PBox.  (* PBox is defined using Sub.wlp. *)
      iIntros (?w ?θ).
      (* Introduce the wlp from the head by running the substitution *)
      (* over the context. *)
      iModIntro.
      (* The modality introduction uses typeclass-based logic programming to *)
      (* perform some rewrites. For instance, the barebones modality introduction *)
      (* of the wlp would result in the last assumption to be the constraint *)
      (*   (oty.bool =ₚ t[θ0 ⊙ θ1])[θ2] *)
      (* but the typeclass machinery automatically "rewrote" it to *)
      (*   oty.bool[θ2] =ₚ t[θ0 ⊙ θ1][θ2] *)
      (* Similarly, for the typing judgements. *)
      iApply wlp_bind.
      iApply wlp_equals. iIntros "#?". iIntros (?w ?θ) "!>".
      iApply wlp_pure...
    - iApply wlp_bind.
      iApply wlp_pick. iIntros (?w ?θ) "!>". iIntros (?τ).
      iApply wlp_bind.
      wlpindhyp.
      iApply wlp_pure...
    - iApply wlp_bind.
      wlpindhyp.
      iApply wlp_pure...
    - iApply wlp_bind.
      wlpindhyp.
      iApply wlp_bind.
      wlpindhyp.
      iApply wlp_bind.
      iApply wlp_pick. iIntros (?w ?θ) "!>". iIntros (?τ).
      iApply wlp_bind.
      iApply wlp_equals. iIntros "#?". iIntros (?w ?θ) "!>".
      iApply wlp_pure.
      (* Unfortunately, we are accumulating a lot of substitutions in the goal. *)
      (* We can make the output nicer through generalizations. *)
      rewrite ?subst_trans; predsimpl.
      (* The subst_trans doesn't work for the elaboration because that would *)
      (* need either functional extensionality or a generalized rewrite *)
      (* At this point we would like to apply the typing relation for the *)
      (* application case. However, we did not define it for the open typing *)
      (* relation. So at this point we the "base logic" abstraction and go to *)
      (* the underlying definition of predicates and also to the closed typing *)
      (* relation that underlies the open typing relation. We can generalize *)
      (* the result further to get rid of more substitutions. *)
      iStopProof. pred_unfold.
      (* Use the typing rule of the closed typing relation. *)
      intuition (subst; econstructor; eauto; fail).
  Restart. *)
  Proof.
    induction e; cbn; intros w G; iStartProof; wlpauto.
    destruct lookup eqn:HGx; wlpauto. iStopProof; pred_unfold.
    constructor. now rewrite lookup_inst HGx.
  Qed.

  Lemma osoundness (e : Exp) {w} (Γ : OEnv w) τ e' :
    Γ |--ₐ e ∷ τ ~> e'  ⊢ₚ  Γ |--ₚ e; τ ~> e'.
  Proof.
    iStartProof. rewrite wand_is_impl. iApply wp_impl.
    iApply (wlp_mono' $! (@osoundness_aux e w Γ)).
    iIntros "%w1 %θ1 !>" ([τ' e'']) "HT". iStopProof; pred_unfold.
    intros HT [Heq1 Heq2]. now subst.
  Qed.

  Lemma ocompleteness_aux {G e t ee} (T : G |-- e ∷ t ~> ee) :
    ∀ w0 (G0 : OEnv w0), ⊢ lift G =ₚ G0 →
      WP (osynth e G0)
          (fun _ _ '(t',e') => lift t =ₚ t' /\ₚ Open.pure ee =ₚ e')%P.
  Proof.
    induction T; cbn; intros w0 G0; iStartProof; wpauto.
    destruct (G0 !! x) eqn:HGx; wpauto; iStopProof; pred_unfold;
      intros ? ->; rewrite lookup_inst HGx in H; cbn in H; congruence.
  Qed.

  Lemma ocompleteness {w} (Γ : OEnv w) (e : Exp) (τ : OTy w) (e' : OExp w) :
    Γ |--ₚ e; τ ~> e'  ⊢ₚ  Γ |--ₐ e ∷ τ ~> e'.
  Proof.
    pred_unfold. intros ι HT.
    destruct (ocompleteness_aux HT Γ) as [Hcompl].
    specialize (Hcompl ι (MkEmp _)). pred_unfold.
    rewrite inst_lift in Hcompl.
    specialize (Hcompl eq_refl). revert Hcompl.
    apply wp_mono. intros w1 θ1 ι1 <- [τ1 e1].
    pred_unfold.
  Qed.

  Lemma ocorrectness {w} (Γ : OEnv w) (e : Exp) (τ : OTy w) (e' : OExp w) :
    Γ |--ₚ e; τ ~> e'  ⊣⊢ₚ  Γ |--ₐ e ∷ τ ~> e'.
  Proof. iSplit. iApply ocompleteness. iApply osoundness. Qed.

End Generator.

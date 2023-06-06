
Module CandidateType.

  Import World.notations.

  #[local] Set Implicit Arguments.
  #[local] Arguments step : simpl never.

  Section Check.
    Import World.notations.

    #[local] Notation "[ ω ] x <- ma ;; mb" :=
      (bind (R := Alloc) ma (fun _ ω x => mb))
        (at level 80, x at next level,
          ma at next level, mb at level 200,
          right associativity).

    #[local] Notation "∃ n , m" :=
      (Bind_Exists_Free _ _ n m)
        (at level 80, right associativity, format "∃ n ,  m").

    #[local] Notation "t1 == t2 //\ m" := (Bind_AssertEq_Free _ _ t1 t2 m) (at level 70).

    Fixpoint check (e : expr) : ⊢ʷ Env -> Ty -> FreeM Unit :=
      fun w G tr =>
        match e with
        | v_true => Bind_AssertEq_Free Unit w (Ty_bool w) tr (Ret_Free Unit w tt)
        | v_false => Bind_AssertEq_Free Unit w (Ty_bool w) tr (Ret_Free Unit w tt)
        | e_if e0 e1 e2 =>
          [r1] _ <- check e0 G (Ty_bool w)   ;;
          [r2] _ <- check e1 G[r1] tr[r1] ;;
          check e2 G[r1 ⊙ r2] tr[r1 ⊙ r2]
        | e_var s =>
          match resolve s G with
          | Some a => Bind_AssertEq_Free Unit w tr a (Ret_Free Unit w tt)
          | None => Fail_Free Unit w
          end
        | e_absu s e0 =>
          ∃1, ∃2,
            let tr' := tr[step ⊙ step] in
            let α1  := Ty_hole _ 1 (ctx.in_succ ctx.in_zero) in
            let α2  := Ty_hole _ 2 ctx.in_zero in
            Ty_func _ α1 α2 == tr' //\
            check e0 ((s, α1) :: G[step ⊙ step]) α2

        | e_abst s t e0 =>
          ∃2,
            let tr' := <{ tr ~ step }> in
            let α1  := lift t (w ▻ 2) in
            let α2  := Ty_hole (w ▻ 2) 2 ctx.in_zero in
            Ty_func (w ▻ 2) α1 α2 == tr' //\
            check e0 ((s, α1) :: <{ G ~ step }>) α2
        | e_app e0 e1 =>
          ∃0,
            let α := Ty_hole (w ▻ 0) 0 ctx.in_zero in
            [r1] _ <- check e0 <{ G ~ step }> (Ty_func _ α <{ tr ~ step }>) ;;
                      check e1 G[step ⊙ r1] <{ α ~ r1 }>
    end.

  End Check.

  Import Pred Pred.notations.
  Import (hints) Sub.
  Import ProgramLogic Pred.proofmode.
  Import iris.proofmode.tactics.
  Open Scope pred_scope.

  Lemma soundness (e : expr) :
    forall (w : World) (G : Env w) (tr : Ty w),
      ⊢ WLP _ (check e G tr) (fun w1 r1 _ => ∃ₚ ee : Expr w1, G[r1] |--ₚ e; tr[r1] ~> ee).
  Proof.
    induction e; cbn; intros w G tr; unfold T, _4; wsimpl.
    - constructor. intros ι. pred_unfold.
      exists (S.pure v_true). constructor.
    - constructor. intros ι. pred_unfold.
      exists (S.pure v_false). constructor.
    - rewrite wlp_bind. unfold _4.
      iPoseProof (IHe1 w G (Ty_bool w)) as "-#IH1". iRevert "IH1". clear IHe1.
      iApply wlp_mono. iIntros (w1 r1 _). iIntros "!> [%e1' HT1]".

      rewrite wlp_bind. unfold _4.
      iPoseProof (IHe2 w1 G[r1] tr[r1]) as "-#IH2". iRevert "IH2". clear IHe2.
      iApply wlp_mono. iIntros (w2 r2 _). iIntros "!> [%e2' HT2]".

      iPoseProof (IHe3 w2 G[r1 ⊙ r2] tr[r1 ⊙ r2]) as "-#IH3". iRevert "IH3". clear IHe3.
      iApply wlp_mono. iIntros (w3 r3 _). iIntros "!> [%e3' HT3]".
      wsimpl.

      iExists (fun ι => e_if (e1' ι) (e2' ι) (e3' ι)).
      iStopProof. constructor. intros ι (IH1 & IH2 & IH3). now constructor.
    - destruct resolve eqn:?; wsimpl.
      constructor. intros ι; pred_unfold.
      exists (S.pure (e_var s)).
      constructor. now rewrite resolve_inst Heqo.
    - iIntros "!> !> Heq1".
      iPoseProof (IHe (w ▻ 1 ▻ 2)
                      ((s, Ty_hole (w ▻ 1 ▻ 2) 1 (ctx.in_succ ctx.in_zero)) :: G[step][step])
                      (Ty_hole (w ▻ 1 ▻ 2) 2 ctx.in_zero)) as "-#IH". iRevert "IH". clear IHe.
      iApply wlp_mono. iIntros (w1 r1 _).
      iIntros "!> [%e' HT]". wsimpl.
      iExists (fun ι => e_abst s (inst (lk r1 (ctx.in_succ ctx.in_zero)) ι) (e' ι)).
      iStopProof. constructor. intros ι (Heq & IH). pred_unfold. now constructor.
    - iIntros "!> Heq".
      iPoseProof (IHe (w ▻ 2)
                    ((s, lift t (w ▻ 2)) :: G[step])
                    (Ty_hole (w ▻ 2) 2 ctx.in_zero))
                      as "-#IH". iRevert "IH". clear IHe.
      iApply wlp_mono. iIntros (w1 r1 _).
      iIntros "!> [%e' HT]". wsimpl.
      generalize (lk r1 ctx.in_zero). clear w r1. intros t2.
      iExists (fun ι => e_abst s t (e' ι)).
      iStopProof. constructor. intros ι (Heq & IH). pred_unfold. now constructor.
    - iIntros "!>".

      rewrite wlp_bind. unfold _4.
      iPoseProof (IHe1 (w ▻ 0) G[step] (Ty_func (w ▻ 0) (Ty_hole (w ▻ 0) 0 ctx.in_zero) tr[step]))
        as "-#IH". iRevert "IH". clear IHe1.
      iApply wlp_mono. iIntros (w1 r1 _). iIntros "!> [%e1' HT1]".

      iPoseProof (IHe2 w1 G[step ⊙ r1] (lk r1 ctx.in_zero)) as "-#IH". iRevert "IH". clear IHe2.
      iApply wlp_mono. iIntros (w2 r2 _). iIntros "!> [%e2' HT2]". wsimpl.
      generalize (lk r1 ctx.in_zero)[r2]. clear w r1. intros t1.
      iExists (fun ι => e_app (e1' ι) (e2' ι)).
      iStopProof. constructor. intros ι (H1 & H2). pred_unfold.
      econstructor; eauto.
  Qed.

  Lemma completeness_aux {G e t ee} (T : G |-- e; t ~> ee) :
    forall w0 (G0 : Env w0) (t0 : Ty w0),
      ⊢ liftEnv G _ =ₚ G0 → lift t _ =ₚ t0 → WP _ (check e G0 t0) (fun _ _ _ => Trueₚ)%P.
  Proof.
    induction T; intros w0 G0 t0; wsimpl.
    - iIntros "#HeqG #Heqt". rewrite wp_bind.
      iPoseProof (IHT1 w0 G0 (Ty_bool w0) with "HeqG") as "-#IHT1".
      clear IHT1. wsimpl.
      iRevert "IHT1". iApply wp_mono. iIntros (w1 r1 _). wsimpl.
      iModIntro. wsimpl. rewrite wp_bind.
      iPoseProof (IHT2 w1 G0[r1] t0[r1] with "HeqG Heqt") as "-#IHT2".
      iRevert "IHT2". iApply wp_mono. iIntros (w2 r2 _). wsimpl.
      iModIntro. wsimpl. unfold _4.
      iApply IHT3; wsimpl.
    - constructor. intros ι. intros _ HeqG Heqt. cbn in *.
      rewrite inst_lift_env in HeqG.
      rewrite inst_lift in Heqt. subst.
      rewrite resolve_inst in H.
      destruct resolve.
      + injection H. easy.
      + discriminate H.
    - iIntros "#HeqG #Heqt".
      iExists (lift vt _), (lift t _). wsimpl.
      iSplit. wsimpl.
      iModIntro. iIntros "#Heq1". iModIntro. iIntros "#Heq2".
      iPoseProof (IHT (w0 ▻ 1 ▻ 2)
                    ((v, Ty_hole (w0 ▻ 1 ▻ 2) 1 (ctx.in_succ ctx.in_zero)) :: G0[step][step])
                    (Ty_hole (w0 ▻ 1 ▻ 2) 2 ctx.in_zero)) as "IHT". clear IHT.
      wsimpl.
      iPoseProof ("IHT" with "Heq1 HeqG Heq2") as "-#IHT'". iRevert "IHT'". iClear "IHT".
      iApply wp_mono. unfold _4. iIntros (w1 r1 _). wsimpl.
    - iIntros "#HeqG #Heqt".
      iExists (lift t _). wsimpl.
      iSplit. wsimpl.
      iModIntro. iIntros "#Heq1".
      iPoseProof (IHT (w0 ▻ 2)
                    ((v, lift vt (w0 ▻ 2)) :: G0[step])
                    (Ty_hole (w0 ▻ 2) 2 ctx.in_zero)) as "IHT"; clear IHT.
      wsimpl.
      iPoseProof ("IHT" with "HeqG Heq1") as "-#IHT'". iRevert "IHT'". iClear "IHT".
      iApply wp_mono. unfold _4. iIntros (w1 r1 _). wsimpl.
    - iIntros "#HeqG #Heqt".
      iExists (lift t2 _).
      iModIntro. iIntros "#Heq1".
      rewrite wp_bind.
      iPoseProof (IHT1 (w0 ▻ 0) G0[step (R := Alloc)] (Ty_func (w0 ▻ 0) (Ty_hole (w0 ▻ 0) 0 ctx.in_zero) t0[step (R := Sub)])) as "IHT1"; clear IHT1.
      wsimpl.
      iPoseProof ("IHT1" with "HeqG Heq1 Heqt") as "-#IHT1'". iRevert "IHT1'". iClear "IHT1".
      iApply wp_mono. unfold _4. iIntros (w1 r1 _). iModIntro. wsimpl.
      iApply IHT2; wsimpl.
  Qed.

End CandidateType.

Require Import List.
Import ListNotations.
From Em Require Import
     Definitions Context Environment STLC Prelude.
Import ctx.notations.
From Em Require
  Unification.

Local Notation "<{ A ~ w }>" := (persist _ A _ w).

#[export] Instance PersistentTri_Ty : Persistent Unification.Tri.Tri Ty :=
  fun w1 t w2 ζ => Unification.Sub.subst t (Unification.Sub.triangular ζ).

Open Scope indexed_scope.

Fixpoint bind [A B] {Σ} (m : FreeM A Σ) (f : □⁺ (A -> (FreeM B)) Σ)
  : FreeM B Σ :=
  match m with
  | Ret_Free _ _ v => (T Σ f) v (* removing the box *)
  | Fail_Free _ _ => Fail_Free B Σ
  | Bind_AssertEq_Free _ _ t1 t2 C1 =>
      Bind_AssertEq_Free B Σ t1 t2 (bind C1 f)
  | Bind_Exists_Free _ _ i C =>
      Bind_Exists_Free B Σ i
        (bind (* (Σ ▻ i) *) C
            (fun Σ' (ω : Accessibility (Σ ▻ i) Σ') (V : A Σ') =>
               (_4 Σ f) (Σ ▻ i) (acc.fresh Σ i (Σ ▻ i) (acc.refl (Σ ▻ i))) Σ' ω V))
  end.

Local Notation "[ ω ] x <- ma ;; mb" :=
  (bind ma (fun _ ω x => mb))
    (at level 80, x at next level,
      ma at next level, mb at level 200,
      right associativity).

Definition assert {Σ} t1 t2 :=
  Bind_AssertEq_Free Unit Σ t1 t2 (Ret_Free Unit Σ tt).

Definition exists_Ty : forall Σ, FreeM Ty Σ :=
  fun Σ => let i := ctx.length Σ in
           Bind_Exists_Free Ty Σ i (Ret_Free _ _ (Ty_hole _ i ctx.in_zero)).

(* Indexes a given ty by a world Σ *)
Fixpoint lift (t : ty) (Σ : World) : Ty Σ :=
  match t with
  | ty_bool => Ty_bool Σ
  | ty_func do co => Ty_func Σ (lift do Σ) (lift co Σ)
  end.

Fixpoint liftEnv (E : env) (Σ : World) : Env Σ :=
  match E with
  | List.nil               => List.nil
  | List.cons (pair s t) E => cons (pair s (lift t Σ)) (liftEnv E Σ)
  end.

Fixpoint generate (e : expr) {Σ : World} (Γ : Env Σ) : FreeM Ty Σ :=
  match e with
  | v_true => Ret_Free Ty Σ (Ty_bool Σ)
  | v_false => Ret_Free Ty Σ (Ty_bool Σ)
  | e_if cnd coq alt =>
      [ ω₁ ] t_cnd <- generate cnd Γ ;;
      [ ω₂ ] _     <- assert t_cnd (Ty_bool _) ;;
      [ ω₃ ] t_coq <- generate coq <{ Γ ~ ω₁ .> ω₂ }> ;;
      [ ω₄ ] t_alt <- generate alt <{ Γ ~ ω₁ .> ω₂ .> ω₃ }> ;;
      [ ω₅ ] _     <- assert <{ t_coq ~ ω₄ }>  <{ t_alt ~ (acc.refl _) }> ;;
         Ret_Free Ty _ <{ t_coq ~ ω₄ .> ω₅ }>
  | e_var var =>
      match (value var Γ) with
      | Some t_var => Ret_Free Ty _ t_var
      | None => Fail_Free Ty Σ
      end
  | e_app f a =>
      [ ω1 ] t_co <- exists_Ty Σ ;;
      [ ω2 ] t_do <- generate a <{ Γ ~ ω1 }> ;;
      [ ω3 ] t_fn <- generate f <{ Γ ~ ω1 .> ω2 }> ;;
      [ ω4 ] _    <- assert t_fn <{ (Ty_func _ t_do <{ t_co ~ ω2 }> ) ~ ω3 }> ;;
         Ret_Free Ty _ <{ t_co ~ ω2 .> ω3 .> ω4 }>
  | e_abst var t_var e =>
      let t_var' := (lift t_var Σ) in (* t_var lives in ty, not in (Ty w) *)
      [ ω1 ] t_e <- generate e ((var, t_var') :: Γ) ;;
        Ret_Free Ty _ (Ty_func _ <{ t_var' ~ ω1 }> t_e)
  | e_absu var e =>
      [ ω1 ] t_var <- exists_Ty Σ ;;
      [ ω2 ] t_e <- generate e ((var, t_var) :: <{ Γ ~ ω1 }>) ;;
        Ret_Free Ty _ (Ty_func _ <{ t_var ~ ω2 }> t_e)
  end.

Section RunTI.

  Import SigTNotations.

  (* infer_schematic defines inference without grounding
     of remaining unification variables. *)
  Definition infer_schematic (e : expr) : option (Schematic Ty) :=
    match Unification.Variant1.solve_ng (generate e []%list) with
    | Some (w; (_, t)) => Some (w; t)
    | None             => None
    end.

  Fixpoint grounding (w : World) : Assignment w :=
    match w with
    | ctx.nil      => env.nil
    | ctx.snoc Γ b => env.snoc (grounding Γ) b ty_bool
    end%ctx.

  Definition infer_grounded (e : expr) : option ty :=
    option.map (fun '(w; t) => inst t (grounding w)) (infer_schematic e).

End RunTI.

Section TypeReconstruction.

  Notation Expr := (Lifted expr).
  (* TODO: define reader applicative to use ctor of expr to create Expr *)

#[export] Instance Persistent_Lifted {A} : Persistent Accessibility (Lifted A).
  Proof. unfold Persistent, Valid, Impl, Lifted, BoxR. eauto using compose. Qed.

  Definition ret  {w} := Ret_Free (Prod Ty Expr) w.
  Definition fail {w} := Fail_Free (Prod Ty Expr) w.

Fixpoint generate' (e : expr) {Σ : World} (Γ : Env Σ) : FreeM (Prod Ty Expr) Σ :=
  match e with
  | v_true  => ret (Ty_bool Σ, (fun _ => v_true))
  | v_false => ret (Ty_bool Σ, (fun _ => v_false))
  | e_if cnd coq alt =>
      [ ω1 ] r_cnd <- generate' cnd Γ ;;
      [ ω2 ] _     <- assert (fst r_cnd) (Ty_bool _) ;;
      [ ω3 ] r_coq <- generate' coq <{ Γ ~ ω1 .> ω2 }> ;;
      [ ω4 ] r_alt <- generate' alt <{ Γ ~ ω1 .> ω2 .> ω3 }> ;;
      [ ω5 ] _     <- assert <{ (fst r_coq) ~ ω4 }>  <{ (fst r_alt) ~ (acc.refl _) }> ;;
         let e_cnd := <{ (snd r_cnd) ~ ω2 .> ω3 .> ω4 .> ω5 }> in
         let e_coq := <{ (snd r_coq) ~ ω4 .> ω5 }> in
         let t_coq := <{ (fst r_coq) ~ ω4 .> ω5 }> in
         let e_alt := <{ (snd r_alt) ~ ω5 }> in
         ret (t_coq, fun a => (e_if (e_cnd a) (e_coq a) (e_alt a)))
  | e_var var =>
      match (value var Γ) with
      | Some t_var => ret (t_var, fun a => e_var var)
      | None => fail
      end
  | e_app f a =>
      [ ω1 ] T_cod <- exists_Ty Σ ;;
      [ ω2 ] r_dom <- generate' a <{ Γ ~ ω1 }> ;;
      [ ω3 ] r_fun <- generate' f <{ Γ ~ ω1 .> ω2 }> ;;
      [ ω4 ] _     <- assert (fst r_fun) <{ (Ty_func _ (fst r_dom) <{ T_cod ~ ω2 }> ) ~ ω3 }> ;;
         let e_fun := <{ (snd r_fun) ~ ω4 }> in
         let t_cod := <{ T_cod ~ ω2 .> ω3 .> ω4 }> in
         let e_dom := <{ (snd r_dom) ~ ω3 .> ω4 }> in
          ret ( t_cod , fun a => e_app (e_fun a) (e_dom a))
  | e_abst var t_var e =>
      let t_var' := (lift t_var Σ) in (* t_var lives in ty, not in (Ty w) *)
      [ ω1 ] t_e <- generate' e ((var, t_var') :: Γ) ;;
        ret (Ty_func _ <{ t_var' ~ ω1 }> (fst t_e), fun a => e_abst var t_var (snd t_e a))
  | e_absu var e =>
      [ ω1 ] t_var <- exists_Ty Σ ;;
      [ ω2 ] t_e <- generate' e ((var, t_var) :: <{ Γ ~ ω1 }>) ;;
        ret (Ty_func _ <{ t_var ~ ω2 }> (fst t_e),
            fun a => e_abst var (inst <{ t_var ~ ω2 }> a) (snd t_e a))
  end.

End TypeReconstruction.

Record Acc (w w' : World) : Type := mkAcc
  { iw : World
  ; pos : Accessibility w iw
  ; neg : Unification.Tri.Tri iw w' }.

Notation "w1 ⇅ w2" := (Acc w1 w2) (at level 80).
Notation "w1 ↑ w2" := (Accessibility w1 w2) (at level 80).
Notation "w1 ↓ w2" := (Unification.Tri.Tri w1 w2) (at level 80).

Lemma acc_refl : forall w, Acc w w.
Proof. intros. exists w. constructor. constructor. Defined.

Lemma adding_invariant: forall w1 w2 α,
    w1     ↓ w2      ->
    w1 ▻ α ↓ w2 ▻ α.
Proof.
  intros. induction H.
  - constructor 1.
  - constructor 2 with x (ctx.in_succ xIn). cbn.
    apply (persist _ t _ (acc.fresh _ α _ (acc.refl _))).
    cbn. apply IHTri.
Defined.

Lemma up_down_down_eq_up_down : forall w1 w2 w3,
    w1 ⇅ w2 -> w2 ↓ w3 -> w1 ⇅ w3.
Proof. destruct 1. eexists. apply pos0. now apply (Unification.Tri.trans neg0). Defined.

Lemma up_down_up_eq_up_up_down : forall w1 w2 w3
    (H1: w1 ⇅ w2), w2 ↑ w3 -> w1 ⇅ w3.
Proof.
  intros. destruct H1. generalize dependent iw0. induction X.
  - intros. now exists iw0.
  - intros. specialize (IHX (iw0 ▻ α)). apply IHX.
    + eapply acc.trans. apply pos0. eapply acc.fresh. apply acc.refl.
    + apply adding_invariant. apply neg0.
Defined.

Lemma acc_trans {w1 w2 w3 : World} : w1 ⇅ w2 -> w2 ⇅ w3 -> w1 ⇅ w3.
Proof.
  intros. destruct X. destruct X0.
  apply (up_down_down_eq_up_down _ iw1).
  apply (up_down_up_eq_up_up_down _ w2).
  exists iw0; easy. easy. easy.
Defined.

Local Notation "r12 ↻ r23" := (acc_trans r12 r23) (at level 80).

Lemma acc_trans_assoc {w1 w2 w3 w4 : World} : forall (r12 : w1 ⇅ w2) (r23 : w2 ⇅ w3) (r34 : w3 ⇅ w4),
  (r12 ↻ (r23 ↻ r34)) = ((r12 ↻ r23) ↻ r34).
Proof. Admitted.

#[export] Instance PersistentAcc_Ty : Persistent Acc Ty :=
  fun w1 t w2 r =>
    match r with
      {| iw := wi; pos := r1; neg := r2 |} =>
        <{ <{ t ~ r1 }> ~ r2 }>
    end.

(* unify with PersistLaws about ↑ *)
Class PersistLaws A `{Persistent Acc A} : Type :=
  { refl_persist w (V : A w) :
        persist w V w (acc_refl w) = V }.

Class PersistLift A `{Persistent Acc A} : Type :=
  { lift_persist (w w': World) t r :
    persist w (lift t _) w' r = lift t _ }.
(* TODO: make lift generic (liftEnv is needed for Env) *)

#[export] Instance PersistLift_Ty : PersistLift Ty.
Proof.
  constructor. intros. induction r. induction t; cbn. easy. rewrite <- IHt1. rewrite <- IHt2. easy.
Defined.

#[export] Instance PersistLift_Env : PersistLift Env.
Proof. Admitted.

Module UpDown.
  #[local] Notation "□⇅ A" := (BoxR Acc A) (at level 9, format "□⇅ A", right associativity)
      : indexed_scope.
  #[local] Notation "w1 .> w2" := (acc_trans w1 w2) (at level 80).

  Definition T {A} : ⊢ □⇅A -> A :=
    fun w a => a w (acc_refl w).
  Definition K {A B} : ⊢ □⇅(A -> B) -> □⇅A -> □⇅B :=
    fun w f a w' r => f _ r (a _ r).
  Definition _4 {A} : ⊢ □⇅A -> □⇅□⇅A :=
    fun w a w1 r1 w2 r2 => a w2 (r1 ↻ r2).

  Definition step {w α} : w ⇅ w ▻ α :=
    {| iw := w ▻ α;
       pos := acc.fresh w α (w ▻ α) (acc.refl (w ▻ α));
       neg := Unification.Tri.refl;
    |}.

  Fixpoint up_aux {w1 wi β} (p : w1 ↑ wi) {struct p} :
    forall w2, wi ↓ w2 -> Acc (w1 ▻ β) (w2 ▻ β) :=
    match p with
    | acc.refl _ =>
        fun w2 n =>
          {| pos := acc.refl _;
            neg := adding_invariant _ _ _ n
          |}
    | acc.fresh _ α wi p =>
        fun w2 n =>
          acc_trans
            {| iw := w1 ▻ β ▻ α ▻ β;
              pos := acc.fresh _ _ _ (acc.fresh _ _ _ (acc.refl _));
              neg :=
                let βIn := ctx.in_succ (ctx.in_succ ctx.in_zero) in
                Unification.Tri.cons β
                  (xIn := βIn)
                  (Ty_hole ((w1 ▻ β ▻ α ▻ β) - β) β ctx.in_zero)
                  Unification.Tri.refl
            |}
            (up_aux p w2 n)
    end.

  Definition up {w1 w2 β} (r : w1 ⇅ w2) :
    w1 ▻ β ⇅ w2 ▻ β :=
    match r with
      mkAcc _ _ iw pos neg => up_aux pos w2 neg
    end.

  Definition bind {A B} : ⊢ FreeM A -> □⇅(A -> (FreeM B)) -> FreeM B :=
    fix bind {w} m f :=
    match m with
    | Ret_Free _ _ a                  => (T _ f) a
    | Fail_Free _ _                   =>
      Fail_Free _ _
    | Bind_AssertEq_Free _ _ t1 t2 C1 =>
      Bind_AssertEq_Free _ _ t1 t2 (bind C1 f)
    | Bind_Exists_Free _ _ i C =>
      Bind_Exists_Free _ _ i (bind C ((_4 _ f) _ step))
    end.

  #[global] Arguments bind {A B} [w] m f.
  #[local] Notation "[ ω ] x <- ma ;; mb" :=
    (bind ma (fun _ (ω : Acc _ _) x => mb))
      (at level 80, x at next level,
        ma at next level, mb at level 200,
        right associativity).

  Fixpoint generate (e : expr) {Σ : World} (Γ : Env Σ) : FreeM Ty Σ :=
    match e with
    | v_true => Ret_Free Ty Σ (Ty_bool Σ)
    | v_false => Ret_Free Ty Σ (Ty_bool Σ)
    | e_if cnd coq alt =>
        [ ω₁ ] t_cnd <- generate cnd Γ ;;
        [ ω₂ ] _     <- assert t_cnd (Ty_bool _) ;;
        [ ω₃ ] t_coq <- generate coq <{ Γ ~ ω₁ .> ω₂ }> ;;
        [ ω₄ ] t_alt <- generate alt <{ Γ ~ ω₁ .> ω₂ .> ω₃ }> ;;
        [ ω₅ ] _     <- assert <{ t_coq ~ ω₄ }> t_alt ;;
           Ret_Free Ty _ <{ t_coq ~ ω₄ .> ω₅ }>
    | e_var var =>
        match (value var Γ) with
        | Some t_var => Ret_Free Ty _ t_var
        | None => Fail_Free Ty Σ
        end
    | e_app f a =>
        [ ω1 ] t_co <- exists_Ty Σ ;;
        [ ω2 ] t_do <- generate a <{ Γ ~ ω1 }> ;;
        [ ω3 ] t_fn <- generate f <{ Γ ~ ω1 .> ω2 }> ;;
        [ ω4 ] _    <- assert t_fn <{ (Ty_func _ t_do <{ t_co ~ ω2 }> ) ~ ω3 }> ;;
           Ret_Free Ty _ <{ t_co ~ ω2 .> ω3 .> ω4 }>
    | e_abst var t_var e =>
        let t_var' := (lift t_var Σ) in (* t_var lives in ty, not in (Ty w) *)
        [ ω1 ] t_e <- generate e ((var, t_var') :: Γ) ;;
          Ret_Free Ty _ (Ty_func _ <{ t_var' ~ ω1 }> t_e)
    | e_absu var e =>
        [ ω1 ] t_var <- exists_Ty Σ ;;
        [ ω2 ] t_e <- generate e ((var, t_var) :: <{ Γ ~ ω1 }>) ;;
          Ret_Free Ty _ (Ty_func _ <{ t_var ~ ω2 }> t_e)
    end.

  Module Attempt2.

    Definition wp {A} :
      ⊢ FreeM A -> □⇅(A -> PROP) -> PROP :=
      fix wp {w} m Q {struct m} :=
        match m with
        | Ret_Free _ _ a  => T _ Q a
        | Fail_Free _ _   => False
        | Bind_AssertEq_Free _ _ t1 t2 m =>
            t1 = t2 /\ wp m Q
        | Bind_Exists_Free _ _ i m =>
            wp m (_4 w Q (w ▻ i) step)
        end.
    #[global] Arguments wp {A} [w].

    Lemma wp_mono {A}
      {w} (m : FreeM A w) (P Q : □⇅(A -> PROP) w)
      (PQ : forall w' r a, P w' r a -> Q w' r a) :
      wp m P -> wp m Q.
    Proof.
      induction m; cbn [wp].
      - unfold T. apply PQ.
      - auto.
      - intros [H1 H2]; split.
        exact H1. revert H2. apply IHm; auto.
      - unfold _4; apply IHm; auto.
    Qed.

    Lemma wp_equiv {A}
      {w} (m : FreeM A w) (P Q : □⇅(A -> PROP) w)
      (PQ : forall w' r a, P w' r a <-> Q w' r a) :
      wp m P <-> wp m Q.
    Proof. split; apply wp_mono; intuition. Qed.

    Lemma wp_bind {A B} (* `{Persistent Acc A,  Persistent Acc B} *)
      {w} (m : FreeM A w) (f : □⇅(A -> FreeM B) w) (Q : □⇅(B -> PROP) w) :
      wp (bind m f) Q <->
      wp m (fun _ r a => wp (f _ r a) (_4 _ Q _ r)).
    Proof.
      induction m; cbn; unfold T, _4.
      - apply wp_equiv. intros w1 r1 a1.
        (* refl is left identity of trans *)
        admit.
      - reflexivity.
      - apply and_iff_compat_l'. intros ?.
        apply IHm.
      - rewrite IHm.
        apply wp_equiv. intros w1 r1 a1.
        apply wp_equiv. intros w2 r2 b2.
        unfold _4.
        (* Need assoc lemma *)
        admit.
    Admitted.

    Lemma completeness {G e t ee} (R : G |-- e ; t ~> ee) :
      forall w,
        wp (generate e (liftEnv G w))
          (fun w _ T => exists A : Assignment w, inst T A = t).
    Proof.
      induction R; cbn [generate wp]; unfold assert, T; intros w0.
      - admit.
      - admit.
      - rewrite wp_bind; cbn [wp].
        specialize (IHR1 w0). revert IHR1. apply wp_mono.
        intros w1 r1 tcnd Hcnd.
        rewrite wp_bind; cbn [wp].
        split.
        { admit. }
        unfold T.
        rewrite wp_bind; cbn [wp].
        specialize (IHR2 w1). revert IHR2.
        (* need more lemmas first *)
    Admitted.

  End Attempt2.

  Module Attempt3.

    Definition Property : TYPE :=
      fun w => forall w', w ⇅ w' -> Prop.

    Definition False : ⊢ Property :=
      fun _ _ _ => Logic.False.
    #[global] Arguments False {w}.
    Definition Eq : ⊢ Ty -> Ty -> Property :=
      fun w t1 t2 w' r => persist _ t1 _ r = persist _ t2 _ r.
    #[global] Arguments Eq [w].
    Definition And : ⊢ Property -> Property -> Property :=
      fun w P Q w' r => P _ r /\ Q _ r.
    #[global] Arguments And [w].

    Definition wp {A} `{Persistent Acc A} :
      ⊢ FreeM A -> □⇅(A -> Property) -> Property :=
      fix wp {w} m Q {struct m} :=
        match m with
        | Ret_Free _ _ a => T w Q a
        | Fail_Free _ _ => False
        | Bind_AssertEq_Free _ _ t1 t2 f => And (Eq t1 t2) (wp f Q)
        | Bind_Exists_Free _ _ i f =>
            fun w1 r1 => wp f (_4 _ Q _ step) _ (up r1)
        end.
    #[global] Arguments wp {A _} [w].

    Lemma wp_mono {A} `{Persistent Acc A}
      {w} (m : FreeM A w) (P Q : □⇅(A -> Property) w)
      (PQ : forall w1 r1 a w2 r2, P w1 r1 a w2 r2 -> Q w1 r1 a w2 r2) :
      forall w' r,
        wp m P w' r -> wp m Q w' r.
    Proof.
      induction m; cbn [wp]; intros w1 r1.
      - unfold T. apply PQ.
      - auto.
      - unfold And, Eq. intros [H1 H2]; split.
        exact H1. revert H2. apply IHm; auto.
      - unfold _4. apply IHm; auto.
    Qed.

    Lemma wp_equiv {A} `{Persistent Acc A}
      {w} (m : FreeM A w) (P Q : □⇅(A -> Property) w)
      (PQ : forall w1 r1 a w2 r2, P w1 r1 a w2 r2 <-> Q w1 r1 a w2 r2) :
      forall w' r,
        wp m P w' r <-> wp m Q w' r.
    Proof. split; apply wp_mono; intuition. Qed.

    Lemma wp_bind {A B} `{Persistent Acc A, Persistent Acc B}
      {w} (m : FreeM A w) (f : □⇅(A -> FreeM B) w) (Q : □⇅(B -> Property) w) :
      forall w' r,
        wp (bind m f) Q w' r <->
          wp m (fun _ r a => wp (f _ r a) (_4 _ Q _ r)) w' r.
    Proof.
    Admitted.

    Lemma completeness {G e t ee} (R : G |-- e ; t ~> ee) :
      forall w1 w2 (r : w1 ⇅ w2),
        wp (generate e (liftEnv G w1))
          (fun w1 r1 T => Eq T (lift t _)
          ) w2 r.
    Proof.
      induction R; cbn; unfold T, _4, K; intros w1 w2 r; cbn.
      - reflexivity.
      - reflexivity.
      - rewrite wp_bind; cbn [wp].
        specialize (IHR1 w1 w2 r). revert IHR1.
        apply wp_mono.
        intros w3 r3 tcnd w4 r4 Hcnd. cbn in Hcnd.
        unfold T, _4, And; cbn [wp].
        split. auto.
        rewrite wp_bind; cbn [wp].
        specialize (IHR2 w3 w3 (acc_refl _)). revert IHR2.
    Admitted.

  End Attempt3.

End UpDown.

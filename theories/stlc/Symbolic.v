Require Import List.
Import ListNotations.
From Em Require Import
     Definitions Context Environment STLC Prelude Substitution Triangular.
Import ctx.notations.
From Em Require
  Unification.

Local Notation "<{ A ~ w }>" := (persist _ A _ w).

#[export] Instance PersistentTri_Ty : Persistent Tri Ty :=
  fun w1 t w2 ζ => Sub.subst t (Sub.triangular ζ).
#[export] Instance PersistentSub_Ty : Persistent Sub Ty :=
  fun w1 t w2 ζ => Sub.subst t ζ.
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
  ; neg : Tri iw w' }.

Notation "w1 ⇅ w2" := (Acc w1 w2) (at level 80).
Notation "w1 ↑ w2" := (Accessibility w1 w2) (at level 80).
Notation "w1 ↓ w2" := (Tri w1 w2) (at level 80).

Definition acc_refl w : Acc w w :=
  {| iw := w; pos := acc.refl w; neg := Tri.refl |}.

Fixpoint down_add {α w1 w2} (t : Tri w1 w2) {struct t} : Tri (w1 ▻ α) (w2 ▻ α) :=
  match t with
  | Tri.refl => Tri.refl
  | @Tri.cons _ _ x _ t r =>
    @Tri.cons _ _ x (ctx.in_succ _) (persist _ t _ acc.step) (down_add r)
  end.

Definition up_down_down_eq_up_down {w1 w2 w3} (r12 : w1 ⇅ w2) (down : w2 ↓ w3) : w1 ⇅ w3 :=
  match r12 with
  | {| iw := iw; pos := pos; neg := neg |} =>
        mkAcc _ _ _ pos (neg ⊙⁻ down)
  end.

Definition up_down_up_eq_up_up_down {w1 w2 w3} (r12: w1 ⇅ w2) (up : w2 ↑ w3) : w1 ⇅ w3 :=
 match r12 with
 | {| iw := iw; pos := pos; neg := neg |} =>
      acc.Accessibility_rect
        (fun (w w' : World) (up : w ↑ w') => forall iw : World, w1 ↑ iw -> iw ↓ w -> w1 ⇅ w')
        (mkAcc _)
        (fun w α w' up IH iw pos neg =>
           IH (iw ▻ α) (pos .> acc.fresh iw α (iw ▻ α) (acc.refl (iw ▻ α))) (down_add neg))
        w2 w3 up iw pos neg
 end.

Definition acc_trans {w1 w2 w3 : World} (r12 : w1 ⇅ w2) (r23 : w2 ⇅ w3) : w1 ⇅ w3 :=
 match r23 with
 | {| iw := iw; pos := pos; neg := neg |} =>
     up_down_down_eq_up_down (up_down_up_eq_up_up_down r12 pos) neg
 end.

Notation "A ⇅↓ B" := (up_down_down_eq_up_down A B) (at level 80).
Notation "A ⇅↑ B" := (up_down_up_eq_up_up_down A B) (at level 80).

Local Notation "r12 ↻ r23" := (acc_trans r12 r23) (at level 80).

Lemma acc_refl_trans {w1 w2 : World} (r : w1 ⇅ w2) :
  (acc_refl w1 ↻  r) = r.
Proof. Admitted.

Lemma acc_trans_refl {w1 w2 : World} (r : w1 ⇅ w2) :
  (r ↻ acc_refl w2) = r.
Proof. destruct r. cbn. now rewrite Tri.trans_refl. Defined.

Lemma acc_trans_assoc {w1 w2 w3 w4} (r12 : w1 ⇅ w2) (r23 : w2 ⇅ w3) (r34 : w3 ⇅ w4) :
   ((r12 ↻ r23) ↻ r34) = (r12 ↻ (r23 ↻ r34)).
Proof. Admitted.

Definition sub_acc {w1 w2 : World} (r : w1 ⇅ w2) : Sub.Sub w1 w2 :=
  match r with
  | {| pos := p; neg := n |} =>
      Sub.comp
        (env.tabulate (fun x xIn => <{ Ty_hole w1 x xIn ~ p }>))
        (Sub.triangular n)
  end.

#[export] Instance PersistentAcc_Ty : Persistent Acc Ty :=
  fun w1 t w2 r =>
    match r with
      {| iw := wi; pos := r1; neg := r2 |} =>
        <{ <{ t ~ r1 }> ~ r2 }>
    end.

Lemma persist_bool {w1 w2} (r : Acc w1 w2) :
  persist _ (Ty_bool _) _ r = Ty_bool _.
Proof. destruct r; reflexivity. Qed.

Lemma persist_func {w1 w2} (r : Acc w1 w2) (t1 t2 : Ty _) :
  persist _ (Ty_func _ t1 t2) _ r =
  Ty_func _ (persist _ t1 _ r) (persist _ t2 _ r).
Proof. destruct r; reflexivity. Qed.

(* unify with PersistLaws about ↑ *)
Class PersistLaws A `{Persistent Acc A} : Type :=
  { refl_persist w (V : A w) :
        persist w V w (acc_refl w) = V }.

(* Class PersistLift A `{Persistent Acc A} : Type := *)
(*   { lift_persist (w w': World) t r : *)
(*     persist w (lift t _) w' r = lift t _ }. *)
(* (* TODO: make lift generic (liftEnv is needed for Env) *) *)

Lemma persist_liftTy : forall (w w' : World) t (r : Sub w w'),
    persist w (lift t _) w' r = lift t _.
Proof.
  intros w w' t. revert w'.
  induction t; cbn; intros; now f_equal.
Qed.

(* Lemma persist_split : forall w w' iw (pos : w ↑ iw) (neg : iw ↓ w') x, *)
(*   persist w  x iw pos -> *)
(*   persist iw x w' neg -> *)
(*   persist w  x w' {| iw := iw; pos := pos; neg := neg |}. *)

Lemma persist_liftEnv : forall (w w' : World) e (r : Sub w w'),
    persist w (liftEnv e _) w' r = liftEnv e _.
Proof.
  induction e. now cbn.
  destruct a. cbn. intro r. rewrite IHe.
  now rewrite persist_liftTy.
Qed.

Lemma subst_lift (t : ty) :
  forall w1 w2 (r : w1 ⊒ˢ w2),
    Sub.subst (lift t w1) r = lift t w2.
Proof.
  induction t; intros w1 w2 r; cbn; now f_equal.
Qed.

Lemma value_lift (g : env) (x : String.string) (w : World) :
  value x (liftEnv g w) =
    option.map (fun t => lift t w) (value x g).
Proof.
  induction g as [|[y t]]; cbn.
  - reflexivity.
  - now destruct String.string_dec.
Qed.

Lemma value_inst (w : World) (g : Env w) (x : String.string) (ι : Assignment w) :
  value x (inst g ι) =
    option.map (fun t => inst t ι) (value x g).
Proof.
  induction g as [|[y t]]; cbn.
  - reflexivity.
  - now destruct String.string_dec.
Qed.

Lemma inst_lift (w : World) (t : ty) (ι : Assignment w) :
  inst (lift t w) ι = t.
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
       neg := Tri.refl;
    |}.

  Fixpoint up_aux {w1 wi β} (p : w1 ↑ wi) {struct p} :
    forall w2, wi ↓ w2 -> Acc (w1 ▻ β) (w2 ▻ β) :=
    match p with
    | acc.refl _ =>
        fun w2 n =>
          {| pos := acc.refl _;
            neg := down_add n
          |}
    | acc.fresh _ α wi p =>
        fun w2 n =>
          acc_trans
            {| iw := w1 ▻ β ▻ α ▻ β;
              pos := acc.fresh _ _ _ (acc.fresh _ _ _ (acc.refl _));
              neg :=
                let βIn := ctx.in_succ (ctx.in_succ ctx.in_zero) in
                Tri.cons β
                  (xIn := βIn)
                  (Ty_hole ((w1 ▻ β ▻ α ▻ β) - β) β ctx.in_zero)
                  Tri.refl
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

    Definition wp {A} :
      ⊢ FreeM A -> □⇅(A -> Property) -> Property :=
      fix wp {w} m Q {struct m} :=
        match m with
        | Ret_Free _ _ a => T w Q a
        | Fail_Free _ _ => False
        | Bind_AssertEq_Free _ _ t1 t2 f => And (Eq t1 t2) (wp f Q)
        | Bind_Exists_Free _ _ i f =>
            fun w1 r1 => wp f (_4 _ Q _ step) _ (up r1)
        end.
    #[global] Arguments wp {A} [w].

    Lemma wp_mono {A}
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

    Lemma wp_equiv {A}
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
        (* rewrite persist_liftEnv. *)
    Admitted.

  End Attempt3.

End UpDown.

(* Remove phase separation and all abstractions to get
   a base line. *)
Module EagerSolving.

  Import option.notations.
  Import Unification.
  Import SigTNotations.

  #[local] Arguments Sub.thin : simpl never.
  #[local] Notation "□ˢ A" :=
    (BoxR Sub A)
      (at level 9, format "□ˢ A", right associativity)
      : indexed_scope.

  Definition T {A} : ⊢ □ˢA -> A :=
    fun w a => a w Sub.id.
  Definition K {A B} : ⊢ □ˢ(A -> B) -> □ˢA -> □ˢB :=
    fun w f a w' r => f _ r (a _ r).
  Definition _4 {A} : ⊢ □ˢA -> □ˢ□ˢA :=
    fun w a w1 r1 w2 r2 => a w2 (r1 ⊙ˢ r2).

  Definition M (A : TYPE) : TYPE :=
    Option (DiamondR Sub A).

  Definition pure {A} : ⊢ A -> M A :=
    fun w a => Some (existT _ w (Sub.id, a)).

  Definition bind {A B} : ⊢ M A -> □ˢ(A -> (M B)) -> M B :=
    fun w m f =>
      '(existT _ w1 (r1,a1)) <- m;;
      '(existT _ w2 (r2,b2)) <- f w1 r1 a1;;
      Some (existT _ w2 (r1 ⊙ˢ r2, b2)).

  Definition mexists {A w n} (m : M A (w ▻ n)) : M A w :=
    '(w';(r,a)) <- m ;;
    Some (existT _ w' (Sub.step ⊙ˢ r, a)).

  Definition mgu : ⊢ Ty -> Ty -> M Unit :=
    fun w t1 t2 =>
      '(w;(r,u)) <- Variant1.mgu t1 t2 ;;
      Some (w; (Sub.triangular r, u)).

  Fixpoint infer (e : expr) : ⊢ Env -> M Ty.
  Proof.
    intros w G. destruct e.
    - exact (pure w (Ty_bool w)).
    - exact (pure w (Ty_bool w)).
    - eapply bind.
      apply (infer e1 w G).
      intros w1 r1 t1.
      eapply bind.
      apply (mgu w1 t1 (Ty_bool w1)).
      intros w2 r2 _.
      eapply bind.
      apply (infer e2 w2 <{ G ~ r1 ⊙ˢ r2 }>).
      intros w3 r3 t2.
      eapply bind.
      apply (infer e3 w3 <{ G ~ r1 ⊙ˢ r2 ⊙ˢ r3 }>).
      intros w4 r4 t3.
      eapply bind.
      apply (mgu w4 <{ t2 ~ r4 }> t3).
      intros w5 r5 _.
      apply pure.
      exact <{ t3 ~ r5 }>.
    - destruct (value s G) as [t|].
      + apply pure. apply t.
      + apply None.
    - pose (w ▻ 0) as w1.
      pose (Ty_hole w1 0 ctx.in_zero) as t1.
      pose (@Sub.step w 0) as r1.
      pose ((s, t1) :: <{ G ~ r1 }>) as G1.
      eapply mexists.
      eapply bind.
      apply (infer e w1 G1).
      intros w2 r2 t2.
      apply pure.
      apply (Ty_func _ <{ t1 ~ r2 }> t2).
    - eapply bind.
      apply (infer e w ((s,lift t w) :: G)).
      intros w1 r1 t2.
      apply pure.
      apply (Ty_func _ (lift t _) t2).
    - eapply bind.
      apply (infer e1 w G).
      intros w1 r1 t1.
      pose <{ G ~ r1 }> as G1.
      eapply bind.
      apply (infer e2 w1 G1).
      intros w2 r2 t2.
      eapply (mexists (n := 0)).
      pose (w2 ▻ 0) as w3.
      pose (@Sub.step w2 0) as r3.
      pose (Ty_hole w3 0 ctx.in_zero) as ti.
      eapply bind.
      apply (mgu _ <{ t1 ~ r2 ⊙ˢ r3 }>
               (Ty_func _ <{ t2 ~ r3 }> ti)).
      intros w4 r4 _.
      apply pure.
      apply <{ ti ~ r4 }>.
  Defined.

  Definition WLP {A} : ⊢ M A -> □ˢ(A -> PROP) -> PROP :=
    fun w m P => option.wlp (fun '(w;(r,a)) => P w r a) m.

  Lemma wlp_pure {A w} (a : A w) (p : □ˢ(A -> PROP) w) :
    WLP w (pure w a) p <-> T w p a.
  Proof. unfold WLP, pure. now rewrite option.wlp_match. Qed.

  Lemma wlp_bind {A B w} (m : M A w) (k : □ˢ(A -> M B) w) (p : □ˢ(B -> PROP) w) :
    WLP w (bind _ m k) p <->
      WLP w m (fun w1 r1 a1 => WLP w1 (k w1 r1 a1) (_4 w p w1 r1)).
  Proof.
    unfold WLP, bind.
    rewrite option.wlp_bind.
    apply option.wlp_proper.
    intros (w1 & r1 & a1).
    rewrite option.wlp_bind.
    apply option.wlp_proper.
    intros (w2 & r2 & b2).
    now rewrite option.wlp_match.
  Qed.

  Lemma wlp_mexists {A w n} (m : M A (w ▻ n)) (p : □ˢ(A -> PROP) w) :
    WLP w (mexists m) p <->
    WLP (w ▻ n) m (_4 w p (w ▻ n) Sub.step).
  Proof.
    unfold mexists, WLP, _4.
    rewrite option.wlp_bind.
    apply option.wlp_proper.
    intros (w1 & r1 & a1).
    now rewrite option.wlp_match.
  Qed.

  Lemma wlp_monotonic {A w} (m : M A w) :
    forall
      (p q : □ˢ(A -> PROP) w)
      (pq : forall w1 r1 a1, p w1 r1 a1 -> q w1 r1 a1),
      WLP w m p -> WLP w m q.
  Proof.
    intros p q pq. unfold WLP.
    apply option.wlp_monotonic.
    intros (w1 & r1 & a1).
    apply pq.
  Qed.

  Definition WP {A} : ⊢ M A -> □ˢ(A -> PROP) -> PROP :=
    fun w m P => option.wp (fun '(w;(r,a)) => P w r a) m.

  Lemma wp_pure {A w} (a : A w) (p : □ˢ(A -> PROP) w) :
    WP w (pure w a) p <-> T w p a.
  Proof.
    unfold WP, pure. now rewrite option.wp_match.
  Qed.

  Lemma wp_bind {A B w} (m : M A w) (k : □ˢ(A -> M B) w) (p : □ˢ(B -> PROP) w) :
    WP w (bind _ m k) p <->
      WP w m (fun w1 r1 a1 => WP w1 (k w1 r1 a1) (_4 w p w1 r1)).
  Proof.
    unfold WP, bind.
    rewrite option.wp_bind.
    apply option.wp_proper.
    intros (w1 & r1 & a1).
    rewrite option.wp_bind.
    apply option.wp_proper.
    intros (w2 & r2 & b2).
    now rewrite option.wp_match.
  Qed.

  Lemma wp_mexists {A w n} (m : M A (w ▻ n)) (p : □ˢ(A -> PROP) w) :
    WP w (mexists m) p <->
    WP (w ▻ n) m (_4 w p (w ▻ n) Sub.step).
  Proof.
    unfold mexists, WP, _4.
    rewrite option.wp_bind.
    apply option.wp_proper.
    intros (w1 & r1 & a1).
    now rewrite option.wp_match.
  Qed.

  Lemma wp_monotonic {A w} (m : M A w) :
    forall
      (p q : □ˢ(A -> PROP) w)
      (pq : forall w1 r1 a1, p w1 r1 a1 -> q w1 r1 a1),
      WP w m p -> WP w m q.
  Proof.
    intros p q pq. unfold WP.
    apply option.wp_monotonic.
    intros (w1 & r1 & a1).
    apply pq.
  Qed.

  (* Lemma wlp_mgu {w} (t1 t2 : Ty w) (p : □ˢ(Unit -> PROP) w) : *)
  (*   (exists w' (r : Sub w w'), *)
  (*     P.max (P.unifies t1 t2) r /\ p w' r tt) -> *)
  (*   WLP w (mgu w t1 t2) p. *)
  (* Proof. *)
  (*   unfold mgu. unfold WLP. *)
  (*   rewrite option.wlp_bind. *)
  (*   rewrite option.wlp_match. *)
  (*   destruct (mgu_spec t1 t2) as [(w2 & r2 & [])|]. *)
  (*   - rewrite option.wlp_match. *)
  (*     split. *)
  (*     + now exists w2, (Sub.triangular r2). *)
  (*     + intros (w3 & r3 & H1 & H2). *)
  (*       admit. *)
  (* Abort. *)

  Lemma soundness e :
    forall (w : World) G,
      WLP w (infer e w G)
        (fun w1 r1 b =>
           forall ι : Assignment w1,
           exists ee, inst <{ G ~ r1 }> ι |-- e ; inst b ι ~> ee).
  Proof.
    induction e; cbn - [mexists]; intros w G.
    - rewrite wlp_pure. intros ι. exists v_true; cbn. constructor.
    - rewrite wlp_pure. intros ι. exists v_false; cbn. constructor.
    - rewrite wlp_bind.
      specialize (IHe1 w G). revert IHe1.
      apply wlp_monotonic.
      intros w1 r1 t1 H1.
      rewrite wlp_bind.
      unfold WLP at 1, mgu at 2.
      destruct (mgu_spec t1 (Ty_bool w1)) as [(w2 & r2 & [])|]; [|constructor].
      constructor.
      rewrite wlp_bind.
      specialize (IHe2 w2 (persist w G w2 (r1 ⊙ˢ Sub.triangular r2))).
      revert IHe2.
      apply wlp_monotonic.
      intros w3 r3 t2 H2.
      rewrite wlp_bind.
      specialize (IHe3 w3 (persist w G w3 (r1 ⊙ˢ Sub.triangular r2 ⊙ˢ r3))).
      revert IHe3.
      apply wlp_monotonic.
      intros w4 r4 t3 H3.
      rewrite wlp_bind.
      unfold WLP at 1, mgu.
      destruct (mgu_spec (persist w3 t2 w4 r4) t3) as [(w5 & r5 & [])|]; [|constructor].
      constructor.
      rewrite wlp_pure.
      intros ι.
      (* Need composition of assignments with Subs. *)
      admit.
    - destruct value eqn:?.
      + rewrite wlp_pure. intros ι. exists (e_var s).
        constructor.
        (* need value inst lemma, and persist_subid *)
        admit.
      + constructor.
    - rewrite wlp_mexists.
      rewrite wlp_bind.
      specialize (IHe (w ▻ 0) (cons (pair s (Ty_hole (ctx.snoc w 0) 0 ctx.in_zero)) (persist w G (ctx.snoc w 0) Sub.step))).
      revert IHe.
      apply wlp_monotonic.
      intros w1 r1 t1 H1.
      rewrite wlp_pure.
      intros ι. specialize (H1 ι). destruct H1 as [e' HT1].
      cbn. eexists. constructor. cbn in *.
      (* need persist acc_trans lemma *)
      admit.
    - rewrite wlp_bind.
      specialize (IHe w (cons (pair s (lift t w)) G)).
      revert IHe.
      apply wlp_monotonic.
      intros w1 r1 t1 H1.
      rewrite wlp_pure.
      intros ι. specialize (H1 ι). destruct H1 as [e' HT1].
      cbn. eexists.
      (* need inst lift lemma *)
      admit.
    - rewrite wlp_bind.
      specialize (IHe1 w G).
      revert IHe1.
      apply wlp_monotonic.
      intros w1 r1 t1 H1.
      rewrite wlp_bind.
      specialize (IHe2 w1 (persist _ G _ r1)).
      revert IHe2.
      apply wlp_monotonic.
      intros w2 r2 t2 H2.
      rewrite wlp_mexists.
      rewrite wlp_bind.
      unfold WLP at 1, mgu.
      destruct (mgu_spec
                  <{ t1 ~ r2 ⊙ˢ Sub.step }>
                  (Ty_func (w2 ▻ 0) <{ t2 ~ Sub.step }> (Ty_hole (w2 ▻ 0) 0 ctx.in_zero)))
        as [(w3 & r3 & [])|]; [|constructor].
      constructor.
      rewrite wlp_pure.
      intros ι.
      (* Need composition of assignments with Subs *)
      admit.
  Admitted.

  Definition REL (A : World -> Type) : Type :=
    forall w0 w1 (r1 : w0 ⊒ˢ w1),
      A w0 -> A w1 -> Prop.

  Definition RBox {A} (R : REL A) : REL □ˢA :=
    fun w0 w1 r01 ba0 ba1 =>
      forall (w2 w3 : World) (r02 : w0 ⊒ˢ w2) (r13 : w1 ⊒ˢ w3) (r23 : w2 ⊒ˢ w3),
        r01 ⊙ˢ r13 = r02 ⊙ˢ r23 ->
        R w2 w3 r23 (ba0 w2 r02) (ba1 w3 r13).

   (*         r01 *)
   (*    w0 -------> w1 *)
   (*     |          | *)
   (* r02 |          | r13 *)
   (*     |    //    | *)
   (*     ↓          ↓ *)
   (*    w2 -------> w3 *)
   (*         r23 *)

  Definition RDSub {A} (R : REL A) : REL <[Sub]>A.
  Proof.
    intros w0 w1 r01.
    intros (w2 & r02 & a2).
    intros (w3 & r13 & a3).
    refine (exists r23,
               r01 ⊙ˢ r13 = r02 ⊙ˢ r23 /\ R _ _ r23 a2 a3).
  Defined.

  Definition RImpl {A B} (RA : REL A) (RB : REL B) : REL (Impl A B) :=
    fun w0 w1 r01 f0 f1 =>
      forall a0 a1,
        RA w0 w1 r01 a0 a1 ->
        RB w0 w1 r01 (f0 a0) (f1 a1).

  Definition ROption {A} (R : REL A) : REL (Option A) :=
    fun w0 w1 r01 m0 m1 =>
      match m0 , m1 with
      | Some a0 , Some a1 => R w0 w1 r01 a0 a1
      | Some _  , None    => True
      | None    , Some _  => False
      | None    , None    => True
      end.

  Definition RTy : REL Ty :=
    fun w0 w1 r01 t0 t1 =>
      t1 = Sub.subst t0 r01.

  Lemma rty_bool {w0 w1 r01} :
    RTy w0 w1 r01 (Ty_bool _) (Ty_bool _).
  Proof.
    reflexivity.
  Qed.

  Lemma rty_func {w0 w1 r01} t1_0 t1_1 t2_0 t2_1 :
    RTy w0 w1 r01 t1_0 t1_1 ->
    RTy w0 w1 r01 t2_0 t2_1 ->
    RTy w0 w1 r01 (Ty_func _ t1_0 t2_0) (Ty_func _ t1_1 t2_1).
  Proof. unfold RTy; cbn; intros; now f_equal. Qed.

  Definition REnv : REL Env.
  Admitted.

  Definition RM {A} (R : REL A) : REL (M A) :=
    ROption (RDSub R).

  Definition RValid {A} (R : REL A) (a : ⊢ A) : Prop :=
    forall w0 w1 r01,
      R w0 w1 r01 (a w0) (a w1).

  Definition RUnit : REL Unit :=
    fun _ _ _ _ _ => True.

  Lemma rsome {A} (R : REL A) w0 w1 (r01 : Sub w0 w1) (a0 : A w0) (a1 : A w1) (ra : R w0 w1 r01 a0 a1) :
    ROption R w0 w1 r01 (Some a0) (Some a1).
  Proof. apply ra. Qed.

  Lemma rpure {A} (R : REL A) :
    RValid (RImpl R (RM R)) pure.
  Proof.
    intros w0 w1 r01 a0 a1 ra.
    refine (@rsome _ (RDSub R) w0 w1 r01 _ _ _).
    unfold RDSub. exists r01. split; auto.
    now rewrite Sub.comp_id_left, Sub.comp_id_right.
  Qed.

  Lemma rbind {A B} (RA : REL A) (RB : REL B) :
    RValid (RImpl (RM RA) (RImpl (RBox (RImpl RA (RM RB))) (RM RB))) bind.
  Proof.
    unfold RValid, RImpl, RBox, RM.
    intros w0 w1 r01.
    intros [(w2 & r2 & a2)|] [(w3 & r3 & a3)|] rm f0 f1 rf; cbn in rm.
    - destruct rm as (r23 & Heqr & ra).
      specialize (rf _ _ r2 r3 r23 Heqr _ _ ra).
      cbn. revert rf.
      destruct f0 as [(w4 & r4 & b4)|], f1 as [(w5 & r5 & b5)|]; cbn.
      + intros (r45 & Heqr2 & rb).
        exists r45.
        rewrite <- ?Sub.comp_assoc.
        rewrite Heqr.
        rewrite ?Sub.comp_assoc.
        now rewrite Heqr2.
      + auto.
      + auto.
      + auto.
    - cbn. destruct f0 as [(w4 & r4 & b4)|]; cbn.
      + auto.
      + auto.
    - cbn. destruct f1 as [(w5 & r5 & b5)|]; cbn.
      + auto.
      + auto.
    - cbn.
      auto.
  Qed.

  Lemma rmgu :
    RValid (RImpl RTy (RImpl RTy (RM RUnit))) mgu.
  Proof.
    unfold RValid, RImpl, RM, RUnit.
    intros w0 w1 r01 t1_0 t1_1 rt1 t2_0 t2_1 rt2.
    unfold mgu.
    destruct (mgu_spec t1_0 t2_0) as [(w2 & r02 & ?)|],
        (mgu_spec t1_1 t2_1) as [(w3 & r13 & ?)|]; cbn.
    - unfold RTy in *.
      clear u u0.
      subst.
      destruct H0 as [H0 _].
      destruct H as [_ H].
      unfold P.unifies in *.
      specialize (H _ (r01 ⊙ˢ Sub.triangular r13)).
      rewrite ?Sub.subst_comp in H.
      specialize (H H0).
      destruct H as (r23 & ?).
      exists r23. split; auto.
    - auto.
    - apply (H w3 (r01 ⊙ˢ Sub.triangular r13)).
      destruct H0 as [H0 _].
      unfold RTy in *.
      subst. unfold P.unifies in *.
      now rewrite ?Sub.subst_comp, H0.
    - auto.
  Qed.

  Definition rexists {A} (R : REL A) w0 w1 (r01 : Sub w0 w1) {n} (m0 : M A (w0 ▻ n)) (m1 : M A (w1 ▻ n)) :
    RM R (w0 ▻ n) (w1 ▻ n) (Sub.up1 r01) m0 m1 ->
    RM R w0 w1 r01 (mexists m0) (mexists m1).
  Proof.
    unfold RM, ROption, mexists.
    destruct m0 as [(w2 & r02 & a2)|], m1 as [(w3 & r13 & a3)|]; cbn - [Sub.step Sub.up1]; auto.
    intros (r23 & Heqr & ra).
    exists r23. split; auto.
    rewrite Sub.comp_assoc, <- Heqr.
    clear.
    rewrite <- ?Sub.comp_assoc. f_equal.
    admit.
  Admitted.

  Arguments mexists : simpl never.

  Lemma infer_mon (e : expr) :
    RValid (RImpl REnv (RM RTy)) (infer e).
  Proof.
    induction e; cbn [infer]; intros w0 w1 r01 G0 G1 HG.
    - apply rpure. apply rty_bool.
    - apply rpure. apply rty_bool.

    - eapply rbind. now apply IHe1.
      intros w2 w3 r02 r13 r23 Heqr23 t1_2 t1_3 rt1.
      eapply rbind. apply rmgu; auto. apply rty_bool.
      intros w4 w5 r24 r35 r45 Heqr45 _ _ _.
      eapply rbind. apply IHe2. admit.
      intros w6 w7 r46 r57 r67 Heqr67 t2_6 t2_7 rt2.
      eapply rbind. apply IHe3. admit.
      intros w8 w9 r68 r89 r79 Heqr79 t3_8 t3_9 rt3.
      eapply rbind. apply rmgu; auto.
      { unfold RTy in *. subst.
        unfold persist, PersistentSub_Ty.
        now rewrite <- ?Sub.subst_comp, Heqr79.
      }
      intros ? ? ? ? ? ? _ _ _.
      apply rpure.
      { unfold RTy in *. subst.
        unfold persist, PersistentSub_Ty.
        now rewrite <- ?Sub.subst_comp, H.
      }

    - admit.

    - apply rexists.
      eapply rbind. apply IHe. admit.
      intros w2 w3 r02 r13 r23 Heqr23 t1_2 t1_3 rt1.
      apply rpure.
      apply rty_func; auto.
      { unfold RTy in *. subst.
        unfold persist, PersistentSub_Ty.
        now rewrite <- Sub.subst_comp, <- Heqr23.
      }

    - eapply rbind. apply IHe. admit.
      intros w2 w3 r02 r13 r23 Heqr23 t1_2 t1_3 rt1.
      apply rpure.
      apply rty_func; auto.
      { unfold RTy. now rewrite subst_lift. }

    - eapply rbind. apply IHe1; auto.
      intros w2 w3 r02 r13 r23 Heqr23 t1_2 t1_3 rt1.
      eapply rbind. apply IHe2; auto. admit.
      intros w4 w5 r24 r35 r45 Heqr45 t2_4 t2_5 rt2.
      apply rexists.
      eapply rbind. apply rmgu.
      { unfold RTy in *. subst.
        unfold persist, PersistentSub_Ty.
        rewrite <- ?Sub.subst_comp. f_equal.
        rewrite <- Sub.comp_assoc.
        rewrite Heqr45.
        rewrite ?Sub.comp_assoc. f_equal.
        admit.
      }
      { unfold RTy in *. subst.
        unfold persist, PersistentSub_Ty.
        cbn - [Sub.step].
        rewrite <- ?Sub.subst_comp.
        f_equal.
        f_equal.
        admit.
      }
      intros w6 w7 r46 r57 r67 Heqr6 _ _ _.
      apply rpure.
      { unfold RTy in *. subst.
        unfold persist, PersistentSub_Ty.
        rewrite <- ?Sub.subst_comp.
        now rewrite <- Heqr6.
      }
  Admitted.

  Definition RPropImpl : REL PROP :=
    fun w0 w1 r01 p q => (q -> p)%type.

  Lemma wp_monotonic_strong {A} (R : REL A) :
    RValid (RImpl (RM R) (RImpl (RBox (RImpl R RPropImpl)) RPropImpl)) WP.
  Proof.
    intros w0 w1 r01 m0 m1 rm p0 p1 rp.
    unfold RBox, RImpl, RPropImpl in *.
    unfold RM, ROption, RDSub in rm.
    destruct m0 as [(w2 & r02 & a2)|], m1 as [(w3 & r13 & a3)|].
    - unfold RM, ROption, RDSub in rm.
      destruct rm as (r23 & Heqr & ra).
      unfold WP. rewrite option.wp_match.
      intros Hp1. constructor. revert Hp1.
      eapply rp; eauto.
    - inversion 1.
    - destruct rm.
    - inversion 1.
  Qed.

  Lemma completeness {G e t ee} (R : G |-- e ; t ~> ee) :
    forall w : World,
      WP w (infer e w (liftEnv G w))
        (fun w1 r1 T =>
           forall w2 (r2 : w1 ⊒ˢ w2),
           exists w3 (r3 : w2 ⊒ˢ w3), <{ T ~ r2 ⊙ˢ r3 }> = lift t w3).
  Proof.
    Set Printing Depth 18.
    induction R; cbn - [Sub.step Sub.subst persist]; intros w.
    - rewrite wp_pure. intros w2 r2. exists w2. exists Sub.id. reflexivity.
    - rewrite wp_pure. intros w2 r2. exists w2. exists Sub.id. reflexivity.

    - rewrite wp_bind.
      specialize (IHR1 w). revert IHR1.
      apply wp_monotonic. intros w1 r1 t1 H1.
      rewrite wp_bind.
      unfold mgu at 1, WP at 1.
      rewrite option.wp_bind.
      destruct (mgu_spec t1 (Ty_bool w1)) as [(w2 & r2 & [])|].
      2: {
        exfalso.
        destruct (H1 w1 Sub.id) as (w2 & r2 & Heq).
        rewrite Sub.comp_id_left in Heq.
        eapply (H w2 r2); clear H.
        apply Heq.
      }
      constructor.
      constructor.
      rewrite wp_bind.
      specialize (IHR2 w2). revert IHR2.
      rewrite persist_liftEnv.
      apply wp_monotonic.
      intros w3 r3 t2 H2.
      rewrite wp_bind.
      specialize (IHR3 w3). revert IHR3.
      rewrite persist_liftEnv.
      apply wp_monotonic.
      intros w4 r4 t3 H3.
      rewrite wp_bind.
      unfold mgu at 1, WP at 1.
      rewrite option.wp_bind.
      destruct (mgu_spec <{ t2 ~ r4 }> t3) as [(w5 & r5 & [])|].
      2: {
        exfalso.
        specialize (H3 w4 Sub.id). destruct H3 as (w5 & r5 & H3).
        rewrite Sub.comp_id_left in H3.
        specialize (H2 w5 (r4 ⊙ˢ r5)). destruct H2 as (w6 & r6 & H2).
        apply (H0 w6 (r5 ⊙ˢ r6)). clear - H2 H3.
        cbv [P.max P.unifies persist PersistentSub_Ty] in *.
        repeat rewrite Sub.subst_comp in *.
        rewrite H2, H3. rewrite subst_lift. easy.
      }

      constructor.
      constructor.
      rewrite wp_pure.
      unfold T, _4.
      intros w6 r6. specialize (H3 w6 (Sub.triangular r5 ⊙ˢ r6)).
      destruct H3 as (w7 & r7 & H3).
      exists w7. exists r7. clear - H3.
      cbv [P.max P.unifies persist PersistentSub_Ty] in *.
      now repeat rewrite Sub.subst_comp in *.

    - rewrite value_lift. rewrite H. cbn.
      rewrite wp_pure. intros w1 r1.
      exists w1. exists Sub.id.
      now rewrite persist_liftTy.

    - rewrite wp_mexists.
      rewrite wp_bind.
      specialize (IHR w). revert IHR.
      rewrite persist_liftEnv.
      cbn - [Sub.subst].
      apply (wp_monotonic_strong RTy (w ▻ 0) w (Sub.thick ctx.in_zero (lift vt _))).
      cbn - [Sub.thick].
      apply infer_mon. admit.
      intros w2 w3 r02 r13 r23 Heq t_2 t_3 rt IH.
      cbn - [Sub.thick] in Heq.
      rewrite wp_pure.
      unfold RTy in *. subst.
      unfold T, _4, persist,  PersistentSub_Ty in *.
      remember (Ty_hole (w ▻ 0) 0 ctx.in_zero) as tfresh.
      admit.

    - rewrite wp_bind.
      specialize (IHR w). revert IHR.
      apply wp_monotonic.
      intros w1 r1 t1 H1.
      rewrite wp_pure.
      intros w2 r2.
      specialize (H1 w2 r2). destruct H1 as (w3 & r3 & H1).
      exists w3, r3. cbn. f_equal.
      + now rewrite subst_lift.
      + apply H1.

    - rewrite wp_bind.
      specialize (IHR1 w). revert IHR1.
      apply wp_monotonic.
      intros w1 r1 tf H1.
      rewrite wp_bind.
      specialize (IHR2 w1). revert IHR2.
      rewrite persist_liftEnv.
      apply wp_monotonic.
      intros w2 r2 ta H2.
      rewrite wp_mexists.
      rewrite wp_bind.
      unfold mgu, WP at 1.
      rewrite option.wp_bind.
      destruct
        (mgu_spec
         <{ tf ~ r2 ⊙ˢ Sub.step }>
           (Ty_func (w2 ▻ 0) <{ ta ~ Sub.step }> (Ty_hole (w2 ▻ 0) 0 ctx.in_zero)))
        as [(w3 & r3' & [])|].
      2: {
        exfalso.
        specialize (H1 w2 r2).
        destruct H1 as (w3 & r3 & H1).
        specialize (H2 w3 r3). destruct H2 as (w4 & r4 & H2).
        apply (H w4 (Sub.thick ctx.in_zero (lift t1 _) ⊙ˢ r3 ⊙ˢ r4)).
        cbv [P.max P.unifies persist PersistentSub_Ty Sub.step] in *.
        cbn - [Sub.thin Sub.thick].
        repeat rewrite Sub.subst_comp in *.
        rewrite
          (Sub.thin_thick_pointful
             ctx.in_zero
             (lift t1 w2)
             (Sub.subst tf r2)).
        rewrite
          (Sub.thin_thick_pointful
             ctx.in_zero
             (lift t1 w2)
             ta).
        cbn. now rewrite H1, H2, ?subst_lift.
      }
      constructor.
      constructor.
      rewrite wp_pure.
      destruct H as [Hu _].
      cbv [P.max P.unifies persist PersistentSub_Ty Sub.step] in *.
      remember (Sub.triangular r3') as r3.
      clear r3' Heqr3.
      intros w4 r4.
      specialize (H1 w4 (r2 ⊙ˢ Sub.thin ctx.in_zero ⊙ˢ r3 ⊙ˢ r4)).
      destruct H1 as (w5 & r5 & H1).
      specialize (H2 w5 (Sub.thin ctx.in_zero ⊙ˢ r3 ⊙ˢ r4 ⊙ˢ r5)).
      destruct H2 as (w6 & r6 & H2).
      cbn - [Sub.thin Sub.thick] in *.
      exists w6, (r5 ⊙ˢ r6).
      rewrite ?Sub.subst_comp in *.
      rewrite Hu in H1. clear Hu.
      cbn - [Sub.thin] in H1.
      injection H1. intros H11 H12. clear H1.
      now rewrite H11, subst_lift.

  Admitted.

End EagerSolving.

(* Focus on the constraint generation only, forget about solving constraints
   and any semantic values. Also try to pass the type as an input instead of
   an output, i.e. checking instead of synthesizing. *)
Module ConstraintsOnly.

  Import option.notations.
  Import Unification.

  #[local] Set Implicit Arguments.
  #[local] Arguments Sub.step : simpl never.

  Module C.

    Inductive CStr (w : World) : Type :=
    | False
    | Eq (t1 t2 : Ty w)
    | And (C1 C2 : CStr w)
    | Ex {x} (C : CStr (w ▻ x)).
    #[global] Arguments False {w}.
    #[global] Arguments Ex [w] x C.

    Definition denote : ⊢ CStr -> Lifted Prop :=
      fix den {w} C ι {struct C} : Prop :=
        match C with
        | False     => Logic.False
        | Eq t1 t2  => inst t1 ι = inst t2 ι
        | And C1 C2 => den C1 ι /\ den C2 ι
        | Ex x C    => exists t, den C (env.snoc ι x t)
        end.

  End C.
  Export C (CStr).

  Notation "C1 /\ C2" := (C.And C1 C2).
  Notation "t1 == t2" := (C.Eq t1 t2) (at level 80).
  Notation "∃ n , C" := (C.Ex n C) (at level 80, right associativity, format "∃ n ,  C").

  Fixpoint check (e : expr) : ⊢ Env -> Ty -> CStr :=
    fun (w : World) (G : Env w) (tr : Ty w) =>
      match e with
      | e_if e1 e2 e3 =>
          check e1 G (Ty_bool w) /\
          check e2 G tr /\
          check e3 G tr
      | e_var s =>
          match value s G with
          | Some a => tr == a
          | None => C.False
          end
      | e_absu x e =>
          ∃1, ∃2,
            let G'  := <{ G ~ Sub.step ⊙ˢ Sub.step }> in
            let tr' := <{ tr ~ Sub.step ⊙ˢ Sub.step }> in
            let α1  := Ty_hole (w ▻ 1 ▻ 2) 1 (ctx.in_succ ctx.in_zero) in
            let α2  := Ty_hole (w ▻ 1 ▻ 2) 2 ctx.in_zero in
            (tr' == Ty_func _ α1 α2) /\
            check e ((x, α1) :: G') α2
      | e_abst x xt e =>
          ∃2,
            let G'  := <{ G ~ Sub.step }> in
            let tr' := <{ tr ~ Sub.step }> in
            let α1  := lift xt _ in
            let α2  := Ty_hole (w ▻ 2) 2 ctx.in_zero in
            (tr' == Ty_func _ α1 α2) /\
            check e ((x, α1) :: G') α2
      | e_app e1 e2 =>
          ∃0,
            let G'  := <{ G ~ Sub.step }> in
            let tr' := <{ tr ~ Sub.step }> in
            let α   := Ty_hole (w ▻ 0) 0 ctx.in_zero in
            check e1 G' (Ty_func _ α tr') /\
            check e2 G' α
      | _ => tr == Ty_bool w
      end.

  Lemma soundness e :
    forall (w : World) G t (ι : Assignment w),
      C.denote (check e G t) ι ->
      exists ee, inst G ι |-- e ; inst t ι ~> ee.
  Proof.
    induction e; cbn; intros w G tr ι.
    - intros ->. eexists. constructor.
    - intros ->. eexists. constructor.
    - intros (H1 & H2 & H3).
      specialize (IHe1 _ _ _ _ H1). clear H1. destruct IHe1 as (e1' & HT1).
      specialize (IHe2 _ _ _ _ H2). clear H2. destruct IHe2 as (e2' & HT2).
      specialize (IHe3 _ _ _ _ H3). clear H3. destruct IHe3 as (e3' & HT3).
      eexists. constructor; eauto.
    - destruct value eqn:?; cbn; intros Heq; [|contradiction].
      eexists. constructor. now rewrite value_inst, Heqo, Heq.
    - intros (t1 & t2 & H1 & H2).
      specialize (IHe _ _ _ _ H2). clear H2.
      destruct IHe as (e1' & HT). cbn in HT.
      assert (inst (persist _ G _ (Sub.step ⊙ˢ Sub.step)) (env.snoc (env.snoc ι 1 t1) 2 t2) = inst G ι).
      { clear. admit. }.
      rewrite H in HT. clear H.
      assert (inst <{ tr ~ Sub.step ⊙ˢ Sub.step }> (env.snoc (env.snoc ι 1 t1) 2 t2) = inst tr ι).
      { clear. admit. }.
      rewrite H in H1. clear H. rewrite H1. clear H1.
      eexists. constructor. eauto.
    - intros (t1 & H1 & H2).
      specialize (IHe _ _ _ _ H2). clear H2.
      destruct IHe as (e' & HT). cbn in HT.
      assert (inst (persist _ G _ Sub.step) (env.snoc ι 2 t1) = inst G ι).
      { clear. admit. }.
      rewrite H in HT. clear H.
      assert (inst (persist _ tr _ Sub.step) (env.snoc ι 2 t1) = inst tr ι).
      { clear. admit. }.
      rewrite H in H1. clear H. rewrite H1. clear H1.
      rewrite inst_lift in HT. rewrite inst_lift.
      eexists. constructor. eauto.
    - intros (t1 & H1 & H2).
      specialize (IHe1 _ _ _ _ H1). clear H1. destruct IHe1 as (e1' & HT1).
      specialize (IHe2 _ _ _ _ H2). clear H2. destruct IHe2 as (e2' & HT2).
      exists (e_app e1' e2').
      cbn in HT1, HT2.
      assert (inst <{ G ~ Sub.step }> (env.snoc ι 0 t1) = inst G ι) by admit.
      rewrite H in *. clear H.
      assert (inst <{ tr ~ Sub.step }> (env.snoc ι 0 t1) = inst tr ι) by admit.
      rewrite H in *. clear H.
      econstructor; eauto.
  Admitted.

  Lemma completeness_aux {G e t ee} (T : G |-- e; t ~> ee) :
    forall (w0 : World) (ι0 : Assignment w0) (G0 : Env w0) (t0 : Ty w0),
      G = inst G0 ι0 -> t = inst t0 ι0 -> C.denote (check e G0 t0) ι0.
  Proof.
    induction T; cbn; intros w0 ι0 G0 t0 ? ?; subst.
    - auto.
    - auto.
    - intuition.
    - rewrite value_inst in H.
      destruct value; [|discriminate].
      now injection H.
    - exists vt. exists t. rewrite H0.
      split. admit.
      apply IHT; cbn. f_equal. admit.
      reflexivity.
    - exists t. rewrite inst_lift. rewrite H0.
      split. admit.
      apply IHT; cbn. rewrite inst_lift.
      f_equal. admit.
      reflexivity.
    - exists t2. split.
      apply IHT1; cbn. admit.
      f_equal. admit.
      apply IHT2; cbn. admit.
      reflexivity.
  Admitted.

  Lemma completeness G e t ee (T : G |-- e ; t ~> ee) :
    C.denote (check e (liftEnv G _) (lift t _)) env.nil.
  Proof.
    eapply completeness_aux; eauto.
    - admit.
    - now rewrite inst_lift.
  Admitted.

End ConstraintsOnly.

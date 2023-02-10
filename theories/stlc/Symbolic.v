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

Module UpDown.
  #[local] Notation "□⇅ A" := (BoxR Acc A) (at level 9, format "□⇅ A", right associativity)
      : indexed_scope.
  #[local] Notation "□ˢ A" :=
    (BoxR Sub A)
      (at level 9, format "□ˢ A", right associativity)
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

  (* Remove phase separation and all abstractions to get
     a base line. *)
  Module EagerSolving.

    Import option.notations.
    Import Unification.

    #[local] Arguments Sub.thin : simpl never.

    Definition M (A : TYPE) : TYPE :=
      Option (DiamondR Sub A).

    Definition pure {A} : ⊢ A -> M A :=
      fun w a => Some (existT _ w (Sub.id, a)).

    Definition bind {A B} : ⊢ M A -> □ˢ(A -> (M B)) -> M B :=
      fun w m f =>
        '(existT _ w1 (r1,a1)) <- m;;
        '(existT _ w2 (r2,b2)) <- f w1 r1 a1;;
        Some (existT _ w2 (r1 ⊙ˢ r2, b2)).

    Fixpoint infer (e : expr) : ⊢ Env -> M Ty :=
      fun w G =>
        match e with
        | v_true => pure w (Ty_bool w)
        | v_false => pure w (Ty_bool w)
        | e_if e1 e2 e3 =>
            '(existT _ w1 (r1 , t1)) <- infer e1 w G;;
            '(existT _ w2 (r2' , _)) <- mgu t1 (Ty_bool w1);;
            let r2 := Sub.triangular r2' in
            let G2 := <{ G ~ r1 ⊙ˢ r2 }> in
            '(existT _ w3 (r3, t2)) <- infer e2 w2 G2;;
            let G3 := <{ G2 ~ r3 }> in
            '(existT _ w4 (r4, t3)) <- infer e3 w3 G3;;
            '(existT _ w5 (r5' , _)) <- mgu <{ t2 ~ r4 }> t3;;
            let r5 := Sub.triangular r5' in
            Some (existT _ w5 (r1 ⊙ˢ (r2 ⊙ˢ (r3 ⊙ˢ (r4 ⊙ˢ r5))), <{ t3 ~ r5 }>))
        | e_var s => match value s G with
                     | Some t => pure w t
                     | None => None
                     end
        | e_absu s e =>
            let w1 := w ▻ 0 in
            let r1 := Sub.step in
            let t1 := Ty_hole w1 0 ctx.in_zero in
            '(existT _ w2 (r2,t2)) <- infer e w1 ((s, t1) :: <{ G ~ r1 }>);;
            Some (existT _ w2 (r1 ⊙ˢ r2, Ty_func _ <{ t1 ~ r2 }> t2))
        | e_abst s t e =>
            let t1 := lift t w in
            '(existT _ w1 (r1,t2)) <- infer e w ((s, t1) :: G);;
            Some (existT _ w1 (r1, Ty_func _ <{ t1 ~ r1 }> t2))
        | e_app e1 e2 =>
            '(existT _ w1 (r1,t1)) <- infer e1 w G;;
            let G1 := <{ G ~ r1 }> in
            '(existT _ w2 (r2,t2)) <- infer e2 w1 G1;;
            let w3 := w2 ▻ 0 in
            let r3 := Sub.step in
            let ti := Ty_hole w3 0 ctx.in_zero in
            let G3 := <{ G1 ~ r2 ⊙ˢ r3 }> in
            '(existT _ w4 (r4', _)) <-
               mgu
                 <{ t1 ~ r2 ⊙ˢ r3 }>
                 (Ty_func _ <{ t2 ~ r3 }> ti);;
            let r4 := Sub.triangular r4' in
            Some (existT _ w4 (r1 ⊙ˢ (r2 ⊙ˢ (r3 ⊙ˢ r4)), <{ ti ~ r4 }>))
        end.

    Lemma soundness e :
      forall (w : World) G,
        option.wlp
          (fun '(existT _ w1 (r1, b)) =>
             forall ι : Assignment w1,
               exists ee, inst <{ G ~ r1 }> ι |-- e ; inst b ι ~> ee)
          (infer e w G).
    Proof.
      induction e; cbn; intros w G; unfold pure.
      - constructor; intros ι. exists v_true; cbn. constructor.
      - constructor; intros ι. exists v_false; cbn. constructor.
      - rewrite option.wlp_bind.
        specialize (IHe1 w G). revert IHe1.
        apply option.wlp_monotonic.
        intros (w1 & r1 & t1) H1.
        rewrite option.wlp_bind.
        destruct (mgu_spec t1 (Ty_bool w1)) as [(w2 & r2 & [])|]; [|constructor].
        constructor.
        rewrite option.wlp_bind.
        specialize (IHe2 w2 (persist w G w2 (r1 ⊙ˢ Sub.triangular r2))).
        revert IHe2.
        apply option.wlp_monotonic.
        intros (w3 & r3 & t2) H2.
        rewrite option.wlp_bind.
        specialize (IHe3 w3 (persist w2 (persist w G w2 (r1 ⊙ˢ Sub.triangular r2)) w3 r3)).
        revert IHe3.
        apply option.wlp_monotonic.
        intros (w4 & r4 & t3) H3.
        rewrite option.wlp_bind.
        destruct (mgu_spec (persist w3 t2 w4 r4) t3) as [(w5 & r5 & [])|]; [|constructor].
        constructor. constructor. intros ι.
        (* Need composition of assignments with Subs. *)
        admit.
      - destruct value eqn:?.
        + constructor. intros. exists (e_var s).
          constructor.
          (* need value inst lemma, and persist_subid *)
          admit.
        + constructor.
      - rewrite option.wlp_bind.
        specialize (IHe (w ▻ 0) (cons (pair s (Ty_hole (ctx.snoc w 0) 0 ctx.in_zero)) (persist w G (ctx.snoc w 0) Sub.step))).
        revert IHe.
        apply option.wlp_monotonic.
        intros (w1 & r1 & t1) H1.
        constructor.
        intros ι. specialize (H1 ι). destruct H1 as [e' HT1].
        cbn. eexists. constructor. cbn in *.
        (* need persist acc_trans lemma *)
        admit.
      - rewrite option.wlp_bind.
        specialize (IHe w (cons (pair s (lift t w)) G)).
        revert IHe.
        apply option.wlp_monotonic.
        intros (w1 & r1 & t1) H1.
        constructor.
        intros ι. specialize (H1 ι). destruct H1 as [e' HT1].
        cbn. eexists.
        (* need inst lift lemma *)
        admit.
      - rewrite option.wlp_bind.
        specialize (IHe1 w G).
        revert IHe1.
        apply option.wlp_monotonic.
        intros (w1 & r1 & t1) H1.
        rewrite option.wlp_bind.
        specialize (IHe2 w1 (persist _ G _ r1)).
        revert IHe2.
        apply option.wlp_monotonic.
        intros (w2 & r2 & t2) H2.
        rewrite option.wlp_bind.
        destruct (mgu_spec
                    <{ t1 ~ r2 ⊙ˢ Sub.step }>
                    (Ty_func (w2 ▻ 0) <{ t2 ~ Sub.step }> (Ty_hole (w2 ▻ 0) 0 ctx.in_zero)))
          as [(w3 & r3 & [])|]; [|constructor].
        constructor. constructor. intros ι.
        (* Need composition of assignments with Subs *)
        admit.
    Admitted.

    Lemma completeness {G e t ee} (R : G |-- e ; t ~> ee) :
      forall w : World,
        option.wp
          (fun '(existT _ w1 (r1, b)) =>
             forall w2 (r2 : w1 ⊒ˢ w2),
             exists w3 (r3 : w2 ⊒ˢ w3), <{ b ~ r2 ⊙ˢ r3 }> = lift t w3)
          (infer e w (liftEnv G w)).
    Proof.
      induction R; cbn - [Sub.step Sub.subst persist]; intros w; unfold pure.
      - constructor. intros w2 r2. exists w2. exists Sub.id. reflexivity.
      - constructor. intros w2 r2. exists w2. exists Sub.id. reflexivity.

      - rewrite option.wp_bind.
        specialize (IHR1 w). revert IHR1.
        apply option.wp_monotonic.
        intros (w1 & r1 & t1) H1.
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
        rewrite option.wp_bind.
        specialize (IHR2 w2). revert IHR2.
        rewrite persist_liftEnv.
        apply option.wp_monotonic.
        intros (w3 & r3 & t2) H2.
        rewrite option.wp_bind.
        specialize (IHR3 w3). revert IHR3.
        rewrite persist_liftEnv.
        apply option.wp_monotonic.
        intros (w4 & r4 & t3) H3.
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
        intros w6 r6. specialize (H3 w6 (Sub.triangular r5 ⊙ˢ r6)).
        destruct H3 as (w7 & r7 & H3).
        exists w7. exists r7. clear - H3.
        cbv [P.max P.unifies persist PersistentSub_Ty] in *.
        now repeat rewrite Sub.subst_comp in *.

      - rewrite value_lift. rewrite H.
        constructor. intros. exists w2. exists Sub.id.
        now rewrite persist_liftTy.

      - rewrite option.wp_bind.
        specialize (IHR (w ▻ 0)). revert IHR.
        rewrite persist_liftEnv. cbn.
        rename v into x.
        admit.

      - rewrite option.wp_bind.
        specialize (IHR w). revert IHR.
        apply option.wp_monotonic.
        intros (w1 & r1 & t1) H1.
        constructor.
        intros w2 r2.
        specialize (H1 w2 r2). destruct H1 as (w3 & r3 & H1).
        exists w3, r3. cbn. f_equal.
        + now rewrite persist_liftTy, subst_lift.
        + apply H1.

      - rewrite option.wp_bind.
        specialize (IHR1 w). revert IHR1.
        apply option.wp_monotonic.
        intros (w1 & r1 & tf) H1.
        rewrite option.wp_bind.
        specialize (IHR2 w1). revert IHR2.
        rewrite persist_liftEnv.
        apply option.wp_monotonic.
        intros (w2 & r2 & ta) H2.
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

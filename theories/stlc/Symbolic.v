Require Import List.
Import ListNotations.
From Em Require Import
     Definitions Context Environment STLC Prelude Substitution Triangular.
Import ctx.notations.
From Em Require
  Unification.
From Equations Require Import Equations.

Local Notation "<{ A ~ w }>" := (persist _ A _ w).

#[export] Instance PersistentTri_Ty : Persistent Tri Ty :=
  fun w1 t w2 ζ => Sub.subst t (Sub.triangular ζ).
#[export] Instance PersistentSub_Ty : Persistent Sub Ty :=
  fun w1 t w2 ζ => Sub.subst t ζ.
#[export] Instance persistent_unit {R} : Persistent R Unit :=
  fun w1 u w2 ζ => u.
Open Scope indexed_scope.

Definition assert {w} t1 t2 :=
  Bind_AssertEq_Free Unit w t1 t2 (Ret_Free Unit w tt).

Definition exists_Ty : forall Σ, FreeM Ty Σ :=
  fun Σ => let i := ctx.length Σ in
           Bind_Exists_Free Ty Σ i (Ret_Free _ _ (Ty_hole _ i ctx.in_zero)).

(* Indexes a given ty by a world Σ *)
Fixpoint lift (t : ty) : ⊢ Ty :=
  fun w =>
    match t with
    | ty_bool       => Ty_bool w
    | ty_func t1 t2 => Ty_func w (lift t1 w) (lift t2 w)
    end.

Fixpoint liftEnv (E : env) : ⊢ Env :=
  fun w =>
    match E with
    | List.nil               => List.nil
    | List.cons (pair s t) E => cons (pair s (lift t w)) (liftEnv E w)
    end.

Section Generate.
  Import MonadNotations.

  Fixpoint generate (e : expr) {Σ : World} (Γ : Env Σ) : FreeM Ty Σ :=
    match e with
    | v_true => Ret_Free Ty Σ (Ty_bool Σ)
    | v_false => Ret_Free Ty Σ (Ty_bool Σ)
    | e_if cnd coq alt =>
        [ ω₁ ] t_cnd <- generate cnd Γ ;;
        [ ω₂ ] _     <- assert t_cnd (Ty_bool _) ;;
        [ ω₃ ] t_coq <- generate coq <{ Γ ~ ω₁ ⊙ ω₂ }> ;;
        [ ω₄ ] t_alt <- generate alt <{ Γ ~ ω₁ ⊙ ω₂ ⊙ ω₃ }> ;;
        [ ω₅ ] _     <- assert <{ t_coq ~ ω₄ }>  t_alt ;;
           Ret_Free Ty _ <{ t_coq ~ ω₄ ⊙ ω₅ }>
    | e_var var =>
        match (resolve var Γ) with
        | Some t_var => Ret_Free Ty _ t_var
        | None => Fail_Free Ty Σ
        end
    | e_app f a =>
        [ ω1 ] t_co <- exists_Ty Σ ;;
        [ ω2 ] t_do <- generate a <{ Γ ~ ω1 }> ;;
        [ ω3 ] t_fn <- generate f <{ Γ ~ ω1 ⊙ ω2 }> ;;
        [ ω4 ] _    <- assert t_fn <{ (Ty_func _ t_do <{ t_co ~ ω2 }> ) ~ ω3 }> ;;
           Ret_Free Ty _ <{ t_co ~ ω2 ⊙ ω3 ⊙ ω4 }>
    | e_abst var t_var e =>
        let t_var' := (lift t_var Σ) in (* t_var lives in ty, not in (Ty w) *)
        [ ω1 ] t_e <- generate e ((var, t_var') :: Γ) ;;
          Ret_Free Ty _ (Ty_func _ <{ t_var' ~ ω1 }> t_e)
    | e_absu var e =>
        [ ω1 ] t_var <- exists_Ty Σ ;;
        [ ω2 ] t_e <- generate e ((var, t_var) :: <{ Γ ~ ω1 }>) ;;
          Ret_Free Ty _ (Ty_func _ <{ t_var ~ ω2 }> t_e)
    end.

End Generate.

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

  #[export] Instance Persistent_Lifted {R : ACC} {A}
    {instR : forall w, Inst (R w) (Assignment w)} : Persistent R (Lifted A) :=
    fun w0 a w1 r1 ι1 => a (inst r1 ι1).

  Definition ret  {w} := Ret_Free (Prod Ty Expr) w.
  Definition fail {w} := Fail_Free (Prod Ty Expr) w.

  Import MonadNotations.

  Fixpoint reconstruct (e : expr) {Σ : World} (Γ : Env Σ) : FreeM (Prod Ty Expr) Σ :=
    match e with
    | v_true  => ret (Ty_bool Σ, (fun _ => v_true))
    | v_false => ret (Ty_bool Σ, (fun _ => v_false))
    | e_if cnd coq alt =>
        [ ω1 ] r_cnd <- reconstruct cnd Γ ;;
        [ ω2 ] _     <- assert (fst r_cnd) (Ty_bool _) ;;
        [ ω3 ] r_coq <- reconstruct coq <{ Γ ~ ω1 ⊙ ω2 }> ;;
        [ ω4 ] r_alt <- reconstruct alt <{ Γ ~ ω1 ⊙ ω2 ⊙ ω3 }> ;;
        [ ω5 ] _     <- assert <{ (fst r_coq) ~ ω4 }> (fst r_alt) ;;
           let e_cnd := <{ (snd r_cnd) ~ ω2 ⊙ ω3 ⊙ ω4 ⊙ ω5 }> in
           let e_coq := <{ (snd r_coq) ~ ω4 ⊙ ω5 }> in
           let t_coq := <{ (fst r_coq) ~ ω4 ⊙ ω5 }> in
           let e_alt := <{ (snd r_alt) ~ ω5 }> in
           ret (t_coq, fun a => (e_if (e_cnd a) (e_coq a) (e_alt a)))
    | e_var var =>
        match (resolve var Γ) with
        | Some t_var => ret (t_var, fun a => e_var var)
        | None => fail
        end
    | e_app f a =>
        [ ω1 ] T_cod <- exists_Ty Σ ;;
        [ ω2 ] r_dom <- reconstruct a <{ Γ ~ ω1 }> ;;
        [ ω3 ] r_fun <- reconstruct f <{ Γ ~ ω1 ⊙ ω2 }> ;;
        [ ω4 ] _     <- assert (fst r_fun) <{ (Ty_func _ (fst r_dom) <{ T_cod ~ ω2 }> ) ~ ω3 }> ;;
           let e_fun := <{ (snd r_fun) ~ ω4 }> in
           let t_cod := <{ T_cod ~ ω2 ⊙ ω3 ⊙ ω4 }> in
           let e_dom := <{ (snd r_dom) ~ ω3 ⊙ ω4 }> in
            ret ( t_cod , fun a => e_app (e_fun a) (e_dom a))
    | e_abst var t_var e =>
        let t_var' := (lift t_var Σ) in (* t_var lives in ty, not in (Ty w) *)
        [ ω1 ] t_e <- reconstruct e ((var, t_var') :: Γ) ;;
          ret (Ty_func _ <{ t_var' ~ ω1 }> (fst t_e), fun a => e_abst var t_var (snd t_e a))
    | e_absu var e =>
        [ ω1 ] t_var <- exists_Ty Σ ;;
        [ ω2 ] t_e <- reconstruct e ((var, t_var) :: <{ Γ ~ ω1 }>) ;;
          ret (Ty_func _ <{ t_var ~ ω2 }> (fst t_e),
              fun a => e_abst var (inst <{ t_var ~ ω2 }> a) (snd t_e a))
    end.

End TypeReconstruction.

Module acc.

  Record Acc (w w' : World) : Type := mkAcc
    { iw : World
    ; pos : Alloc w iw
    ; neg : Tri iw w' }.

  Notation "w1 ⇅ w2" := (Acc w1 w2) (at level 80).
  Notation "w1 ↑ w2" := (Alloc w1 w2) (at level 80).
  Notation "w1 ↓ w2" := (Tri w1 w2) (at level 80).

  #[export] Instance refl_acc : Refl Acc :=
    fun w => {| iw := w; pos := refl; neg := refl |}.

  Fixpoint down_add {α w1 w2} (t : Tri w1 w2) {struct t} : Tri (w1 ▻ α) (w2 ▻ α) :=
    match t with
    | Tri.refl => refl
    | @Tri.cons _ _ x _ t r =>
      @Tri.cons _ _ x (ctx.in_succ _) (persist _ t _ step) (down_add r)
    end.

  Definition up_down_down_eq_up_down {w1 w2 w3} (r12 : w1 ⇅ w2) (down : w2 ↓ w3) : w1 ⇅ w3 :=
    match r12 with
    | {| iw := iw; pos := pos; neg := neg |} =>
          mkAcc _ _ _ pos (neg ⊙⁻ down)
    end.

  Definition up_down_up_eq_up_up_down {w1 w2 w3} (r12: w1 ⇅ w2) (up : w2 ↑ w3) : w1 ⇅ w3 :=
   match r12 with
   | {| iw := iw; pos := pos; neg := neg |} =>
        alloc.Alloc_rect
          (fun (w w' : World) (up : w ↑ w') => forall iw : World, w1 ↑ iw -> iw ↓ w -> w1 ⇅ w')
          (mkAcc _)
          (fun w α w' up IH iw pos neg =>
             IH (iw ▻ α) (pos ⊙ step) (down_add neg))
          w2 w3 up iw pos neg
   end.

  #[export] Instance trans_acc : Trans Acc :=
    fun w1 w2 w3 r12 r23 =>
      match r23 with
      | {| iw := iw; pos := pos; neg := neg |} =>
          up_down_down_eq_up_down (up_down_up_eq_up_up_down r12 pos) neg
      end.

  #[export] Instance preorder_acc : PreOrder Acc.
  Proof.
    constructor.
    - admit.
    - destruct r. cbn. now rewrite trans_refl_r.
    - admit.
  Admitted.

  Import (hints) Sub.

  Definition sub_acc {w1 w2 : World} (r : w1 ⇅ w2) : Sub w1 w2 :=
    match r with
    | {| pos := p; neg := n |} =>
        trans (R := Sub)
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
          persist w V w refl = V }.

  (* Class PersistLift A `{Persistent Acc A} : Type := *)
  (*   { lift_persist (w w': World) t r : *)
  (*     persist w (lift t _) w' r = lift t _ }. *)
  (* (* TODO: make lift generic (liftEnv is needed for Env) *) *)

End acc.

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

Lemma resolve_lift (g : env) (x : String.string) (w : World) :
  resolve x (liftEnv g w) =
    option.map (fun t => lift t w) (resolve x g).
Proof.
  induction g as [|[y t]]; cbn.
  - reflexivity.
  - now destruct String.string_dec.
Qed.

Lemma resolve_inst (w : World) (g : Env w) (x : String.string) (ι : Assignment w) :
  resolve x (inst g ι) =
    option.map (fun t => inst t ι) (resolve x g).
Proof.
  induction g as [|[y t]]; cbn.
  - reflexivity.
  - now destruct String.string_dec.
Qed.

Lemma inst_lift (w : World) (t : ty) (ι : Assignment w) :
  inst (lift t w) ι = t.
Proof. Admitted.

Lemma inst_lift_env (w : World) (G : env) (ι : Assignment w) :
  inst (liftEnv G w) ι = G.
Proof. Admitted.

Lemma inst_persist_env {R} {persR : Persistent R Env}
  {instR : forall w, Inst (R w) (Assignment w)}
  {w0 w1} (r1 : R w0 w1) (G0 : Env w0) (ι1 : Assignment w1) :
  inst <{ G0 ~ r1 }> ι1 = inst G0 (inst r1 ι1).
Proof. Admitted.

Lemma inst_persist_ty {R} {persR : Persistent R Ty}
  {instR : forall w, Inst (R w) (Assignment w)}
  {w0 w1} (r1 : R w0 w1) (t0 : Ty w0) (ι1 : Assignment w1) :
  inst <{ t0 ~ r1 }> ι1 = inst t0 (inst r1 ι1).
Proof. Admitted.

Lemma inst_step {R} {stepR : Step R} {instR : forall w, Inst (R w) (Assignment w)}
  {w x} (ι : Assignment (w ▻ x)) :
  inst (step (R := R)) ι = let (ι',_) := env.view ι in ι'.
Proof. Admitted.

Lemma inst_step_snoc {R} {stepR : Step R} {instR : forall w, Inst (R w) (Assignment w)}
  {w x} (ι : Assignment w) (t : ty) :
  inst (step (R := R)) (env.snoc ι x t) = ι.
Proof. rewrite inst_step. reflexivity. Qed.

Module StrongMonotonicity.

  Import option.notations.
  Import Unification.
  Import SigTNotations.
  Import (hints) Sub.

  #[local] Arguments Sub.thin : simpl never.
  #[local] Notation "□ˢ A" :=
    (Box Sub A)
      (at level 9, format "□ˢ A", right associativity)
      : indexed_scope.

  Definition M (A : TYPE) : TYPE :=
    Option (Diamond Sub A).

  Definition pure {A} : ⊢ A -> M A :=
    fun w a => Some (existT _ w (refl, a)).

  Definition bind {A B} : ⊢ M A -> □ˢ(A -> (M B)) -> M B :=
    fun w m f =>
      '(existT _ w1 (r1,a1)) <- m;;
      '(existT _ w2 (r2,b2)) <- f w1 r1 a1;;
      Some (existT _ w2 (r1 ⊙ r2, b2)).

  Definition mexists {A w n} (m : M A (w ▻ n)) : M A w :=
    '(w';(r,a)) <- m ;;
    Some (existT _ w' (step ⊙ r, a)).

  Definition mgu : ⊢ Ty -> Ty -> M Unit :=
    fun w t1 t2 =>
      '(w;(r,u)) <- Variant1.mgu t1 t2 ;;
      Some (w; (Sub.triangular r, u)).

  Definition WLP {A} : ⊢ M A -> □ˢ(A -> PROP) -> PROP :=
    fun w m P => option.wlp (fun '(w;(r,a)) => P w r a) m.

  Lemma wlp_pure {A w} (a : A w) (p : □ˢ(A -> PROP) w) :
    WLP w (pure w a) p <-> T p a.
  Proof. unfold WLP, pure. now rewrite option.wlp_match. Qed.

  Lemma wlp_bind {A B w} (m : M A w) (k : □ˢ(A -> M B) w) (p : □ˢ(B -> PROP) w) :
    WLP w (bind _ m k) p <->
      WLP w m (fun w1 r1 a1 => WLP w1 (k w1 r1 a1) (_4 p r1)).
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
    WLP (w ▻ n) m (_4 p step).
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
    WP w (pure w a) p <-> T p a.
  Proof.
    unfold WP, pure. now rewrite option.wp_match.
  Qed.

  Lemma wp_bind {A B w} (m : M A w) (k : □ˢ(A -> M B) w) (p : □ˢ(B -> PROP) w) :
    WP w (bind _ m k) p <->
      WP w m (fun w1 r1 a1 => WP w1 (k w1 r1 a1) (_4 p r1)).
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
    WP (w ▻ n) m (_4 p step).
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

  Definition RELATION (A : World -> Type) : Type :=
    forall w0 w1 (r1 : w0 ⊒ˢ w1),
      A w0 -> A w1 -> Prop.

  Definition RBox {A} (R : RELATION A) : RELATION □ˢA :=
    fun w0 w1 r01 ba0 ba1 =>
      forall (w2 w3 : World) (r02 : w0 ⊒ˢ w2) (r13 : w1 ⊒ˢ w3) (r23 : w2 ⊒ˢ w3),
        r01 ⊙ r13 = r02 ⊙ r23 ->
        R w2 w3 r23 (ba0 w2 r02) (ba1 w3 r13).

   (*         r01 *)
   (*    w0 -------> w1 *)
   (*     |          | *)
   (* r02 |          | r13 *)
   (*     |    //    | *)
   (*     ↓          ↓ *)
   (*    w2 -------> w3 *)
   (*         r23 *)

  Definition RDSub {A} (R : RELATION A) : RELATION (Diamond Sub A).
  Proof.
    intros w0 w1 r01.
    intros (w2 & r02 & a2).
    intros (w3 & r13 & a3).
    refine (exists r23,
               r01 ⊙ r13 = r02 ⊙ r23 /\ R _ _ r23 a2 a3).
  Defined.

  Definition RImpl {A B} (RA : RELATION A) (RB : RELATION B) : RELATION (Impl A B) :=
    fun w0 w1 r01 f0 f1 =>
      forall a0 a1,
        RA w0 w1 r01 a0 a1 ->
        RB w0 w1 r01 (f0 a0) (f1 a1).

  Definition ROption {A} (R : RELATION A) : RELATION (Option A) :=
    fun w0 w1 r01 m0 m1 =>
      match m0 , m1 with
      | Some a0 , Some a1 => R w0 w1 r01 a0 a1
      | Some _  , None    => True
      | None    , Some _  => False
      | None    , None    => True
      end.

  Definition RTy : RELATION Ty :=
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

  Definition REnv : RELATION Env.
  Admitted.

  Definition RM {A} (R : RELATION A) : RELATION (M A) :=
    ROption (RDSub R).

  Definition RValid {A} (R : RELATION A) (a : ⊢ A) : Prop :=
    forall w0 w1 r01,
      R w0 w1 r01 (a w0) (a w1).

  Definition RUnit : RELATION Unit :=
    fun _ _ _ _ _ => True.

  Lemma rsome {A} (R : RELATION A) w0 w1 (r01 : Sub w0 w1) (a0 : A w0) (a1 : A w1) (ra : R w0 w1 r01 a0 a1) :
    ROption R w0 w1 r01 (Some a0) (Some a1).
  Proof. apply ra. Qed.

  Lemma rpure {A} (R : RELATION A) :
    RValid (RImpl R (RM R)) pure.
  Proof.
    intros w0 w1 r01 a0 a1 ra.
    refine (@rsome _ (RDSub R) w0 w1 r01 _ _ _).
    unfold RDSub. exists r01. split; auto.
    now rewrite trans_refl_l, trans_refl_r.
  Qed.

  Lemma rbind {A B} (RA : RELATION A) (RB : RELATION B) :
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
        rewrite <- ?trans_assoc.
        rewrite Heqr.
        rewrite ?trans_assoc.
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
      specialize (H _ (r01 ⊙ Sub.triangular r13)).
      rewrite ?Sub.subst_comp in H.
      specialize (H H0).
      destruct H as (r23 & ?).
      exists r23. split; auto.
    - auto.
    - apply (H w3 (r01 ⊙ Sub.triangular r13)).
      destruct H0 as [H0 _].
      unfold RTy in *.
      subst. unfold P.unifies in *.
      now rewrite ?Sub.subst_comp, H0.
    - auto.
  Qed.

  Definition rexists {A} (R : RELATION A) w0 w1 (r01 : Sub w0 w1) {n} (m0 : M A (w0 ▻ n)) (m1 : M A (w1 ▻ n)) :
    RM R (w0 ▻ n) (w1 ▻ n) (Sub.up1 r01) m0 m1 ->
    RM R w0 w1 r01 (mexists m0) (mexists m1).
  Proof.
    unfold RM, ROption, mexists.
    destruct m0 as [(w2 & r02 & a2)|], m1 as [(w3 & r13 & a3)|]; cbn - [step Sub.up1]; auto.
    intros (r23 & Heqr & ra).
    exists r23. split; auto.
    rewrite trans_assoc, <- Heqr.
    clear.
    rewrite <- ?trans_assoc. f_equal.
    admit.
  Admitted.

  Arguments mexists : simpl never.

  Definition RPropImpl : RELATION PROP :=
    fun w0 w1 r01 p q => (q -> p)%type.

  Lemma wp_monotonic_strong {A} (R : RELATION A) :
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

End StrongMonotonicity.

(* Focus on the constraint generation only, forget about solving constraints
   and any semantic values. Also try to pass the type as an input instead of
   an output, i.e. checking instead of synthesizing. *)
Module ConstraintsOnly.

  Import option.notations.
  Import Unification.

  #[local] Set Implicit Arguments.
  #[local] Arguments step : simpl never.

  Module C.

    Inductive CStr (w : World) : Type :=
    | False
    | Eq (t1 t2 : Ty w)
    | And (C1 C2 : CStr w)
    | Ex {x} (C : CStr (w ▻ x)).
    #[global] Arguments False {w}.
    #[global] Arguments Ex [w] x C.

    Definition denote : ⊢ CStr -> Assignment -> PROP :=
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
      | v_true => tr == Ty_bool w
      | v_false => tr == Ty_bool w
      | e_if e1 e2 e3 =>
          check e1 G (Ty_bool w) /\
          check e2 G tr /\
          check e3 G tr
      | e_var s =>
          match resolve s G with
          | Some a => tr == a
          | None => C.False
          end
      | e_absu x e =>
          ∃1, ∃2,
            let G'  := <{ G ~ step ⊙ step }> in
            let tr' := <{ tr ~ step ⊙ step }> in
            let α1  := Ty_hole (w ▻ 1 ▻ 2) 1 (ctx.in_succ ctx.in_zero) in
            let α2  := Ty_hole (w ▻ 1 ▻ 2) 2 ctx.in_zero in
            (tr' == Ty_func _ α1 α2) /\
            check e ((x, α1) :: G') α2
      | e_abst x xt e =>
          ∃2,
            let G'  := <{ G ~ step }> in
            let tr' := <{ tr ~ step }> in
            let α1  := lift xt _ in
            let α2  := Ty_hole (w ▻ 2) 2 ctx.in_zero in
            (tr' == Ty_func _ α1 α2) /\
            check e ((x, α1) :: G') α2
      | e_app e1 e2 =>
          ∃0,
            let G'  := <{ G ~ step }> in
            let tr' := <{ tr ~ step }> in
            let α   := Ty_hole (w ▻ 0) 0 ctx.in_zero in
            check e1 G' (Ty_func _ α tr') /\
            check e2 G' α
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
    - destruct resolve eqn:?; cbn; intros Heq; [|contradiction].
      eexists. constructor. now rewrite resolve_inst, Heqo, Heq.
    - intros (t1 & t2 & H1 & H2).
      specialize (IHe _ _ _ _ H2). clear H2.
      destruct IHe as (e1' & HT). cbn in HT.
      rewrite ?inst_lift, ?inst_persist_env, ?inst_persist_ty, ?inst_trans, ?inst_step_snoc in *.
      rewrite H1. clear H1.
      eexists. constructor. eauto.
    - intros (t1 & H1 & H2).
      specialize (IHe _ _ _ _ H2). clear H2.
      destruct IHe as (e' & HT). cbn in HT.
      rewrite ?inst_lift, ?inst_persist_env, ?inst_persist_ty, ?inst_trans, ?inst_step_snoc in *.
      rewrite H1. clear H1.
      eexists. constructor. eauto.
    - intros (t1 & H1 & H2).
      specialize (IHe1 _ _ _ _ H1). clear H1. destruct IHe1 as (e1' & HT1).
      specialize (IHe2 _ _ _ _ H2). clear H2. destruct IHe2 as (e2' & HT2).
      exists (e_app e1' e2').
      cbn in HT1, HT2.
      rewrite ?inst_lift, ?inst_persist_env, ?inst_persist_ty, ?inst_trans, ?inst_step_snoc in *.
      econstructor; eauto.
  Qed.

  Lemma completeness_aux {G e t ee} (T : G |-- e; t ~> ee) :
    forall (w0 : World) (ι0 : Assignment w0) (G0 : Env w0) (t0 : Ty w0),
      G = inst G0 ι0 -> t = inst t0 ι0 -> C.denote (check e G0 t0) ι0.
  Proof.
    induction T; cbn; intros w0 ι0 G0 t0 ? ?; subst.
    - auto.
    - auto.
    - intuition.
    - rewrite resolve_inst in H.
      destruct resolve; [|discriminate].
      now injection H.
    - exists vt, t. rewrite H0. split.
      + now rewrite inst_persist_ty, inst_trans, !inst_step_snoc.
      + apply IHT; cbn; [|easy].
        now rewrite inst_persist_env, inst_trans, !inst_step_snoc.
    - exists t. split.
      + now rewrite inst_lift, inst_persist_ty, inst_step_snoc.
      + apply IHT; cbn; [|easy].
        now rewrite inst_lift, inst_persist_env, inst_step_snoc.
    - exists t2. split.
      + apply IHT1; cbn.
        * now rewrite inst_persist_env, inst_step_snoc.
        * now rewrite inst_persist_ty, inst_step_snoc.
      + apply IHT2; cbn; [|easy].
        now rewrite inst_persist_env, inst_step_snoc.
  Qed.

  Corollary completeness G e t ee (T : G |-- e ; t ~> ee) :
    C.denote (check e (liftEnv G _) (lift t _)) env.nil.
  Proof.
    eapply completeness_aux; eauto.
    - now rewrite inst_lift_env.
    - now rewrite inst_lift.
  Qed.

End ConstraintsOnly.

Module CandidateType.

  #[local] Set Implicit Arguments.
  #[local] Arguments step : simpl never.
  #[local] Arguments step : simpl never.

  Local Notation "[ ω ] x <- ma ;; mb" :=
    (bind (R := Alloc) ma (fun _ ω x => mb))
      (at level 80, x at next level,
        ma at next level, mb at level 200,
        right associativity).

  Local Notation "∃ n , m" :=
    (Bind_Exists_Free _ _ n m)
      (at level 80, right associativity, format "∃ n ,  m").

  Notation "t1 == t2 //\ m" := (Bind_AssertEq_Free _ _ t1 t2 m) (at level 70).

  Fixpoint check (e : expr) : ⊢ Env -> Ty -> FreeM Unit :=
    fun w G tr =>
      match e with
      | v_true => Bind_AssertEq_Free Unit w tr (Ty_bool w) (Ret_Free Unit w tt)
      | v_false => Bind_AssertEq_Free Unit w tr (Ty_bool w) (Ret_Free Unit w tt)
      | e_if e0 e1 e2 =>
        [r1] _ <- check e0 G (Ty_bool w)   ;;
        [r2] _ <- check e1 <{ G ~ r1 }> <{ tr ~ r1 }> ;;
        check e2 <{ G ~ r1 ⊙ r2 }> <{ tr ~ r1 ⊙ r2 }>
      | e_var s =>
        match resolve s G with
        | Some a => Bind_AssertEq_Free Unit w tr a (Ret_Free Unit w tt)
        | None => Fail_Free Unit w
        end
      | e_absu s e0 =>
        ∃1, ∃2,
          let tr' := <{ tr ~ step ⊙ step }> in
          let α1  := Ty_hole _ 1 (ctx.in_succ ctx.in_zero) in
          let α2  := Ty_hole _ 2 ctx.in_zero in
          tr' == Ty_func _ α1 α2 //\
          check e0 ((s, α1) :: <{ G ~ step ⊙ step }>) α2

      | e_abst s t e0 =>
        ∃2,
          let tr' := <{ tr ~ step }> in
          let α1  := lift t (w ▻ 2) in
          let α2  := Ty_hole (w ▻ 2) 2 ctx.in_zero in
          tr' == Ty_func (w ▻ 2) α1 α2 //\
          check e0 ((s, α1) :: <{ G ~ step }>) α2
      | e_app e0 e1 =>
        ∃0,
          let α := Ty_hole (w ▻ 0) 0 ctx.in_zero in
          [r1] _ <- check e0 <{ G ~ step }> (Ty_func _ α <{ tr ~ step }>) ;;
                    check e1 <{ G ~ step ⊙ r1 }> <{ α ~ r1 }>
  end.

  Lemma lookup_inst {w1 w2 : World} (r : Alloc w1 w2) (ι : Assignment w2) {x} (i : x ∈ w1) :
    env.lookup (inst r ι) i = env.lookup ι <{ i ~ r }>.
  Proof. induction r. reflexivity. cbn. rewrite <- IHr. now destruct env.view. Qed.

  Lemma completeness_aux {G e t ee} (T : G |-- e; t ~> ee) :
    forall (w0 : World) (ι0 : Assignment w0) (G0 : Env w0) (t0 : Ty w0),
      G = inst G0 ι0 -> t = inst t0 ι0 ->
      WP (check e G0 t0) (fun w1 r01 _ ι1 => ι0 = inst r01 ι1)%type ι0.
  Proof.
    Set Printing Depth 17.
    induction T; cbn; intros w0 ι0 G0 t0 ? ?; subst.
    + easy.
    + easy.
    + rewrite wp_bind. specialize (IHT1 w0 ι0 G0 (Ty_bool w0) eq_refl eq_refl).
      revert IHT1.
      apply wp_monotonic. intros w1 r1 _ ι1 Hι0.
      rewrite wp_bind.
      specialize (IHT2 w1 ι1 <{ G0 ~ r1 }> <{ t0 ~ r1}>).
      rewrite inst_persist_env in IHT2.
      rewrite inst_persist_ty in IHT2.
      rewrite Hι0 in IHT2.
      specialize (IHT2 eq_refl eq_refl).
      revert IHT2. apply wp_monotonic. intros w2 r2 _ ι2 Hι1.
      specialize (IHT3 w2 ι2 <{ G0 ~ r1 ⊙ r2 }> <{ t0 ~ r1 ⊙ r2 }>).
      rewrite inst_persist_env in IHT3.
      rewrite inst_persist_ty in IHT3.
      rewrite Hι0, Hι1, inst_trans in IHT3.
      specialize (IHT3 eq_refl eq_refl).
      revert IHT3. apply wp_monotonic. unfold _4.
      intros w3 r3 _ ι3 Hι2.
      now rewrite Hι0, Hι1, Hι2, !inst_trans.
    + rewrite resolve_inst in H. destruct resolve; cbn in *; now inversion H.
    + exists vt. exists t.
      rewrite inst_persist_ty.
      split; [easy|].
      specialize (IHT (w0 ▻ 1 ▻ 2)
                      (env.snoc (env.snoc ι0 1 vt) 2 t)
                      ((v, Ty_hole (w0 ▻ 1 ▻ 2) 1 (ctx.in_succ ctx.in_zero)) :: <{ G0 ~ step ⊙ step }>)
                      (Ty_hole (w0 ▻ 1 ▻ 2) 2 ctx.in_zero)).
      cbn in IHT. rewrite inst_persist_env in IHT. specialize (IHT eq_refl eq_refl).
      revert IHT. apply wp_monotonic. intros. hnf.
      now rewrite !inst_trans, <- H.
    + exists t.
      rewrite inst_persist_ty, inst_lift, H0.
      split; [easy|].
      specialize (IHT (w0 ▻ 2)
                      (env.snoc ι0 2 t)
                      ((v, lift vt (w0 ▻ 2)) :: <{ G0 ~ step }>)
                      (Ty_hole (w0 ▻ 2) 2 ctx.in_zero)).
      cbn in IHT.
      rewrite inst_lift in IHT.
      rewrite inst_persist_env in IHT.
      specialize (IHT eq_refl eq_refl).
      revert IHT. apply wp_monotonic. intros. hnf.
      now rewrite inst_trans, <- H.
    + exists t2.
      rewrite wp_bind.
      specialize (IHT1 (w0 ▻ 0)
                       (env.snoc ι0 0 t2)
                       <{ G0 ~ step }>
                       (Ty_func (w0 ▻ 0) (Ty_hole (w0 ▻ 0) 0 ctx.in_zero) <{ t0 ~ step }>)).
      cbn in IHT1.
      rewrite inst_persist_env in IHT1.
      rewrite inst_persist_ty in IHT1.
      specialize (IHT1 eq_refl eq_refl).
      revert IHT1. apply wp_monotonic. intros.
      specialize (IHT2 _ ι1 <{ G0 ~ step ⊙ r1 }> (Ty_hole w1 0 <{ ctx.in_zero ~ r1 }>)).
      cbn in IHT2.
      rewrite inst_persist_env in IHT2.
      rewrite inst_trans in IHT2.
      rewrite <- lookup_inst, <- H in IHT2.
      specialize (IHT2 eq_refl eq_refl).
      revert IHT2. apply wp_monotonic. intros. hnf.
      now rewrite !inst_trans, <- H0, <- H.
  Qed.

  Lemma soundness e :
    forall (w0 : World) (ι0 : Assignment w0) (G0 : Env w0) (t0 : Ty w0),
      WLP (check e G0 t0)
          (fun w1 r01 _ ι1 => ι0 = inst r01 ι1 /\
                       exists ee, inst G0 ι0 |-- e ; inst t0 ι0 ~> ee)
          ι0.
  Proof.
    induction e; cbn; intros.
    - split. auto. rewrite H. eexists. constructor.
    - split. auto. rewrite H. eexists. constructor.
    - rewrite wlp_bind. specialize (IHe1 _ ι0 G0 (Ty_bool w0)).
      revert IHe1. apply wlp_monotonic. intros.
      rewrite wlp_bind. specialize (IHe2 _ ι1 <{ G0 ~ r1 }> <{ t0 ~ r1}>).
      revert IHe2. apply wlp_monotonic. intros.
      specialize (IHe3 _ ι2 <{ G0 ~ r1 ⊙ r0 }> <{ t0 ~ r1 ⊙ r0 }>).
      revert IHe3. apply wlp_monotonic. intros.
      hnf. destruct H1, H0, H. subst.
      rewrite ?inst_persist_env,
              ?inst_persist_ty,
              ?inst_trans in *.
      split; [easy|].
      firstorder.
      exists (e_if x0 x1 x).
      now constructor.
    - destruct (resolve s G0) eqn:?; [|easy].
      intros Heqt. split; [easy|].
      exists (e_var s). constructor.
      rewrite resolve_inst, Heqo. cbn. congruence.
    - specialize (IHe _ (env.snoc (env.snoc ι0 1 t) 2 t1)
                        ((s, Ty_hole (w0 ▻ 1 ▻ 2) 1 (ctx.in_succ ctx.in_zero))
                             :: <{ G0 ~ step ⊙ step }>)
                        (Ty_hole (w0 ▻ 1 ▻ 2) 2 ctx.in_zero)).
      revert IHe. apply wlp_monotonic. unfold _4. cbn.
      intros ? ? _ ? (Hι1 & e' & IHe).
      rewrite
        ?inst_persist_env,
        ?inst_persist_ty,
        ?inst_trans, <- ?Hι1, ?inst_step_snoc in *.
      split; [easy|].
      exists (e_abst s t e').
      rewrite H.
      now constructor.
    - specialize (IHe _ (env.snoc ι0 2 t1)
                        ((s, lift t (w0 ▻ 2)) :: <{ G0 ~ step }>)
                        (Ty_hole (w0 ▻ 2) 2 ctx.in_zero)).
      revert IHe. apply wlp_monotonic. intros. hnf.
      destruct H0 as (Heq & e' & Ht). split. now rewrite inst_trans, <- Heq.
      exists (e_abst s t e'). cbn in *.
      Set Printing Depth 50.
      rewrite
        ?inst_persist_env,
        ?inst_persist_ty,
        ?inst_trans, ?inst_step_snoc in *.
      rewrite H, inst_lift in *.
      now constructor.
    - rewrite wlp_bind.
      specialize (IHe1 _ (env.snoc ι0 0 t)
                        <{ G0 ~ step }>
                        (Ty_func (w0 ▻ 0)
                           (Ty_hole (w0 ▻ 0) 0 ctx.in_zero)
                           <{ t0 ~ step }>)).
      revert IHe1. apply wlp_monotonic. intros.
      specialize (IHe2 _ ι1 <{ G0 ~ step ⊙ r1 }> (lk r1 ctx.in_zero)).
      revert IHe2. apply wlp_monotonic. intros. hnf.
      destruct H0 as (Hι1 & e2' & Hte2), H as (Hsnoc & e1' & Hte1).
      split. now rewrite ?inst_trans, <- Hι1, <- Hsnoc, inst_step.
      exists (e_app e1' e2').
      constructor 7 with t;
      rewrite
        ?inst_persist_env,
        ?inst_persist_ty,
        ?inst_trans, ?inst_step_snoc, ?inst_step, <- ?Hsnoc in *; cbn in *;
      rewrite ?lookup_inst, <- ?Hsnoc in *.
      + now rewrite inst_persist_ty in Hte1.
      + now rewrite <- lookup_inst, <- Hsnoc in Hte2.
  Qed.

End CandidateType.

Module ProofWorlds.

  #[local] Set Implicit Arguments.
  #[local] Arguments step : simpl never.

  Local Notation "[ ω ] x <- ma ;; mb" :=
    (bind (R := Alloc) ma (fun _ ω x => mb))
      (at level 80, x at next level,
        ma at next level, mb at level 200,
        right associativity).

  Local Notation "∃ n , m" :=
    (Bind_Exists_Free _ _ n m)
      (at level 80, right associativity, format "∃ n ,  m").

  Notation "t1 == t2 //\ m" := (Bind_AssertEq_Free _ _ t1 t2 m) (at level 70).

  Fixpoint check (e : expr) : ⊢ Env -> Ty -> FreeM Unit :=
    fun w G tr =>
      match e with
      | v_true => Bind_AssertEq_Free Unit w tr (Ty_bool w) (Ret_Free Unit w tt)
      | v_false => Bind_AssertEq_Free Unit w tr (Ty_bool w) (Ret_Free Unit w tt)
      | e_if e0 e1 e2 =>
        [r1] _ <- check e0 G (Ty_bool w)   ;;
        [r2] _ <- check e1 <{ G ~ r1 }> <{ tr ~ r1 }> ;;
        check e2 <{ G ~ r1 ⊙ r2 }> <{ tr ~ r1 ⊙ r2 }>
      | e_var s =>
        match resolve s G with
        | Some a => Bind_AssertEq_Free Unit w tr a (Ret_Free Unit w tt)
        | None => Fail_Free Unit w
        end
      | e_absu s e0 =>
        ∃1, ∃2,
          let tr' := <{ tr ~ step ⊙ step }> in
          let α1  := Ty_hole _ 1 (ctx.in_succ ctx.in_zero) in
          let α2  := Ty_hole _ 2 ctx.in_zero in
          tr' == Ty_func _ α1 α2 //\
          check e0 ((s, α1) :: <{ G ~ step ⊙ step }>) α2

      | e_abst s t e0 =>
        ∃2,
          let tr' := <{ tr ~ step }> in
          let α1  := lift t (w ▻ 2) in
          let α2  := Ty_hole (w ▻ 2) 2 ctx.in_zero in
          tr' == Ty_func (w ▻ 2) α1 α2 //\
          check e0 ((s, α1) :: <{ G ~ step }>) α2
      | e_app e0 e1 =>
        ∃0,
          let α := Ty_hole (w ▻ 0) 0 ctx.in_zero in
          [r1] _ <- check e0 <{ G ~ step }> (Ty_func _ α <{ tr ~ step }>) ;;
                    check e1 <{ G ~ step ⊙ r1 }> <{ α ~ r1 }>
  end.

  #[projections(primitive)]
  Record PWorld : Type :=
    { world :> World;
      assign : Assignment world
    }.

  Definition PTYPE : Type := PWorld -> Type.
  Definition PACC : Type := PWorld -> PTYPE.

  Bind    Scope indexed_scope with PTYPE.

  Definition PBox (R : PACC) (A : PTYPE) : PTYPE :=
    fun w0 => forall (w1 : PWorld), R w0 w1 -> A w1.

  Definition ACC2PACC (R : ACC)
    {instR : forall w, Inst (R w) (Assignment w)} : PACC :=
    fun w0 w1 => { r : R w0 w1 & inst r (assign w1) = assign w0 }.

  Definition PValid (A : PTYPE) : Type :=
    forall w, A w.
  Definition PImpl (A B : PTYPE) : PTYPE :=
    fun w => (A w -> B w)%type.

  Notation "⊩ A" := (PValid A) (at level 100).
  Notation "A ↣ B" := (PImpl A B)
    (at level 99, B at level 200, right associativity) :
      indexed_scope.

  #[local] Notation "□ᵖ A" :=
    (PBox (ACC2PACC Alloc) A)
      (at level 9, format "□ᵖ A", right associativity)
      : indexed_scope.

  Definition PT {A} : ⊩ □ᵖ A ↣ A.
  Proof.
    intros w a. apply a. hnf. exists refl. apply inst_refl.
  Defined.
  #[global] Arguments PT {A} [_] _ : simpl never.

  Definition P4 {A} : ⊩ □ᵖ A ↣ □ᵖ (□ᵖ A).
  Proof.
    intros [w0 ι0] a [w1 ι1] r1 [w2 ι2] r2; cbn in *.
    apply a.
    exists (projT1 r1 ⊙ projT1 r2). cbn.
    hnf in r1. hnf in r2. cbn in *.
    rewrite inst_trans.
    rewrite <- (projT2 r1).
    apply f_equal.
    apply (projT2 r2).
  Defined.
  #[global] Arguments P4 {A} [_] _ [_] _ [_] _ : simpl never.

  Definition pstep (w : PWorld) (x : nat) (t : ty) :
    ACC2PACC Alloc w {| world := w ▻ x; assign := env.snoc (assign w) x t |} :=
    existT
      (fun r => inst r (env.snoc (assign w) x t) = assign w)
      step (inst_step (env.snoc (assign w) x t)).

  Definition WP {A} : ⊩ FreeM A ↣ □ᵖ(A ↣ PROP) ↣ PROP :=
    fix WP w m POST {struct m} :=
    match m with
    | Ret_Free _ _ v => PT POST v
    | Fail_Free _ _ => False
    | Bind_AssertEq_Free _ _ t1 t2 k =>
        inst t1 (assign w) = inst t2 (assign w) /\ WP _ k POST
    | Bind_Exists_Free _ _ i k =>
        exists t : ty,
          WP {| world := w ▻ i; assign := env.snoc (assign w) i t |}
            k (P4 POST (pstep w i t))
    end.

  Lemma wp_monotonic {A : TYPE} {w : PWorld}
    (m : FreeM A w) (p q : □ᵖ(A ↣ PROP) w)
    (pq : forall w1 r1 a1, p w1 r1 a1 -> q w1 r1 a1) :
    WP m p -> WP m q.
  Proof.
    destruct w as [w ι]. cbn in m.
    induction m; cbn.
    - apply pq.
    - auto.
    - firstorder.
    - intros [x H]. exists x.
      revert H. apply IHm. intros *.
      apply pq.
  Qed.

  (* Lemma wp_bind {A B w} (m : FreeM A w) (f : □⁺(A -> FreeM B) w) : *)
  (*   forall (Q : □⁺(B -> Assignment -> PROP) w) (ι : Assignment w), *)
  (*     WP (bind m f) Q ι <-> *)
  (*     WP m (fun _ r a => WP (f _ r a) (_4 Q r)) ι. *)
  (* Proof. split; intros; induction m; cbn; firstorder; exists x; firstorder. Qed. *)

  (* Lemma lookup_inst {w1 w2 : World} (r : Alloc w1 w2) (ι : Assignment w2) {x} (i : x ∈ w1) : *)
  (*   env.lookup (inst r ι) i = env.lookup ι <{ i ~ r }>. *)
  (* Proof. induction r. reflexivity. cbn. rewrite <- IHr. now destruct env.view. Qed. *)

  Lemma completeness_aux {G e t ee} (T : G |-- e; t ~> ee) :
    forall (w0 : PWorld) (G0 : Env w0) (t0 : Ty w0),
      G = inst G0 (assign w0) -> t = inst t0 (assign w0) ->
      WP (check e G0 t0) (fun w1 r01 _ => True).
  Proof. Admitted.

  Definition WLP {A} : ⊩ FreeM A ↣ □ᵖ(A ↣ PROP) ↣ PROP :=
    fix WP w m POST {struct m} :=
    match m with
    | Ret_Free _ _ v => PT POST v
    | Fail_Free _ _ => True
    | Bind_AssertEq_Free _ _ t1 t2 k =>
        inst t1 (assign w) = inst t2 (assign w) -> WP _ k POST
    | Bind_Exists_Free _ _ i k =>
        forall t : ty,
          WP {| world := w ▻ i; assign := env.snoc (assign w) i t |}
            k (P4 POST (pstep w i t))
    end%type.

  Lemma soundness e :
    forall (w0 : PWorld) (G0 : Env w0) (t0 : Ty w0),
      WLP (check e G0 t0)
          (fun w1 r01 _ =>
             exists ee, inst G0 (assign w0) |-- e ; inst t0 (assign w0) ~> ee).
  Proof. Admitted.

End ProofWorlds.

  Lemma soundness e :
    forall (w0 : World) (ι0 : Assignment w0) (G0 : Env w0),
      WLP (reconstruct e G0)
          (fun w1 r01 '(t,ee) ι1 => ι0 = inst r01 ι1 /\
                                   inst G0 ι0 |-- e ; inst t ι1 ~> inst ee ι1)
          ι0.
  Proof. Set Printing Depth 17.
    induction e; cbn; intros.
    - repeat constructor.
    - repeat constructor.
    - rewrite wlp_bind. specialize (IHe1 _ ι0 G0).
      revert IHe1. apply wlp_monotonic. intros w1 r1 v1 ι1 Hv1.
      destruct v1 eqn:? in Hv1. destruct Hv1. intro.
      unfold T.
      rewrite wlp_bind. specialize (IHe2 _ ι1 <{ G0 ~ r1 ⊙ refl }>).
      revert IHe2. apply wlp_monotonic. intros w2 r2 v2 ι2 Hv2.
      destruct v2 eqn:? in Hv2. destruct Hv2.
      rewrite wlp_bind.
      specialize (IHe3 _ ι2 <{ G0 ~ r1 ⊙ refl ⊙ r2 }>).
      revert IHe3. apply wlp_monotonic. intros w3 r3 v3 ι3 Hv3.
      destruct v3 eqn:? in Hv3. destruct Hv3. intro.
      hnf.
      rewrite ?inst_persist_env,
              ?inst_persist_ty,
              ?inst_trans in *. cbn.
      split. now rewrite <- H4, <- H2, <- H.
      constructor 3.
      + rewrite Heqp. cbn.
        rewrite ?inst_trans. cbn.
        rewrite <- H4, <- H2.
        rewrite Heqp in H1. cbn in H1.
        rewrite H1 in H0. unfold inst, inst_lifted in H0.
        apply H0.
      + rewrite Heqp0. cbn. rewrite <- H4. rewrite inst_trans. cbn. rewrite <- H4. cbn in H3. rewrite <- H in H3. unfold inst, inst_lifted in H3. apply H3.
      + rewrite Heqp0, Heqp1. cbn. rewrite <- H4. cbn in H5. rewrite <- H2, <- H in H5. rewrite Heqp0, Heqp1 in H6. cbn in H6. rewrite <- H4 in H6. rewrite H6. apply H5.
    - destruct (resolve s G0) eqn:?; [|easy].
      cbn. unfold T. split. auto. constructor.
      rewrite resolve_inst, Heqo. cbn. congruence.
    - unfold T, _4.
      rewrite wlp_bind.
      specialize (IHe _ (env.snoc ι0 (ctx.length w0) t) ((s,
         Ty_hole (w0 ▻ ctx.length w0) (ctx.length w0)
           ctx.in_zero) :: <{ G0 ~ step ⊙ refl }>)).
      revert IHe. apply wlp_monotonic. intros w1 r1 v1 ι1 Hv1.
      destruct v1 eqn:? in Hv1. destruct Hv1. cbn.
      unfold T, _4.
      rewrite ?inst_persist_env,
              ?inst_persist_ty,
              ?inst_trans in *. cbn.
      rewrite <- H. split. auto.
      constructor.
      cbn in H0. rewrite <- CandidateType.lookup_inst. rewrite <- H. cbn.
      rewrite Heqp. cbn.
      rewrite ?inst_persist_env,
              ?inst_persist_ty,
              ?inst_trans in *. cbn in *.
      apply H0.
    - rewrite wlp_bind.
      specialize (IHe _ ι0 ((s, lift t w0) :: G0)).
      revert IHe. apply wlp_monotonic. intros w1 r1 v1 ι1 Hv1.
      destruct v1 eqn:? in Hv1. destruct Hv1. cbn.
      unfold T, _4.
      split. rewrite inst_trans. cbn. now rewrite <- H.
      rewrite Heqp. cbn.
      rewrite ?inst_persist_ty, ?inst_lift.
      constructor 6. cbn in H0.
      now rewrite ?inst_lift in H0.
    - unfold T, _4. rewrite wlp_bind.
      specialize (IHe2 _ (env.snoc ι0 (ctx.length w0) t) <{ G0 ~ step ⊙ refl }>).
      revert IHe2. apply wlp_monotonic. intros w1 r1 v1 ι1 Hv1.
      destruct v1 eqn:? in Hv1. destruct Hv1. cbn.
      rewrite wlp_bind.
      specialize (IHe1 _ ι1 <{ G0 ~ alloc.fresh w0 (ctx.length w0) w1 r1 }>).
      revert IHe1. apply wlp_monotonic. intros w2 r2 v2 ι2 Hv2.
      destruct v2 eqn:? in Hv2. destruct Hv2. cbn.
      intro.
      unfold T, _4.
      rewrite ?inst_persist_env,
              ?inst_persist_ty,
              ?inst_trans in *. cbn in *.
      rewrite Heqp, Heqp0, <- H1 in H3. cbn in H3.
      rewrite <- H1, <- H. cbn. split. auto.
      constructor 7 with (inst t0 ι1). rewrite <- H in H2. cbn in H2.
      rewrite <- CandidateType.lookup_inst in H3.
      rewrite <- H1 in H3.
      rewrite Heqp0. cbn.
      rewrite <- CandidateType.lookup_inst.
      rewrite ?inst_trans. cbn.
      rewrite <- H1, <- H. cbn.
      rewrite H3 in H2.
      rewrite <- CandidateType.lookup_inst in H2. rewrite <- H in H2. cbn in H2.
      apply H2.
      rewrite Heqp. cbn. rewrite ?inst_trans. cbn. rewrite <- H1.
      apply H0.
  Qed.

  Lemma completeness_aux {G e t ee} (T : G |-- e; t ~> ee) :
    forall (w0 : World) (ι0 : Assignment w0) (G0 : Env w0),
      G = inst G0 ι0 ->
      WP (reconstruct e G0) (fun w1 r01 '(t',ee) ι1 =>
                                             ι0 = inst r01 ι1 /\
                                             t = inst t' ι1) ι0.
  Proof.
    Set Printing Depth 17.
    induction T; cbn; intros w0 ι0 G0 ?; subst.
    + easy.
    + easy.
    + rewrite wp_bind. specialize (IHT1 w0 ι0 G0 eq_refl).
      revert IHT1. apply wp_monotonic. intros w1 r1 v1 ι1 Hv1.
      cbn. destruct v1 eqn:? in Hv1. destruct Hv1. split. now rewrite H0, Heqp.
      unfold T.
      rewrite wp_bind.
      specialize (IHT2 _ ι1 <{ G0 ~ r1 ⊙ refl }>).
      rewrite inst_persist_env in IHT2.
      rewrite inst_trans in IHT2.
      cbn in IHT2.
      rewrite <- H in IHT2.
      specialize (IHT2 eq_refl).
      revert IHT2. apply wp_monotonic. intros w2 r2 v2 ι2 Hv2.
      destruct v2 eqn:? in Hv2. destruct Hv2.
      rewrite wp_bind.
      specialize (IHT3 _ ι2 <{ G0 ~ r1 ⊙ refl ⊙ r2 }>).
      rewrite inst_persist_env in IHT3.
      rewrite inst_trans in IHT3.
      cbn in IHT3.
      rewrite <- H1, <- H in IHT3.
      specialize (IHT3 eq_refl).
      revert IHT3. apply wp_monotonic. intros w3 r3 v3 ι3 Hv3.
      destruct v3 eqn:? in Hv3. destruct Hv3. cbn.
      rewrite Heqp0, Heqp1. cbn.
      rewrite inst_persist_ty, <- H3.
      split. now rewrite <- H2, <- H4.
      unfold T. hnf.
      rewrite ?inst_persist_ty,
              ?inst_trans. cbn.
      now rewrite <- H3, <- H2, <- H1, <- H.
    + rewrite resolve_inst in H. destruct resolve; cbn in *; now inversion H.
    + exists vt.
      unfold Definitions.T, _4.
      rewrite wp_bind.
      specialize (IHT _ (env.snoc ι0 (ctx.length w0) vt)
                        ((v, Ty_hole (w0 ▻ ctx.length w0) (ctx.length w0) ctx.in_zero)
                           :: <{ G0 ~ step ⊙ refl }>)).
      cbn in IHT.
      rewrite inst_persist_env in IHT.
      cbn in IHT.
      specialize (IHT eq_refl).
      revert IHT. apply wp_monotonic. intros w1 r1 v1 ι1 Hv1. cbn.
      unfold Definitions.T, _4. cbn.
      destruct v1 eqn:? in Hv1. destruct Hv1.
      split.
      rewrite inst_trans. cbn. now rewrite <- H.
      rewrite Heqp. cbn.
      now rewrite <- H0, <- CandidateType.lookup_inst, <- H.
    + rewrite wp_bind.
      specialize (IHT _ ι0 ((v, lift vt w0) :: G0)).
      cbn in IHT.
      rewrite inst_lift in IHT.
      specialize (IHT eq_refl).
      revert IHT. apply wp_monotonic. intros w1 r1 v1 ι1 Hv1. cbn.
      unfold Definitions.T, _4. cbn.
      destruct v1 eqn:? in Hv1. destruct Hv1.
      split.
      rewrite inst_trans. cbn. now rewrite H.
      rewrite inst_persist_ty. rewrite inst_lift.
      now rewrite Heqp, H0.
    + exists t1.
      unfold Definitions.T, _4. cbn.
      rewrite wp_bind.
      specialize (IHT2 _ (env.snoc ι0 (ctx.length w0) t2) <{ G0 ~ alloc.fresh w0 (ctx.length w0) (w0 ▻ ctx.length w0) refl }>).
      cbn in IHT2.
      rewrite inst_persist_env in IHT2.
      cbn in IHT2.
      specialize (IHT2 eq_refl).
      revert IHT2. apply wp_monotonic. intros w1 r1 v1 ι1 Hv1. cbn.
      destruct v1 eqn:? in Hv1. destruct Hv1.
      rewrite wp_bind.
      specialize (IHT1 _ ι1 <{ G0 ~ alloc.fresh w0 (ctx.length w0) w1 r1 }>).
      rewrite inst_persist_env in IHT1. cbn in IHT1.
      Set Printing Depth 50.
      rewrite <- H in IHT1. cbn in IHT1.
      specialize (IHT1 eq_refl).
      revert IHT1. apply wp_monotonic. intros w2 r2 v2 ι2 Hv2. cbn.
      destruct v2 eqn:? in Hv2. destruct Hv2.
      split.
      - rewrite Heqp0. cbn.
        rewrite <- H2, inst_persist_ty, Heqp, <- H1. cbn.
        now rewrite <- H0,
                    -> assoc_persist,
                    <- CandidateType.lookup_inst,
                    -> inst_trans,
                    <- H1,
                    <- H.
      - unfold Definitions.T, _4. cbn.
        rewrite ?inst_trans. cbn.
        rewrite <- H1, <- H. cbn.
        rewrite <- ?CandidateType.lookup_inst,
                -> ?inst_trans. cbn.
        now rewrite <- H1, <- H.
  Qed.

From Coq Require Import
  Classes.Morphisms
  Classes.Morphisms_Prop
  Lists.List
  Strings.String.

From Equations Require Import
  Equations.

From iris Require
  bi.interface
  proofmode.tactics.
From Em Require Import
     Definitions Context Environment STLC Prelude Substitution Triangular
     Predicates
     LogicalRelation.
From Em Require
  Unification.

Import ctx.notations.
Import ListNotations.

#[local] Arguments step : simpl never.
#[local] Arguments reduce : simpl never.
#[local] Arguments thick : simpl never.

Lemma lk_step {Θ : ACC} {lkΘ : Lk Θ} {stepΘ : Step Θ} [w α] (αIn : α ∈ w) :
  lk step αIn = Ty_hole (w ▻ α) α (ctx.in_succ αIn).
Proof. Admitted.

Lemma lk_refl {Θ : ACC} {lkΘ : Lk Θ} {reflΘ : Step Θ} [w α] (αIn : α ∈ w) :
  lk refl αIn = Ty_hole w α αIn.
Proof. Admitted.

#[local] Notation "<{ A ~ w }>" := (persist _ A _ w) (only parsing).
#[local] Notation "s [ ζ ]" :=
  (persist _ s _ ζ)
    (at level 8, left associativity,
      format "s [ ζ ]").

#[export] Instance persistent_unit {R} : Persistent R Unit :=
  fun w1 u w2 r => u.
#[export] Instance persistent_prod {R A B} {pRA : Persistent R A} {pRB : Persistent R B} : Persistent R (Prod A B) :=
  fun w1 '(a,b) w2 r => (persist _ a _ r, persist _ b _ r).
#[export] Instance persistent_option {R A} {pRA : Persistent R A} : Persistent R (Option A) :=
  fun w1 oa w2 r => option.map (fun a => persist _ a _ r) oa.

Notation Expr := (Sem expr).
(* TODO: define reader applicative to use ctor of expr to create Expr *)

#[export] Instance persistpreorder_alloc_ty : PersistPreOrder Alloc Ty.
Proof.
Admitted.

#[export] Instance persistpreorder_alloc_env : PersistPreOrder Alloc Env.
Proof.
Admitted.

#[export] Instance persistpreorder_alloc_expr : PersistPreOrder Alloc Expr.
Proof.
Admitted.

Fixpoint grounding (w : World) : Assignment w :=
  match w with
  | ctx.nil      => env.nil
  | ctx.snoc Γ b => env.snoc (grounding Γ) b ty_bool
  end%ctx.

Open Scope indexed_scope.

Definition assert {w} t1 t2 :=
  Bind_AssertEq_Free Unit w t1 t2 (Ret_Free Unit w tt).

Definition exists_Ty : forall Σ, FreeM Ty Σ :=
  fun Σ => let i := ctx.length Σ in
           Bind_Exists_Free Ty Σ i (Ret_Free _ _ (Ty_hole _ i ctx.in_zero)).

Section Generate.
  Import MonadNotations.
  Import World.notations.

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
    | e_var x =>
        match (resolve x Γ) with
        | Some t_x => Ret_Free Ty _ t_x
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
  Import (hints) Tri.

  (* infer_schematic defines inference without grounding
     of remaining unification variables. *)
  Definition infer_schematic (e : expr) : option (Schematic Ty) :=
    match Unification.Variant1.solvefree (generate e nil) with
    | Some (w; (_, t)) => Some (w; t)
    | None             => None
    end.

  Definition infer_grounded (e : expr) : option ty :=
    option.map (fun '(w; t) => inst t (grounding w)) (infer_schematic e).

End RunTI.

Section TypeReconstruction.

  Definition ret  {w} := Ret_Free (Prod Ty Expr) w.
  Definition fail {w} := Fail_Free (Prod Ty Expr) w.

  Import MonadNotations.
  Import World.notations.

  Notation "f <$> a" := (@S.fmap _ _ f _ a) (at level 61, left associativity).
  Notation "f <*> a" := (@S.app _ _ _ f a) (at level 61, left associativity).

  Definition decode_ty : ⊢ʷ Ty -> Sem ty := fun w t => inst t.
  #[global] Arguments decode_ty [w] _.
  Definition decode_env : ⊢ʷ Env -> Sem env := fun w G => inst G.
  #[global] Arguments decode_env [w] _.

  Fixpoint reconstruct (e : expr) {Σ : World} (Γ : Env Σ) : FreeM (Prod Ty Expr) Σ :=
    match e with
    | v_true  => ret (Ty_bool Σ, S.pure v_true)
    | v_false => ret (Ty_bool Σ, S.pure v_false)
    | e_if cnd coq alt =>
        [ ω1 ] '(t1,e1') <- reconstruct cnd Γ ;;
        [ ω2 ] _     <- assert (Ty_bool _) t1 ;;
        [ ω3 ] r_coq <- reconstruct coq <{ Γ ~ ω1 ⊙ ω2 }> ;;
        [ ω4 ] r_alt <- reconstruct alt <{ Γ ~ ω1 ⊙ ω2 ⊙ ω3 }> ;;
        [ ω5 ] _     <- assert <{ (fst r_coq) ~ ω4 }> (fst r_alt) ;;
           let e_cnd := <{ e1' ~ ω2 ⊙ ω3 ⊙ ω4 ⊙ ω5 }> in
           let e_coq := <{ (snd r_coq) ~ ω4 ⊙ ω5 }> in
           let t_coq := <{ (fst r_coq) ~ ω4 ⊙ ω5 }> in
           let e_alt := <{ (snd r_alt) ~ ω5 }> in
           ret (t_coq, e_if <$> e_cnd <*> e_coq <*> e_alt)
    | e_var x =>
        match (resolve x Γ) with
        | Some t_x => ret (t_x, S.pure (e_var x))
        | None => fail
        end
    | e_absu x e1 =>
        [ ω1 ] t1        <- exists_Ty Σ ;;
        [ ω2 ] '(t2,e1') <- reconstruct e1 ((x, t1) :: Γ[ω1]) ;;
          ret (Ty_func _ t1[ω2] t2,
              e_abst x <$> decode_ty t1[ω2] <*> e1')
    | e_abst x t_x e =>
        let t_x' := lift t_x Σ in
        [ ω1 ] t_e <- reconstruct e ((x, t_x') :: Γ) ;;
          ret (Ty_func _ t_x'[ω1] (fst t_e),
              e_abst x t_x <$> snd t_e)
    | e_app e1 e2 =>
        [ θ1 ] '(tf, e1') <- reconstruct e1 Γ ;;
        [ θ2 ] '(t1, e2') <- reconstruct e2 (persist _ Γ _ θ1) ;;
        [ θ3 ] t2         <- @exists_Ty _ ;;
        [ θ4 ] _          <- assert tf[θ2⊙θ3] (Ty_func _ t1[θ3] t2) ;;
            ret (t2[θ4] , e_app <$> e1'[θ2⊙θ3⊙θ4] <*> e2'[θ3⊙θ4])
    end.

  Import SigTNotations.
  Import (hints) Tri.

  (* reconstruct_schematic defines type reconstruction without grounding
     of remaining unification variables. *)
  Definition reconstruct_schematic (e : expr) : option (Schematic (Prod Ty Expr)) :=
    match Unification.Variant1.solvefree (reconstruct e nil) with
    | Some (w; (_, te)) => Some (w; te)
    | None              => None
    end.

  Definition reconstruct_grounded (e : expr) : option (ty * expr) :=
    option.map
      (fun s : Schematic _ =>
         let (w, te) := s in
         inst te (grounding w))
      (reconstruct_schematic e).

End TypeReconstruction.

(*
Module acc.

  Import World.notations.
  Import (hints) Tri.

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
  Proof. destruct r; cbn; now rewrite Tri.persist_bool. Qed.

  Lemma persist_func {w1 w2} (r : Acc w1 w2) (t1 t2 : Ty _) :
    persist _ (Ty_func _ t1 t2) _ r =
    Ty_func _ (persist _ t1 _ r) (persist _ t2 _ r).
  Proof. destruct r; cbn; now rewrite Tri.persist_func. Qed.

  (* unify with PersistLaws about ↑ *)
  Class PersistLaws A `{Persistent Acc A} : Type :=
    { refl_persist w (V : A w) :
          persist w V w refl = V }.

  (* Class PersistSem A `{Persistent Acc A} : Type := *)
  (*   { sem_persist (w w': World) t r : *)
  (*     persist w (sem t _) w' r = sem t _ }. *)
  (* (* TODO: make sem generic (semEnv is needed for Env) *) *)

End acc.
*)

Section MoveMe.

  Context {Θ : ACC } {persΘ : Persistent Θ Ty}.
  Lemma persist_liftTy (w w' : World) t (θ : Θ w w') :
    persist w (lift t _) w' θ = lift t _.
  Proof.
    (* intros w w' t. revert w'. *)
    (* induction t; cbn; intros; now f_equal. *)
  Admitted.

  (* Lemma persist_split : forall w w' iw (pos : w ↑ iw) (neg : iw ↓ w') x, *)
  (*   persist w  x iw pos -> *)
  (*   persist iw x w' neg -> *)
  (*   persist w  x w' {| iw := iw; pos := pos; neg := neg |}. *)

  Lemma persist_liftEnv (w w' : World) e (θ : Θ w w') :
      persist w (liftEnv e _) w' θ = liftEnv e _.
  Proof.
    (* induction e. now cbn. *)
    (* destruct a. cbn. intro r. rewrite IHe. *)
    (* now rewrite persist_liftTy. *)
  Admitted.

End MoveMe.


Section WithPredicates.

  Import World.notations.
  Import Pred Pred.notations.
  Import (hints) Pred Pred.Acc Sub.

  Definition WP {A} : ⊢ʷ FreeM A -> □⁺(A -> Pred) -> Pred :=
    fix WP (w : World) (m : FreeM A w) (POST : □⁺(A -> Pred) w) {struct m} :=
      match m with
      | Ret_Free _ _ v => POST _ refl v
      | Fail_Free _ _ => ⊥ₚ
      | Bind_AssertEq_Free _ _ t1 t2 k => t1 =ₚ t2 /\ₚ WP w k POST
      | Bind_Exists_Free _ _ α k =>
          ∃ₚ t : Ty w,
           Ext (WP (w ▻ α) k (fun w1 r01 => _4 POST step r01)) (reduce (R := Sub) α t)
      end%P.

  Definition WLP {A} : ⊢ʷ FreeM A -> □⁺(A -> Pred) -> Pred :=
    fix WLP (w : World) (m : FreeM A w) (POST : □⁺(A -> Pred) w) {struct m} :=
      match m with
      | Ret_Free _ _ v => POST _ refl v
      | Fail_Free _ _ => ⊤ₚ
      | Bind_AssertEq_Free _ _ t1 t2 k => t1 =ₚ t2 ->ₚ WLP w k POST
      | Bind_Exists_Free _ _ α k =>
          (* ∀ₚ t : Ty w, *)
          (*   Ext (WLP (w ▻ α) k (fun w1 r01 => _4 POST step r01)) (reduce (R := Sub) α t) *)
          Acc.wlp step (WLP (w ▻ α) k (fun w1 r01 => _4 POST step r01))
      end%P.

  Lemma wp_bind {A B w1} (m : FreeM A w1) (f : □⁺(A -> FreeM B) w1) :
    forall (Q : □⁺(B -> Pred) w1),
      WP w1 (bind m f) Q ⊣⊢ₚ
      WP w1 m (fun w1 r01 a => WP w1 (f _ r01 a) (_4 Q r01)).
  Proof. split; intros; induction m; cbn; firstorder; exists x; firstorder. Qed.

  Lemma wlp_bind {A B w1} (m : FreeM A w1) (f : □⁺(A -> FreeM B) w1) :
    forall (Q : □⁺(B -> Pred) w1),
      WLP w1 (bind m f) Q ⊣⊢ₚ
      WLP w1 m (fun w1 r01 a => WLP w1 (f _ r01 a) (_4 Q r01)).
  Proof. (* split; intros; induction m; cbn; firstorder; exists x; firstorder. *) Admitted.

  Lemma wp_monotonic' {A w} (m : FreeM A w) (R : Pred w) (P Q : □⁺(A -> Pred) w) :
    (forall w1 (r : Alloc w w1) (a : A w1),
        Ext R r ⊢ₚ P w1 r a ->ₚ Q w1 r a) ->
    R ⊢ₚ WP w m P ->ₚ WP w m Q.
  Proof. Admitted.

  Lemma wlp_monotonic' {A w} (m : FreeM A w) (R : Pred w) (P Q : □⁺(A -> Pred) w) :
    (forall w1 (r : Alloc w w1) (a : A w1),
        Ext R r ⊢ₚ P w1 r a ->ₚ Q w1 r a) ->
    R ⊢ₚ WLP w m P ->ₚ WLP w m Q.
  Proof.
    intros pq. destruct m; cbn.
    - specialize (pq w refl a). rewrite ext_refl in pq. apply pq.
    - apply impl_and_adjoint. apply true_r.
    - admit.
    - apply impl_and_adjoint. admit.
  Admitted.

  Lemma wp_frame2 {A w} (m : FreeM A w) (P : □⁺(A -> Pred) w) (Q : Pred w) :
    WP w m P /\ₚ Q ⊣⊢ₚ WP w m (fun _ θ a => P _ θ a /\ₚ Ext Q θ)%P.
  Proof. Admitted.

  (* Lemma completeness e : forall (w0 : World) (G : Env w0) {t ee}, *)
  (*   (TPB G e t ee) *)
  (*   ⊢ₚ *)
  (*   WP w0 (reconstruct e G) *)
  (*       (fun w1 r01 '(t', ee') => (<{ ee ~ r01 }> =ₚ ee' /\ₚ <{ t ~ r01 }> =ₚ t')%P). *)
  (* Proof. *)
  (*   intros. revert w0 G e t ee. apply TPB_ind; cbn. *)
  (*   - intro w. *)
  (*     apply forall_r. intros _. *)
  (*     apply forall_r. intros t. *)
  (*     apply forall_r. intros ee ι. *)
  (*     unfold T. cbn. intros _ Ht Hee. *)
  (*     now rewrite inst_persist_ty, inst_refl. *)
  (*   - intro w. *)
  (*     apply forall_r. intros _. *)
  (*     apply forall_r. intros t. *)
  (*     apply forall_r. intros ee ι. *)
  (*     unfold T. cbn. intros _ Ht Hee. *)
  (*     now rewrite inst_persist_ty, inst_refl. *)
  (*   - intro w1. *)
  (*     do 9 (apply forall_r; intros ?). *)
  (*     do 7 (rewrite <- impl_and_adjoint). *)
  (*     assert (MASSAGE: forall w (A B C D E F G : Pred w), *)
  (* bientails (andₚ (andₚ (andₚ (andₚ (andₚ (andₚ A B) C) D) E) F) G) *)
  (*           (andₚ (andₚ (andₚ (andₚ (andₚ (andₚ A B) C) G) E) F) D)) by admit. *)
  (*     rewrite MASSAGE. clear MASSAGE. *)
  (*     rewrite wp_bind. apply impl_and_adjoint. apply wp_monotonic'. *)
  (*     intros w2 r12 [t1 ee1]. cbn -[step]. unfold Definitions.T, _4. *)
  (*     rewrite wp_bind. *)
  (*     rewrite <- impl_and_adjoint. *)
  (*     rewrite (eqₚ_sym t1). *)
  (*     assert (MASSAGE: forall w (A B C D : Pred w), *)
  (*                entails (andₚ A (andₚ B C)) (andₚ C D) <-> entails (andₚ A (andₚ B ⊤ₚ)) D) by admit. *)
  (*     rewrite (MASSAGE _ _ (eqₚ (persist w1 x4 w2 r12) ee1) (eqₚ (Ty_bool w2) t1) _). *)
  (*     rewrite and_true_r. *)
  (*     admit. *)
  (*   - intros w G s t e' ι. cbn. *)
  (*     intros _ Heqo Hvar. destruct (resolve s G) eqn:?; cbn; inversion Heqo. *)
  (*     unfold T. firstorder. now rewrite refl_persist. *)
  (*   - admit. *)
  (*   - admit. *)
  (*   - admit. *)
  (* Admitted. *)

  Lemma soundness' e : forall (w0 : World) (G : Env w0),
    Trueₚ
    ⊢ₚ
    WLP w0 (reconstruct e G)
        (fun w1 r01 '(t, ee) => TPB <{G ~ r01}> e t ee).
  Proof.
    (* induction e; cbn; intros; subst; unfold T. *)
    (* - constructor; constructor. *)
    (* - constructor; constructor. *)
    (* - rewrite wlp_bind. rewrite IHe1. *)
    (*   rewrite <- and_true_l. apply impl_and_adjoint. apply wlp_monotonic'. *)
    (*   intros. rewrite ext_true. *)
    (*   destruct a. rewrite <- impl_and_adjoint. *)
    (*   cbn. rewrite <- impl_and_adjoint. unfold T. rewrite wlp_bind. *)
    (*   specialize (IHe2 w1 <{ G ~ r ⊙ refl }>). rewrite IHe2. *)
    (*   (* probably doable with some kind of tactic, perhaps change or replace X with Y is easier? *) *)
    (*   assert (MASSAGE: forall w (X Y Z : Pred w), bientails (andₚ (andₚ X Y) Z) (andₚ (andₚ Y Z) X)). *)
    (*   { intros. now rewrite (and_assoc X _), (and_comm _ X). } *)
    (*   rewrite MASSAGE. clear MASSAGE. *)
    (*   apply impl_and_adjoint. apply wlp_monotonic'. *)
    (*   intros. destruct a. rewrite wlp_bind. *)
    (*   rewrite <- impl_and_adjoint. rewrite <- and_true_r. *)
    (*   rewrite IHe3. *)
    (*   apply impl_and_adjoint. apply wlp_monotonic'. *)
    (*   intros. destruct a. cbn. unfold T, _4. clear. *)
    (*   rewrite trans_refl_r, trans_refl_r. *)
    (*   constructor. *)
    (*   intro. unfold Ext. unfold andₚ, implₚ, TPB. intros. *)
    (*   destruct H as [[]]. *)
    (*   constructor. *)
    (*   + rewrite inst_persist_env, ?inst_trans. *)
    (*     rewrite inst_persist_env, H2 in H. cbn in H. *)
    (*     rewrite persist_trans. *)
    (*     exact H. *)
    (*   + rewrite inst_persist_env, inst_trans, inst_trans, inst_persist_ty. *)
    (*     rewrite inst_persist_env, inst_persist_env in H3. *)
    (*     apply H3. *)
    (*   + rewrite inst_persist_env, inst_trans, inst_trans. *)
    (*     rewrite inst_persist_env, inst_persist_env, inst_trans, <- H1 in H0. *)
    (*     apply H0. *)
    (* - destruct (resolve s G) eqn:?; cbn; try easy. *)
    (*   unfold T. rewrite refl_persist. constructor. constructor. *)
    (*   now rewrite resolve_inst, Heqo. *)
    (* - rewrite <- Acc.entails_wlp. rewrite ext_true. rewrite IHe. *)
    (*   rewrite <- and_true_l. *)
    (*   apply impl_and_adjoint. unfold T, _4. rewrite wlp_bind. *)
    (*   apply wlp_monotonic'. *)
    (*   intros. rewrite ext_true. *)
    (*   destruct a. cbn -[step]. unfold T, _4. *)
    (*   rewrite trans_refl_r, trans_refl_r. *)
    (*   constructor. intro. cbn -[step]. *)
    (*   unfold Ext, andₚ, implₚ, TPB. intros. cbn -[step] in *. *)
    (*   constructor. rewrite ?inst_persist_env in *. exact H0. *)
    (* - rewrite wlp_bind. specialize (IHe w0 ((s, lift t w0) :: G)). rewrite IHe. *)
    (*   rewrite <- and_true_l. *)
    (*   apply impl_and_adjoint. *)
    (*   apply wlp_monotonic'. *)
    (*   intros. rewrite ext_true. destruct a. rewrite <- impl_and_adjoint. *)
    (*   rewrite and_true_l. cbn in *. unfold T, _4. *)
    (*   constructor. intros ι He. cbn in *. rewrite ?inst_persist_env, ?inst_persist_ty, ?trans_refl_r, ?inst_lift in *. now constructor. *)
    (* - rewrite <- Acc.entails_wlp, ext_true, IHe2, <- and_true_l. *)
    (*   apply impl_and_adjoint. unfold T, _4. rewrite wlp_bind. apply wlp_monotonic'. *)
    (*   intros w1 r [t2 e2']. *)
    (*   rewrite ext_true, wlp_bind, <- impl_and_adjoint, and_comm, IHe1. *)
    (*   apply impl_and_adjoint. apply wlp_monotonic'. *)
    (*   intros w2 r12 [t1 e1']. cbn -[step]. unfold T, _4. *)
    (*   rewrite ?trans_refl_r. *)
    (*   constructor. *)
    (*   intros ι He2 He1 Ht1. *)
    (*   cbn -[step] in *. *)
    (*   rewrite ?inst_persist_ty, ?inst_persist_env, ?inst_trans, ?assoc_persist in *. *)
    (*   rewrite Ht1 in He1. econstructor. *)
    (*   exact He1. exact He2. *)
  Admitted.

  Import bi.interface.
  Import Pred.proofmode.
  #[local] Open Scope pred_scope.


  Lemma wlp_mono (A : TYPE) (w : World) (m : FreeM A w) (P Q : □⁺(A -> Pred) w) :
    (∀ (w1 : World) (r : Alloc w w1) (a : A w1), Acc.wlp r (P w1 r a → Q w1 r a)) ⊢
    (WLP w m P -∗ WLP w m Q).
  Proof. Admitted.

  Lemma wp_mono (A : TYPE) (w : World) (m : FreeM A w) (P Q : □⁺(A -> Pred) w) :
    (∀ (w1 : World) (r : Alloc w w1) (a : A w1), Acc.wlp r (P w1 r a → Q w1 r a)) ⊢
    (WP w m P -∗ WP w m Q).
  Proof. Admitted.


End WithPredicates.

Module ProgramLogic.

  Export Pred (* Pred.notations *).
  Export (hints) Pred.Acc.
  Export (hints) alloc.
  Export (hints) Sub.
  Export Pred.notations.

  Lemma ext_wp_step {w0 w1 : World} (x : nat) (P : Pred (w0 ▻ x)) (θ : Sub w0 w1) :
    Ext (Acc.wp (step (R := Alloc)) P) θ ⊣⊢ₚ
      Acc.wp (step (R := Alloc)) (Ext P (Sub.up1 θ)).
  Proof.
    rewrite !Acc.wp_step. constructor.
    intros ι; cbn - [thick Sub.up1].
    split; intros [t HP].
    - exists (persist _ t _ θ). admit.
    - exists (lift (inst t ι) _). admit.
  Admitted.

  Lemma step_reduce {Θ1 Θ2 T} `{Persistent Θ1 T, Persistent Θ2 T, Step Θ1, Reduce Θ2} {w α s} (t : T w) :
    persist _ (persist w t (w ▻ α) (step (R := Θ1))) _ (reduce (R := Θ2) α s) = t.
  Proof. Admitted.

  Lemma lift_reduce {Θ} `{Persistent Θ Ty, Reduce Θ} w α s t :
    (lift t (w ▻ α))[reduce (R := Θ) α s] = lift t w.
  Proof. Admitted.

  Lemma eqₚ_env_cons {w} b1 b2 (G1 G2 : Env w) :
    cons b1 G1 =ₚ cons b2 G2 ⊣⊢ₚ
    b1 =ₚ b2 /\ₚ G1 =ₚ G2.
  Proof.
    destruct b1, b2. constructor. intros ι. pred_unfold. cbn. split.
    - injection 1. intuition.
    - intros []. f_equal; auto.
  Qed.

  Lemma eq_func {w} (s1 s2 t1 t2 : Ty w) :
    Ty_func w s1 s2 =ₚ Ty_func w t1 t2 ⊣⊢ₚ (s1 =ₚ t1) /\ₚ (s2 =ₚ t2).
  Proof. now rewrite peq_ty_noconfusion. Qed.

  Import bi.interface.
  Import Pred.proofmode.
  #[local] Open Scope pred_scope.

  Definition ext_gen {w0} (P : Pred w0) {w1} (r01 : Sub w0 w1) (HP : ⊢ P) : ⊢ Ext P r01 :=
    {| fromEntails ι _ := fromEntails HP (inst r01 ι) (MkEmp (inst r01 ι)) |}.
  #[global] Arguments ext_gen {w0 P w1} r01 HP.

  Lemma ext_impl' (Θ : ACC) (instΘ : forall w, Inst (Θ w) (Assignment w)) {w0 w1}
    (θ01 : Θ w0 w1) (P Q : Pred w0) :
    Ext (P → Q) θ01 ⊣⊢ (Ext P θ01 → Ext Q θ01).
  Proof. apply ext_impl. Qed.

  Lemma equiv_true {w} : @Trueₚ w ⊣⊢ True.
  Proof. easy. Qed.

  Lemma equiv_sep {w} (P Q : Pred w) : (P ∗ Q) ⊣⊢ (P ∧ Q).
  Proof. constructor. firstorder. Qed.

  Lemma equiv_wand {w} (P Q : Pred w) : (P -∗ Q) ⊣⊢ (P → Q).
  Proof. constructor. firstorder. Qed.

  Lemma resolve_eq {w} {G1 G2 : Env w} x :
    G1 =ₚ G2 ⊢ₚ resolve x G1 =ₚ resolve x G2.
  Proof. constructor. intros ι ?. cbn. rewrite <- !resolve_inst. now f_equal. Qed.

  Lemma resolve_persist {R : ACC} `{Definitions.Persistent R Ty}
    {w0 w1} (r01 : R w0 w1) (G : Env w0) (x : string) :
    resolve x G[r01] = (resolve x G)[r01].
  Proof. induction G as [|[y]]; cbn; [|destruct string_dec]; easy. Qed.

  Lemma eqₚ_trans'
    {w} : ⊢ ∀ (s t u : Option Ty w), s =ₚ t → t =ₚ u → s =ₚ u.
  Proof.
    constructor. intros ι _ s t u st tu.
    exact (fromEntails (eqₚ_trans _ _ _) ι (conj st tu)).
  Qed.

  Lemma lk_reduce_zero {w x} (t : Ty w) :
    lk (reduce (R := Sub) x t) ctx.in_zero = t.
  Proof. reflexivity. Qed.

  Lemma lk_reduce_succ {w x y} (t : Ty w) (yIn : y ∈ w) :
    lk (reduce (R := Sub) x t) (ctx.in_succ yIn) = Ty_hole w y yIn.
  Proof. exact (env.lookup_tabulate (Ty_hole w) yIn). Qed.

  Lemma ext_wlp {R} {instR : forall w, Inst (R w) (Assignment w)}
    {w0 w1} {r01 : R w0 w1} P :
    Ext (Acc.wlp r01 P) r01 ⊢ₚ P.
  Proof. constructor. intros ι H. now apply H. Qed.

  Lemma lookup_inst {w1 w2 : World} (r : Alloc w1 w2) (ι : Assignment w2) {x} (i : x ∈ w1) :
    env.lookup (inst r ι) i = env.lookup ι i[r].
  Proof. induction r. reflexivity. cbn. rewrite <- IHr. now destruct env.view. Qed.

End ProgramLogic.

Ltac wsimpl :=
  repeat
    (rewrite ?persist_refl, ?persist_trans, ?persist_liftEnv, ?persist_liftTy,
      ?inst_lift, ?inst_reduce, ?inst_persist,
      ?inst_step_snoc, ?inst_lift_env, ?Sub.lk_trans, ?trans_refl_l, ?trans_refl_r,

      ?Pred.ext_refl, ?Pred.ext_tpb, ?Pred.ext_and, ?Pred.ext_eq,
      ?Pred.eqₚ_refl, ?Pred.impl_true_l, ?Pred.and_true_r, ?Pred.and_true_l,
      ?Pred.impl_true_r, ?Pred.impl_false_l, ?Pred.ext_impl, ?Pred.impl_and,
      ?Pred.ext_exists, ?Pred.ext_forall, ?Pred.Acc.wlp_true, ?Pred.eq_pair,

      ?Sub.persist_sim_step_alloc_env, ?Sub.persist_sim_step_alloc_ty, ?Sub.persist_sim_step_alloc_sem,

      ?ProgramLogic.eqₚ_env_cons, ?ProgramLogic.step_reduce,
      ?ProgramLogic.lift_reduce, ?ProgramLogic.eq_func,
      ?ProgramLogic.equiv_true, ?ProgramLogic.lk_reduce_zero,
      ?ProgramLogic.lk_reduce_succ;
     cbn - [lk trans step thin thick Sub.up1]; auto);
  repeat setoid_rewrite Pred.ext_exists;
  repeat setoid_rewrite Pred.ext_forall;
  repeat
    match goal with
    | |- context[@persist ?Θ ?A ?I ?w0 ?x ?w1 ?r01] =>
        is_var x; generalize (@persist Θ A I w0 x w1 r01); clear x; intros x;
        try (clear w0 r01)
    | |- context[fun w : Ctx nat => Ty w] =>
        change_no_check (fun w : Ctx nat => Ty w) with Ty
    | |- context[fun w : Ctx nat => Sem ?X w] =>
        change_no_check (fun w : Ctx nat => Sem X w) with (Sem X)
    end.

Section Modalities.

  Import Pred Pred.notations.
  Import (hints) Sub.
  Import ProgramLogic Pred.proofmode.
  Import iris.proofmode.tactics.
  Open Scope pred_scope.

  Section AccModality.

    Context {Θ : ACC} (instΘ : forall w, Inst (Θ w) (Assignment w)) [w0 w1] (θ : Θ w0 w1).

    Class IntoAcc (P : Pred w0) (Q : Pred w1) :=
      into_acc : P ⊢ Acc.wlp θ Q.

    #[export] Instance into_acc_default (P : Pred w0) : IntoAcc P (Ext P θ).
    Proof. constructor. cbn. intros ι0 HP ι1 <-. apply HP. Qed.

    Definition modality_wlp_mixin :
      modality_mixin (Acc.wlp θ)
        (MIEnvTransform IntoAcc)
        (MIEnvTransform IntoAcc).
    Proof. firstorder. Qed.

    Definition modality_wlp : modality bi_pred bi_pred :=
      Modality _ (modality_wlp_mixin).

    #[export] Instance from_modal_wlp P :
      FromModal True modality_wlp (Acc.wlp θ P) (Acc.wlp θ P) P.
    Proof. firstorder. Qed.

  End AccModality.

  #[global] Arguments IntoAcc {Θ _} [w0 w1] θ P Q.
  #[global] Arguments into_acc {Θ _} [w0 w1] θ P Q {_}.
  #[global] Hint Mode IntoAcc + + + + + - - : typeclass_instances.

  Section ExtReduceModality.

    Context {Θ : ACC} (instΘ : forall w, Inst (Θ w) (Assignment w)).
    Context [w : World] (α : nat) (t : Ty w).

    Class IntoExtReduce (P : Pred w) (Q : Pred (w ▻ α)) :=
      into_ext_reduce : P ⊢ Ext Q (reduce α t).

    #[export] Instance into_ext_reduce_default (P : Pred w) :
      IntoExtReduce P (Ext P (step (R := Sub))).
    Proof.
      constructor. cbn - [inst step]. intros ι HP.
      now rewrite inst_reduce inst_step_snoc.
    Qed.

    Definition modality_ext_reduce_mixin :
      modality_mixin (fun P => Ext P (reduce α t))
        (MIEnvTransform IntoExtReduce)
        (MIEnvTransform IntoExtReduce).
    Proof. firstorder. Qed.

    Definition modality_ext_reduce : modality bi_pred bi_pred :=
      Modality _ (modality_ext_reduce_mixin).

    #[export] Instance from_modal_ext_reduce P :
      FromModal True modality_ext_reduce
        (Ext P (reduce α t)) (Ext P (reduce α t))
        (persist w t (ctx.snoc w α) (step (R := Sub)) =ₚ Ty_hole (w ▻ α) α ctx.in_zero ->ₚ P).
    Proof.
      intros _. cbn. apply ext_reduce. constructor. pred_unfold.
      intros ι. cbn. destruct (env.view ι) as [ι t'].
      rewrite ?inst_persist ?inst_reduce inst_step_snoc. cbn.
      rewrite inst_step_snoc. intros HP ->. now apply HP.
    Qed.

  End ExtReduceModality.

End Modalities.

(* Focus on the constraint generation only, forget about solving constraints
   and any semantic values. Also try to pass the type as an input instead of
   an output, i.e. checking instead of synthesizing. *)
Module ConstraintsOnly.

  Import option.notations.
  Import Unification.

  #[local] Set Implicit Arguments.

  Module C.

    Import World.notations.
    Import Pred Pred.notations.
    Import (hints) Sub.

    Inductive CStr (w : World) : Type :=
    | False
    | Eq (t1 t2 : Ty w)
    | And (C1 C2 : CStr w)
    | Ex {x} (C : CStr (w ▻ x)).
    #[global] Arguments False {w}.
    #[global] Arguments Ex [w] x C.

    Definition denote : ⊢ʷ CStr -> Pred :=
      fix den {w} C {struct C} : Pred w :=
        match C with
        | False     => ⊥ₚ
        | Eq t1 t2  => t1 =ₚ t2
        | And C1 C2 => den C1 /\ₚ den C2
        | Ex x C    => ∃ₚ t : Ty w, Ext (den C) (reduce (R := Sub) x t)
        (* | Ex x C    => ∃ₚ t : ty, Ext (den C) (reduce (R := Sub) x (lift t _)) *)
        (* | Ex x C    => Acc.wlp (step (R := Sub)) (den C) *)
        end%P.

    Notation "C1 /\ C2" := (C.And C1 C2).
    Notation "t1 == t2" := (C.Eq t1 t2) (at level 80).
    Notation "∃ n , C" := (C.Ex n C) (at level 80, right associativity, format "∃ n ,  C").
  End C.
  Export C (CStr).

  Section Check.
    Import World.notations.
    Import C.

    Fixpoint check (e : expr) : ⊢ʷ Env -> Ty -> CStr :=
      fun (w : World) (G : Env w) (tr : Ty w) =>
        match e with
        | v_true => Ty_bool w == tr
        | v_false => Ty_bool w == tr
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
              let G'  := <{ G ~ step (R := Alloc) ⊙ step }> in
              let tr' := <{ tr ~ step (R := Alloc) ⊙ step }> in
              let α1  := Ty_hole (w ▻ 1 ▻ 2) 1 (ctx.in_succ ctx.in_zero) in
              let α2  := Ty_hole (w ▻ 1 ▻ 2) 2 ctx.in_zero in
              (Ty_func _ α1 α2 == tr') /\
              check e ((x, α1) :: G') α2
        | e_abst x xt e =>
            ∃2,
              let G'  := <{ G ~ step (R := Alloc) }> in
              let tr' := <{ tr ~ step (R := Alloc) }> in
              let α1  := lift xt _ in
              let α2  := Ty_hole (w ▻ 2) 2 ctx.in_zero in
              (Ty_func _ α1 α2 == tr') /\
              check e ((x, α1) :: G') α2
        | e_app e1 e2 =>
            ∃0,
              let G'  := <{ G ~ step (R := Alloc) }> in
              let tr' := <{ tr ~ step (R := Alloc) }> in
              let α   := Ty_hole (w ▻ 0) 0 ctx.in_zero in
              check e1 G' (Ty_func _ α tr') /\
              check e2 G' α
        end.

  End Check.

  Import iris.bi.interface.
  Import iris.proofmode.tactics.
  Import Pred Pred.notations Pred.proofmode.
  Import (hints) Sub.

  Lemma soundness e :
    forall (w : World) G t,
      C.denote (check e G t) ⊢ (∃ₚ ee : Expr w, G |--ₚ e; t ~> ee)%P.
  Proof.
    induction e; cbn; intros w G tr; wsimpl.
    - apply exists_r. exists (S.pure v_true).
      constructor. intros ι. cbn. intros <-. constructor.
    - apply exists_r. exists (S.pure v_false).
      constructor. intros ι. cbn. intros <-. constructor.
    - rewrite IHe1 IHe2 IHe3.
      iIntros "([%e1' H1] & [%e2' H2] & [%e3' H3])".
      iExists (fun ι => e_if (e1' ι) (e2' ι) (e3' ι)).
      iStopProof. constructor. intros ι (IH1 & IH2 & IH3). now constructor.
    - destruct resolve eqn:?; cbn.
      + apply exists_r. exists (S.pure (e_var s)).
        constructor. intros ι. cbn.
        constructor. now rewrite resolve_inst Heqo H.
      + apply false_l.
    - iIntros "(%t1 & %t2 & H)". wsimpl. rewrite IHe. wsimpl.
      iDestruct "H" as "[Heq [%e' H]]". wsimpl.
      iExists (fun ι => e_abst s (inst t1 ι) (inst e' ι)).
      iStopProof. constructor. intros ι (Heq & IH). cbn in *.
      rewrite <- Heq. now constructor.
    - iIntros "(%t2 & H)". wsimpl. rewrite IHe. wsimpl.
      iDestruct "H" as "[Heq [%e' H]]". wsimpl.
      iExists (fun ι => e_abst s t (inst e' ι)).
      iStopProof. constructor. intros ι (Heq & IH). cbn in *.
      rewrite inst_lift in Heq IH. rewrite <- Heq. now constructor.
    - iIntros "(%t2 & H)". wsimpl. rewrite IHe1 IHe2. wsimpl.
      iDestruct "H" as "([%e1' H1] & [%e2' H2])". wsimpl.
      iExists (fun ι => e_app (e1' ι) (e2' ι)).
      iStopProof. constructor. intros ι (H1 & H2). cbn in *.
      econstructor; eauto.
  Qed.

  Import iris.proofmode.tactics.
  Import ProgramLogic Pred.proofmode.
  Open Scope pred_scope.

  Lemma completeness_aux {G e t ee} (T : G |-- e; t ~> ee) :
    forall w0 (G0 : Env w0) (t0 : Ty w0),
      ⊢ liftEnv G _ =ₚ G0 → lift t _ =ₚ t0 → C.denote (check e G0 t0).
  Proof.
    induction T; intros w0 G0 t0; wsimpl.
    - iIntros "#HeqG #Heqt". repeat iSplit.
      + iApply IHT1; wsimpl.
      + iApply IHT2; wsimpl.
      + iApply IHT3; wsimpl.
    - constructor. intros ι. intros _ HeqG Heqt. cbn in *.
      rewrite inst_lift_env in HeqG.
      rewrite inst_lift in Heqt. subst.
      rewrite resolve_inst in H.
      destruct resolve.
      + injection H. easy.
      + discriminate H.
    - iIntros "#HeqG #Heqt".
      iExists (lift vt w0), (lift t _). wsimpl. iSplit; wsimpl.
      iIntros "!> #Heq1 !> #Heq2". iApply IHT; wsimpl.
    - iIntros "#HeqG #Heqt".
      iExists (lift t _). wsimpl. iSplit; wsimpl.
      iIntros "!> #Heq1". iApply IHT; wsimpl.
    - iIntros "#HeqG #Heqt".
      iExists (lift t2 _). iIntros "!> #Heq1".
      iSplit.
      + iApply IHT1; wsimpl.
      + iApply IHT2; wsimpl.
  Qed.

  Corollary completeness G e t ee (T : G |-- e ; t ~> ee) :
    C.denote (check e (liftEnv G _) (lift t _)) env.nil.
  Proof. eapply completeness_aux; now eauto. Qed.

End ConstraintsOnly.

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

Module Reconstruct.

  Import Pred Pred.notations.
  Import (hints) Sub.
  Import ProgramLogic Pred.proofmode.
  Import iris.proofmode.tactics.
  Open Scope pred_scope.

  Import Pred Pred.notations.
  Import World.notations.

  Lemma soundness e :
    forall (w : World) (G : Env w),
      ⊢ WLP w (reconstruct e G) (fun w1 r1 '(t,ee) =>
                                   G[r1] |--ₚ e; t ~> ee).
  Proof.
    induction e; cbn; intros w G; unfold T, _4; wsimpl.
    - constructor. intros ι _. pred_unfold. cbn. constructor.
    - constructor. intros ι _. pred_unfold. cbn. constructor.
    - rewrite wlp_bind. unfold _4. cbn.
      iPoseProof (IHe1 w G) as "-#IH1". iRevert "IH1". clear IHe1.
      iApply wlp_mono. iIntros (w1 r1 (t1 & e1')). cbn. iIntros "!> HT1 Heq1".

      rewrite wlp_bind. unfold _4. wsimpl.
      iPoseProof (IHe2 w1 G[r1]) as "-#IH2". iRevert "IH2". clear IHe2.
      iApply wlp_mono. iIntros (w2 r2 (t2 & e2')). cbn. iIntros "!> HT2".

      rewrite wlp_bind. unfold _4.
      iPoseProof (IHe3 w2 G[r1 ⊙ r2]) as "-#IH3". iRevert "IH3". clear IHe3.
      iApply wlp_mono. iIntros (w3 r3 (t3 & e3')). cbn. iIntros "!> HT3 Heq2".
      wsimpl.
      iStopProof. constructor. intros ι (HT1 & Heq1 & HT2 & HT3 & Heq2).
      pred_unfold. constructor; auto.

    - destruct resolve eqn:?; wsimpl.
      constructor. intros ι _; pred_unfold.
      constructor. now rewrite resolve_inst Heqo.
    - rewrite wlp_bind. unfold _4. cbn.
      iIntros "!>".
      iPoseProof (IHe (w ▻ ctx.length w)
                    ((s, Ty_hole (w ▻ ctx.length w) (ctx.length w) ctx.in_zero) :: G[step])) as "-#IH". iRevert "IH". clear IHe.
      iApply wlp_mono. iIntros (w1 r1 (t1 & e1')).
      iIntros "!> HT". wsimpl.
      iStopProof. constructor. intros ι HT1. pred_unfold. now constructor.
    - rewrite wlp_bind. unfold _4. cbn.
      iPoseProof (IHe w ((s, lift t w) :: G)) as "-#IH". iRevert "IH". clear IHe.
      iApply wlp_mono. iIntros (w1 r1 (t1 & e1')).
      iIntros "!> HT". wsimpl.
      iStopProof. constructor. intros ι HT1. pred_unfold.
      now constructor.
    - rewrite wlp_bind. unfold _4.
      iPoseProof (IHe1 w G)
        as "-#IH". iRevert "IH". clear IHe1.
      iApply wlp_mono. iIntros (w1 r1 (t12 & e1')) "!> HT1".
      rewrite wlp_bind. unfold _4.
      iPoseProof (IHe2 w1 G[r1]) as "-#IH". iRevert "IH". clear IHe2.
      iApply wlp_mono. iIntros (w2 r2 (t1 & e2')) "!> HT2". cbn. unfold _4. wsimpl. iIntros "!> Heq1".
      rewrite lk_refl.
      iStopProof. constructor. intros ι (HT1 & HT2 & Heq1). pred_unfold.
      econstructor; eauto.
  Qed.

  Lemma completeness_aux {G e t ee} (T : G |-- e; t ~> ee) :
    forall w0 (G0 : Env w0),
      ⊢ liftEnv G _ =ₚ G0 →
        WP _ (reconstruct e G0)
          (fun w1 r01 '(t',e') => lift t w1 =ₚ t' /\ₚ S.pure ee =ₚ e')%P.
  Proof.
    induction T; intros w0 G0; wsimpl; unfold _4, Definitions.T.
    - iIntros "#HeqG". rewrite wp_bind. unfold _4.
      iPoseProof (IHT1 w0 G0 with "HeqG") as "-#IH".
      clear IHT1. wsimpl.
      iRevert "IH". iApply wp_mono. iIntros (w1 r1 (t1 & e1')) "!> (#Heq1 & #Heq2)". wsimpl.
      iSplit. wsimpl.

      rewrite wp_bind. unfold _4.
      iPoseProof (IHT2 w1 G0[r1] with "HeqG") as "-#IH". clear IHT2.
      iRevert "IH". iApply wp_mono. iIntros (w2 r2 (t2 & e2')). wsimpl.
      iIntros "!> #Heq3 #Heq4". wsimpl.

      rewrite wp_bind. unfold _4.
      iPoseProof (IHT3 w2 G0 with "HeqG") as "-#IH". clear IHT3.
      iRevert "IH". iApply wp_mono. iIntros (w3 r3 (t3 & e3')). wsimpl.
      iIntros "!> #Heq5 #Heq6". wsimpl.
      repeat iSplit; auto.
      + admit.
      + admit.

    - constructor. intros ι. pred_unfold.
      rewrite inst_lift_env. intros _ ->.
      rewrite resolve_inst in H.
      destruct resolve.
      + injection H. clear H. intros <-.
        cbn. now pred_unfold.
      + discriminate H.
    - iIntros "#HeqG".
      iExists (lift vt _). iIntros "!> #Heq1".
      rewrite wp_bind. unfold _4. wsimpl.
      iPoseProof (IHT (w0 ▻ ctx.length w0) ((v, Ty_hole (w0 ▻ ctx.length w0) (ctx.length w0) ctx.in_zero) :: G0)) as "IHT".
      wsimpl.
      iPoseProof ("IHT" with "Heq1 HeqG") as "-#IHT'". iRevert "IHT'". iClear "IHT".
      iApply wp_mono. iIntros (w1 r1 (t1 & e1')) "!> (#Heq2 & #Heq3)". wsimpl.
      repeat iSplit; auto.
      admit.

    - admit.
    - admit.
  Admitted.

  Lemma wp_impl {A w} (m : FreeM A w) (P : □⁺(A -> Pred) w) (Q : Pred w) :
    (WP _ m P ->ₚ Q) ⊣⊢ₚ WLP _ m (fun w1 r01 a1 => P w1 r01 a1 ->ₚ Ext Q r01)%P.
  Proof.
    (* unfold Ext, bientails, implₚ. revert P Q. *)
    (* induction m; cbn; unfold T, _4, Basics.impl. *)
    (* - easy. *)
    (* - intros. intuition. *)
    (* - split; intuition. now apply IHm. *)
    (* - intros. specialize (IHm (_4 P step) (Ext Q step)). *)
    (*   cbn. split. *)
    (*   + intros HQ t. specialize (IHm (env.snoc ι _ t)). *)
    (*     apply IHm. intros Hwp. apply HQ. exists t. apply Hwp. *)
    (*   + intros Hwlp (t & Hwp). specialize (Hwlp t). *)
    (*     apply IHm in Hwlp; auto. *)
  Admitted.

  Theorem correctness e :
    forall w (G : Env w) Q (RQ : ProperPost Q),
      WP _ (reconstruct e G) Q ⊣⊢ₚ
      ∃ₚ t : Ty w, ∃ₚ ee : Expr w, TPB G e t ee /\ₚ T Q (t,ee).
  Proof.
    (* intros w G Q RQ ι. unfold T. split. *)
    (* - apply wp_impl. generalize (@soundness e w ι G). apply wlp_monotonic. *)
    (*   intros w1 r01 [t e'] ι1 (Heq & HT) HQ. subst. cbn. *)
    (*   exists (lift (inst t ι1) _). *)
    (*   exists (fun _ => inst e' ι1). cbn. *)
    (*   rewrite inst_lift. cbn. split. apply HT. unfold T. *)
    (*   change (Ext (T Q (lift (inst t ι1) w, fun _ : Assignment w => inst e' ι1)) r01 ι1). *)
    (*   specialize (RQ _ r01 (lift (inst t ι1) w, fun _ : Assignment w => inst e' ι1) (t, e') ι1). *)
    (*   unfold entails, implₚ in RQ. cbn in RQ. *)
    (*   rewrite inst_persist_ty, inst_lift in RQ. *)
    (*   specialize (RQ eq_refl). intuition. *)
    (* - intros (t & e' & HT & HQ). *)
    (*   generalize (@completeness_aux e w G ι (inst G ι) eq_refl (inst t ι) (inst e' ι) HT). *)
    (*   apply wp_monotonic. intros w1 r01 [t1 e1'] ι1 (Heq & Heqt). subst. *)
    (*   specialize (RQ _ r01 (t,e') (t1,e1') ι1). cbn in RQ. *)
    (*   rewrite inst_persist_ty, Heqt in RQ. *)
    (*   apply RQ; auto. f_equal. clear. *)
    (*   admit. *)
  Admitted.

End Reconstruct.

Module StrongMonotonicity.

  Import option.notations.
  Import Unification.
  Import SigTNotations.
  Import World.notations.
  Import (hints) Sub.

  #[local] Arguments Sub.thin : simpl never.
  #[local] Notation "□ˢ A" :=
    (Box Sub A)
      (at level 9, format "□ˢ A", right associativity)
      : indexed_scope.

  Definition M (A : TYPE) : TYPE :=
    Option (Diamond Sub A).

  Definition pure {A} : ⊢ʷ A -> M A :=
    fun w a => Some (existT w (refl, a)).

  Definition bind {A B} : ⊢ʷ M A -> □ˢ(A -> (M B)) -> M B :=
    fun w m f =>
      '(existT w1 (r1,a1)) <- m;;
      '(existT w2 (r2,b2)) <- f w1 r1 a1;;
      Some (existT w2 (r1 ⊙ r2, b2)).

  Definition mexists {A w n} (m : M A (w ▻ n)) : M A w :=
    '(w';(r,a)) <- m ;;
    Some (existT w' (step ⊙ r, a)).

  Definition mgu : ⊢ʷ Ty -> Ty -> M Unit :=
    fun w t1 t2 =>
      '(w;(r,u)) <- Variant1.mgu t1 t2 ;;
      Some (w; (Sub.triangular r, u)).

  Definition WLP {A} : ⊢ʷ M A -> □ˢ(A -> PROP) -> PROP :=
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

  Definition WP {A} : ⊢ʷ M A -> □ˢ(A -> PROP) -> PROP :=
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

  Import LR.

  (* Definition RDSub {Θ A} {transΘ : Trans Θ} (R : RELATION Θ A) : *)
  (*   RELATION Θ (Diamond Θ A) := *)
  (*   fun w0 w1 θ01 d1 d2 => *)
  (*     match d1 , d2 with *)
  (*     | (w2; (θ02,a2)) , (w3; (θ13,a3)) => *)
  (*         exists θ23, θ01 ⊙ θ13 = θ02 ⊙ θ23 /\ R _ _ θ23 a2 a3 *)
  (*     end. *)

  (* Definition ROption {Θ A} (R : RELATION Θ A) : RELATION Θ (Option A) := *)
  (*   fun w0 w1 r01 m0 m1 => *)
  (*     match m0 , m1 with *)
  (*     | Some a0 , Some a1 => R w0 w1 r01 a0 a1 *)
  (*     | Some _  , None    => True *)
  (*     | None    , Some _  => False *)
  (*     | None    , None    => True *)
  (*     end. *)

  (* Lemma rty_bool {Θ} {lkΘ : Lk Θ} {w0 w1} {θ01 : Θ w0 w1} : *)
  (*   RTy θ01 (Ty_bool _) (Ty_bool _). *)
  (* Proof. reflexivity. Qed. *)

  (* Lemma rty_func {Θ} {lkΘ : Lk Θ} {w0 w1} {θ01 : Θ w0 w1} t1_0 t1_1 t2_0 t2_1 : *)
  (*   RTy θ01 t1_0 t1_1 -> *)
  (*   RTy θ01 t2_0 t2_1 -> *)
  (*   RTy θ01 (Ty_func _ t1_0 t2_0) (Ty_func _ t1_1 t2_1). *)
  (* Proof. unfold RTy; cbn; intros; now f_equal. Qed. *)

  (* Definition REnv {Θ} : RELATION Θ Env. *)
  (* Admitted. *)

  (* Definition RM {A} (R : RELATION Sub A) : RELATION Sub (M A) := *)
  (*   ROption (RDSub R). *)

  (* Lemma rsome {Θ A} (R : RELATION Θ A) w0 w1 (θ01 : Θ w0 w1) (a0 : A w0) (a1 : A w1) (ra : R w0 w1 θ01 a0 a1) : *)
  (*   ROption R w0 w1 θ01 (Some a0) (Some a1). *)
  (* Proof. apply ra. Qed. *)

  (* Lemma rpure {A} (R : RELATION Sub A) : *)
  (*   RValid (RImpl R (RM R)) pure. *)
  (* Proof. *)
  (*   intros w0 w1 r01 a0 a1 ra. *)
  (*   refine (@rsome _ _ (RDSub R) w0 w1 r01 _ _ _). *)
  (*   unfold RDSub. exists r01. split; auto. *)
  (*   now rewrite trans_refl_l, trans_refl_r. *)
  (* Qed. *)

  (* Lemma rbind {A B} (RA : RELATION Sub A) (RB : RELATION Sub B) : *)
  (*   RValid (RImpl (RM RA) (RImpl (RBox (RImpl RA (RM RB))) (RM RB))) bind. *)
  (* Proof. *)
  (*   unfold RValid, RImpl, RBox, RM. *)
  (*   intros w0 w1 r01. *)
  (*   intros [(w2 & r2 & a2)|] [(w3 & r3 & a3)|] rm f0 f1 rf; cbn in rm. *)
  (*   - destruct rm as (r23 & Heqr & ra). *)
  (*     specialize (rf _ _ r2 r3 r23 Heqr _ _ ra). *)
  (*     cbn. revert rf. *)
  (*     destruct f0 as [(w4 & r4 & b4)|], f1 as [(w5 & r5 & b5)|]; cbn. *)
  (*     + intros (r45 & Heqr2 & rb). *)
  (*       exists r45. *)
  (*       rewrite <- ?trans_assoc. *)
  (*       rewrite Heqr. *)
  (*       rewrite ?trans_assoc. *)
  (*       now rewrite Heqr2. *)
  (*     + auto. *)
  (*     + auto. *)
  (*     + auto. *)
  (*   - cbn. destruct f0 as [(w4 & r4 & b4)|]; cbn. *)
  (*     + auto. *)
  (*     + auto. *)
  (*   - cbn. destruct f1 as [(w5 & r5 & b5)|]; cbn. *)
  (*     + auto. *)
  (*     + auto. *)
  (*   - cbn. *)
  (*     auto. *)
  (* Qed. *)

  (* Import SubstitutionPredicates. *)
  (* Lemma rmgu : *)
  (*   RValid (RImpl RTy (RImpl RTy (RM RUnit))) mgu. *)
  (* Proof. *)
  (*   unfold RValid, RImpl, RM, RUnit. *)
  (*   intros w0 w1 r01 t1_0 t1_1 rt1 t2_0 t2_1 rt2. *)
  (*   unfold mgu. *)
  (*   destruct (Correctness.mgu_spec t1_0 t2_0) as [(w2 & r02 & ?)|], *)
  (*       (Correctness.mgu_spec t1_1 t2_1) as [(w3 & r13 & ?)|]; cbn. *)
  (*   - unfold RTy in *. *)
  (*     clear u u0. *)
  (*     subst. *)
  (*     destruct H0 as [H0 _]. *)
  (*     destruct H as [_ H]. *)
  (*     unfold unifies in *. *)
  (*     specialize (H _ (r01 ⊙ Sub.triangular r13)). *)
  (*     rewrite ?persist_trans in H. *)
  (*     specialize (H H0). *)
  (*     destruct H as (r23 & ?). *)
  (*     exists r23. split; auto. *)
  (*   - auto. *)
  (*   - apply (H w3 (r01 ⊙ Sub.triangular r13)). *)
  (*     destruct H0 as [H0 _]. *)
  (*     unfold RTy in *. *)
  (*     subst. unfold unifies in *. *)
  (*     now rewrite ?persist_trans, H0. *)
  (*   - auto. *)
  (* Qed. *)

  (* Definition rexists {A} (R : RELATION Sub A) w0 w1 (r01 : Sub w0 w1) {n} (m0 : M A (w0 ▻ n)) (m1 : M A (w1 ▻ n)) : *)
  (*   RM R (w0 ▻ n) (w1 ▻ n) (Sub.up1 r01) m0 m1 -> *)
  (*   RM R w0 w1 r01 (mexists m0) (mexists m1). *)
  (* Proof. *)
  (*   unfold RM, ROption, mexists. *)
  (*   destruct m0 as [(w2 & r02 & a2)|], m1 as [(w3 & r13 & a3)|]; cbn - [step Sub.up1]; auto. *)
  (*   intros (r23 & Heqr & ra). *)
  (*   exists r23. split; auto. *)
  (*   rewrite trans_assoc, <- Heqr. *)
  (*   clear. *)
  (*   rewrite <- ?trans_assoc. f_equal. *)
  (*   admit. *)
  (* Admitted. *)

  (* Arguments mexists : simpl never. *)

  (* Definition RPropImpl {Θ} : RELATION Θ PROP := *)
  (*   fun w0 w1 r01 p q => (q -> p)%type. *)

  (* Lemma wp_monotonic_strong {A} (R : RELATION Sub A) : *)
  (*   RValid (RImpl (RM R) (RImpl (RBox (RImpl R RPropImpl)) RPropImpl)) WP. *)
  (* Proof. *)
  (*   intros w0 w1 r01 m0 m1 rm p0 p1 rp. *)
  (*   unfold RBox, RImpl, RPropImpl in *. *)
  (*   unfold RM, ROption, RDSub in rm. *)
  (*   destruct m0 as [(w2 & r02 & a2)|], m1 as [(w3 & r13 & a3)|]. *)
  (*   - unfold RM, ROption, RDSub in rm. *)
  (*     destruct rm as (r23 & Heqr & ra). *)
  (*     unfold WP. rewrite option.wp_match. *)
  (*     intros Hp1. constructor. revert Hp1. *)
  (*     eapply rp; eauto. *)
  (*   - inversion 1. *)
  (*   - destruct rm. *)
  (*   - inversion 1. *)
  (* Qed. *)

End StrongMonotonicity.

Module ProofWorlds.

  Import World.notations.

  #[local] Set Implicit Arguments.
  #[local] Arguments step : simpl never.

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
    @existT _
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

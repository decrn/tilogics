Require Import List.
Import ListNotations.
From Em Require Import
     Definitions Context Environment STLC.
Import ctx.notations.
From Em Require
  Unification.

Local Notation "<{ A ~ w }>" := (persist _ A _ w).

#[refine] Instance Persistent_Ty : Persistent Accessibility Ty :=
  fix F {Σ} (t : Ty Σ) {Σ'} (r : Accessibility Σ Σ') : Ty Σ' :=
    match t with
    | Ty_bool _ => Ty_bool Σ'
    | Ty_func _ t0 t1 => Ty_func Σ' (F t0 r) (F t1 r)
    | Ty_hole _ i i0 => Ty_hole Σ' i (transient Σ Σ' i r i0)
    end.
Defined.

#[refine] Instance Persistent_Env : Persistent Accessibility Env :=
  fix F {Σ} (l : list (String.string * Ty Σ)) {Σ'} (ω : Accessibility Σ Σ') :
           list (String.string * Ty Σ') :=
    match l with
    | []%list => []%list
    | (a0, b) :: l => (a0, <{ b ~ ω}>) :: F l ω
    end.
Defined.

Open Scope indexed_scope.

Fixpoint bind [A B] {Σ} (m : FreeM A Σ) (f : ◻ (A -> (FreeM B)) Σ)
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

Definition Unit (_ : World) := unit.

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

  (* infer_ng defines inference without grounding
     of remaining unification variables. *)
  Definition infer_ng (e : expr) : SolvedM Ty [] :=
    Unification.Variant1.solve_ng (@generate e ctx.nil []%list).

  Fixpoint ground (w: World) (ass : Assignment w)
                  (s: SolvedM Ty w) : option ty.
  Proof. destruct s.
    - (* value  *) apply Some. apply (Unification.applyassign t ass).
    - (* fail   *) apply None.
    - (* exists *) apply (ground (w ▻ i)).
      + constructor. apply ass. constructor 1. (* ground remaining to Bool *)
      + apply s.
  Defined.

  Definition runTI (e : expr) : option ty :=
    ground ctx.nil env.nil (infer_ng e).

End RunTI.

Section TypeReconstruction.

  Notation Expr := (Lifted expr).
  (* TODO: define reader applicative to use ctor of expr to create Expr *)

#[export] Instance Persistent_Lifted : forall A, Persistent Accessibility (Lifted A).
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
            fun a => e_abst var (Unification.applyassign <{ t_var ~ ω2 }> a) (snd t_e a))
  end.

End TypeReconstruction.

Definition PROP : TYPE :=
  fun _ => Prop.

Notation "⊢ A" := (Valid A) (at level 100).

Definition wp  {A} : ⊢ (SolvedM A) -> ◻(A -> PROP) -> PROP. Admitted.
Definition wlp {A} : ⊢ (SolvedM A) -> ◻(A -> PROP) -> PROP. Admitted.


Lemma soundness : forall e,
  wlp ctx.nil (infer_ng e)
    (fun w r t => forall (a : Assignment w),
       exists ee, nil |-- e ; (Unification.applyassign t a) ~> ee).
Admitted.

Lemma completeness : forall e t,
    (exists ee, nil |-- e ; t ~> ee) ->
      wp ctx.nil (infer_ng e)
        (fun w r s =>
           exists (a : Assignment w), t = (Unification.applyassign s a)).
Admitted.

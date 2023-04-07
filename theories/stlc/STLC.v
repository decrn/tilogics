From Coq Require Import
     Lists.List
     Relations.Relation_Definitions
     Relations.Relation_Operators
     Strings.String.
From Equations Require Import
     Equations.
From Em Require Import
     Definitions Context Environment Prelude.

#[local] Set Transparent Obligations.

Import ListNotations.
Import SigTNotations.
Import ctx.notations.

(* =================================== *)
(*  The Simply-Typed Lambda Calculus   *)
(*      extended with Booleans         *)
(* =================================== *)

(* ===== Types ===== *)

Inductive ty : Type :=
  | ty_bool : ty
  | ty_func : ty -> ty -> ty.

Inductive Ty (Σ : World) : Type :=
  | Ty_bool : Ty Σ
  | Ty_func : Ty Σ -> Ty Σ -> Ty Σ
  | Ty_hole : forall (i : nat), i ∈ Σ -> Ty Σ.

Section DecEquality.

  #[local] Set Implicit Arguments.

  Derive NoConfusion EqDec Subterm for ty.
  Derive NoConfusion Subterm for Ty.

  #[local] Set Equations With UIP.

  #[export] Instance In_eqdec {w} : EqDec (sigT (fun x : nat => ctx.In x w)).
  Proof.
    intros [x xIn] [y yIn].
    induction xIn; cbn; destruct (ctx.view yIn) as [|y yIn].
    - left. reflexivity.
    - right. abstract discriminate.
    - right. abstract discriminate.
    - destruct (IHxIn yIn); clear IHxIn; [left|right].
      + abstract (now dependent elimination e).
      + abstract (intros e; apply n; clear n;
                  now dependent elimination e).
  Defined.

  #[export] Instance Ty_eqdec {w} : EqDec (Ty w).
  Proof.
    change_no_check (forall x y : Ty w, dec_eq x y).
    induction x; destruct y; cbn; try (right; abstract discriminate).
    - left. auto.
    - apply f_equal2_dec; auto.
      now intros H%noConfusion_inv.
    - destruct (eq_dec (i; i0) (i1; i2)).
      + left. abstract now dependent elimination e.
      + right. abstract (intros H; apply n; clear n; inversion H; auto).
  Defined.

End DecEquality.

(* ===== Terms / Expressions ===== *)

Inductive expr : Type :=
  (* values *)
  | v_true  : expr
  | v_false : expr
  (* compound expressions *)
  | e_if    : expr -> expr -> expr -> expr
  | e_var   : string -> expr
  | e_absu  : string -> expr -> expr
  | e_abst  : string -> ty -> expr -> expr
  | e_app   : expr -> expr -> expr.

Derive NoConfusion for expr.

(* ===== Typing Context ===== *)

Definition env := list (string * ty).

Definition Env Σ := list (string * Ty Σ).

(* Context lookup *)
Fixpoint resolve {X} (var : string) (ctx : list (string * X)) : option X :=
  match ctx with
  | nil => None
  | (var', val) :: ctx' =>
      if (string_dec var var') then Some val else (resolve var ctx')
  end.

(* ===== Typing relation ===== *)

Reserved Notation "G |-- E ; T ~> EE"
            (at level 50).

Inductive tpb : env -> expr -> ty -> expr -> Prop :=
  | tpb_false : forall g,
      g |-- v_false ; ty_bool ~> v_false
  | tpb_true : forall g,
      g |-- v_true ; ty_bool ~> v_true
  | tpb_if : forall g cnd cnd' coq coq' alt alt' t,
      g |-- cnd ; ty_bool ~> cnd' ->
      g |-- coq ; t       ~> coq' ->
      g |-- alt ; t       ~> alt' ->
      g |-- (e_if cnd coq alt) ; t ~> (e_if cnd' coq' alt')
  | tpb_var : forall g v vt,
      resolve v g = Some vt ->
      g |-- (e_var v) ; vt ~> (e_var v)
  | tpb_absu : forall v vt g e e' t,
      ((v, vt) :: g) |-- e ; t ~> e' ->
      g |-- (e_absu v e) ; (ty_func vt t) ~> (e_abst v vt e')
  | tpb_abst : forall v vt g e e' t,
      ((v, vt) :: g) |-- e ; t ~> e' ->
      g |-- (e_abst v vt e) ; (ty_func vt t) ~> (e_abst v vt e')
  | tpb_app : forall g e1 t1 e1' e2 t2 e2',
      g |-- e1 ; (ty_func t2 t1) ~> e1' ->
      g |-- e2 ; t2 ~> e2' ->
      g |-- (e_app e1 e2) ; t1 ~> (e_app e1' e2')

  where "G |-- E ; T ~> EE" := (tpb G E T EE).

(* (λx . x) : Bool → Bool  ... is well-typed *)
Example id_bool_well_typed :
  nil |-- (e_absu "x" (e_var "x")) ; (ty_func ty_bool ty_bool) ~> (e_abst "x" ty_bool (e_var "x")).
Proof. repeat constructor. Qed.

Inductive freeM (A : Type) : Type :=
  | ret_free           : A -> freeM A
  | fail_free          : freeM A
  | bind_asserteq_free : ty -> ty -> freeM A -> freeM A
  | bind_exists_free   : (ty -> freeM A) -> freeM A.

Inductive FreeM (A : TYPE) (Σ : World) : Type :=
  | Ret_Free           : A Σ -> FreeM A Σ
  | Fail_Free          : FreeM A Σ
  | Bind_AssertEq_Free : Ty Σ -> Ty Σ -> FreeM A Σ -> FreeM A Σ
  | Bind_Exists_Free   : forall (i : nat), FreeM A (Σ ▻ i) -> FreeM A Σ.

Section Bind.
  Context {R} {reflR : Refl R} {transR : Trans R} {stepR : Step R}.

  #[export] Instance bind_freem  : Bind R FreeM :=
    fun A B =>
      fix bind {w} m f {struct m} :=
      match m with
      | Ret_Free _ _ v => T f v
      | Fail_Free _ _ => Fail_Free B w
      | Bind_AssertEq_Free _ _ t1 t2 C1 =>
          Bind_AssertEq_Free B w t1 t2 (bind C1 f)
      | Bind_Exists_Free _ _ i C =>
          Bind_Exists_Free B w i (bind C (_4 f step))
      end.
End Bind.

Inductive SolvedM (A : TYPE) (Σ : World) : Type :=
  | Ret_Solved           : A Σ -> SolvedM A Σ
  | Fail_Solved          : SolvedM A Σ
  | Bind_Exists_Solved   : forall (i : nat), SolvedM A (Σ ▻ i) -> SolvedM A Σ.

Inductive solvedM (A : Type) : Type :=
  | ret_solved           : A -> solvedM A
  | fail_solved          : solvedM A
  | bind_exists_solved   : (ty -> solvedM A) -> solvedM A.

Notation Assignment := (env.Env (fun _ => ty)).

Module S.
  Import World.notations.

  Definition Sem (A : Type) : TYPE :=
    fun w => Assignment w -> A.

  (* pure  :: a -> f a *)
  Definition pure {A} (a : A) : Valid (Sem A) := fun _ _ => a.
  #[global] Arguments pure {A} _ {w} _/.

  (* app :: f (a -> b) -> f a -> f b *)
  Definition app (A B : Type) : ⊢ (Sem (A -> B)) -> Sem A -> Sem B :=
    fun w fab fa ass => fab ass (fa ass).

  (* <*> : f a -> f b -> f (a * b) *)
  Definition spaceship (A B : Type) : ⊢ (Sem A) -> (Sem B) -> (Sem (A * B)) :=
    fun w fa fb ass => (fa ass, fb ass).

End S.
Export S (Sem).

Class Inst (A : TYPE) (a : Type) : Type :=
  inst : forall {w}, A w -> Assignment w -> a.

#[export] Instance inst_list {A : TYPE} {a : Type} `{Inst A a} :
  Inst (List A) (list a) :=
  fun w xs ass => List.map (fun x => inst x ass) xs.

#[export] Instance inst_const {A} :
  Inst (Const A) A | 10 :=
  fun Σ x ι => x.

#[export] Instance inst_unit :
  Inst Unit unit :=
  fun _ x ass => x.

#[export] Instance inst_prod {AT BT A B} `{Inst AT A, Inst BT B} :
  Inst (Prod AT BT) (A * B) :=
  fun ass '(a , b) ι => (inst a ι, inst b ι).

#[export] Instance inst_option {AT A} `{Inst AT A} :
  Inst (Option AT) (option A) :=
  fun w ma ass => option_map (fun a => inst a ass) ma.

#[export] Instance inst_ty : Inst Ty ty :=
  fix inst_ty {w} T ass :=
    match T with
    | Ty_bool _     => ty_bool
    | Ty_func _ σ τ => ty_func (inst_ty σ ass) (inst_ty τ ass)
    | Ty_hole _ _ i => env.lookup ass i
    end.

#[export] Instance inst_env :
  Inst Env env :=
  fix inst_env {w} E ass :=
  match E with
  | []           => []
  | (s,T) :: sTs => (s, inst T ass) :: inst_env sTs ass
  end%list.

#[export] Instance inst_sem {A} :
  Inst (Sem A) A :=
  fun w x ass => x ass.

Class Lk (R : ACC) : Type :=
  lk w1 w2 (r : R w1 w2) x (xIn : ctx.In x w1) : Ty w2.
#[global] Arguments lk {R _ w1 w2} r {x} xIn.

Class Thick (R : ACC) : Type :=
  thick w x {xIn : x ∈ w} (t : Ty (w - x)) : R w (w - x).
#[global] Arguments thick {R _ w} x {xIn} t.

#[export] Instance lk_alloc : Lk Alloc :=
  fun w1 w2 r x xIn => Ty_hole _ x (persist _ xIn _ r).

#[export] Instance persistent_sem {R} {instR : forall w, Inst (R w) (Assignment w)} {A} :
  Persistent R (Sem A) := fun w0 t w1 r01 ι1 => t (inst r01 ι1).

#[export] Instance Persistent_Ty {R} {lkR : Lk R} : Persistent R Ty :=
  fix per {w} (t : Ty w) {w'} (r : R w w') : Ty w' :=
    match t with
    | Ty_bool _ => Ty_bool w'
    | Ty_func _ t1 t2 => Ty_func w' (per t1 r) (per t2 r)
    | Ty_hole _ x xIn => lk r xIn
    end.

#[export] Instance PersistLaws_Ty : PersistLaws Ty.
Proof.
  constructor.
  - induction V; cbn; f_equal; auto.
  - induction V; cbn; f_equal; auto.
    unfold lk, lk_alloc. f_equal.
    apply assoc_persist.
Qed.

#[export] Instance Persistent_Env {R} {PTy : Persistent R Ty} :
  Persistent R Env :=
  fix per {w} (E : Env w) {w'} (r : R w w') : Env w' :=
    match E with
    | nil          => nil
    | cons (x,t) E => cons (x,persist w t w' r) (per E r)
    end.

#[export] Instance PersistLaws_Env : PersistLaws Env.
Proof.
  constructor.
  - induction V as [|[]]; cbn; f_equal; auto.
    f_equal. apply refl_persist.
  - induction V as [|[]]; cbn; f_equal; auto.
    f_equal. apply assoc_persist.
Qed.

#[export] Instance InstAlloc : forall w, Inst (Alloc w) (Assignment w) :=
  fix installoc {w0 w1} (r : Alloc w0 w1) :=
    match r with
    | alloc.refl _        => fun ι => ι
    | alloc.fresh _ α w r => fun ι => let (r',_) := env.view (inst (Inst := @installoc _) r ι) in r'
    end.

Class InstRefl (R : ACC) {reflR : Refl R} {instR : forall w, Inst (R w) (Assignment w)} : Prop :=
  inst_refl : forall [w] (ι : Assignment w), inst (refl (R := R)) ι = ι.
#[global] Arguments InstRefl R {_ _}.

#[export] Instance instrefl_alloc : InstRefl Alloc :=
  fun _ _ => eq_refl.

Lemma inst_trans {R} {transR : Trans R} {instR : forall w, Inst (R w) (Assignment w)}
  [w1 w2 w3] (r12 : R w1 w2) (r23 : R w2 w3) (ass : Assignment w3) :
  inst (trans r12 r23) ass = inst r12 (inst r23 ass).
Proof. Admitted.

Section WeakestPre.
  Import World.notations.

  Definition WLP {A} : ⊢ FreeM A -> □⁺(A -> Assignment -> PROP) -> Assignment -> PROP :=
    fix WLP w m POST ı {struct m} :=
      match m with
      | Ret_Free _ _ v => T POST v ı
      | Fail_Free _ _ => True
      | Bind_AssertEq_Free _ _ t1 t2 k =>
          (inst t1 ı = inst t2 ı) -> WLP _ k POST ı
      | Bind_Exists_Free _ _ i k =>
          forall t, WLP _ k (_4 POST step) (env.snoc ı i t)
      end%type.

  Definition WP {A} : ⊢ FreeM A -> □⁺(A -> Assignment -> PROP) -> Assignment -> PROP :=
    fix WP w m POST ı {struct m} :=
      match m with
      | Ret_Free _ _ v => T POST v ı
      | Fail_Free _ _ => False
      | Bind_AssertEq_Free _ _ t1 t2 k =>
          (inst t1 ı) = (inst t2 ı) /\ WP _ k POST ı
      | Bind_Exists_Free _ _ i k =>
          exists t, WP _ k (_4 POST step) (env.snoc ı i t)
      end.


  #[global] Arguments WP  {A} {w} _ _ _.
  #[global] Arguments WLP {A} {w} _ _ _.

  Open Scope indexed_scope.

  Lemma wlp_monotonic {A w} (m : FreeM A w) (p q : □⁺(A -> Assignment -> PROP) w)
    (pq : forall w1 r1 a1 ι1, p w1 r1 a1 ι1 -> q w1 r1 a1 ι1) :
    forall (ι : Assignment w), WLP m p ι -> WLP m q ι.
  Proof.
    induction m; cbn.
    - apply pq.
    - auto.
    - firstorder.
    - firstorder.
  Qed.

  Lemma wlp_bind {A B w} (m : FreeM A w) (f : □⁺(A -> FreeM B) w) :
    forall (Q : □⁺(B -> Assignment -> PROP) w) (ι : Assignment w),
      WLP (bind m f) Q ι <->
      WLP m (fun _ r a => WLP (f _ r a) (_4 Q r)) ι.
  Proof. split; intros; induction m; cbn; firstorder. Qed.

  Lemma wp_monotonic {A w} (m : FreeM A w) (p q : □⁺(A -> Assignment -> PROP) w)
    (pq : forall w1 r1 a1 ι1, p w1 r1 a1 ι1 -> q w1 r1 a1 ι1) :
    forall (ι : Assignment w), WP m p ι -> WP m q ι.
  Proof.
    induction m; cbn.
    - apply pq.
    - auto.
    - firstorder.
    - intros ι [x H]. exists x. firstorder.
  Qed.

  Lemma wp_bind {A B w} (m : FreeM A w) (f : □⁺(A -> FreeM B) w) :
    forall (Q : □⁺(B -> Assignment -> PROP) w) (ι : Assignment w),
      WP (bind m f) Q ι <->
      WP m (fun _ r a => WP (f _ r a) (_4 Q r)) ι.
  Proof. split; intros; induction m; cbn; firstorder; exists x; firstorder. Qed.

End WeakestPre.

Section Lift.
  Import World.notations.

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

  Lemma inst_lift (w : World) (t : ty) (ι : Assignment w) :
    inst (lift t w) ι = t.
  Proof. Admitted.

  Lemma inst_lift_env (w : World) (G : env) (ι : Assignment w) :
    inst (liftEnv G w) ι = G.
  Proof. Admitted.

End Lift.

Lemma inst_persist_env {R} {persR : Persistent R Env}
  {instR : forall w, Inst (R w) (Assignment w)}
  {w0 w1} (r1 : R w0 w1) (G0 : Env w0) (ι1 : Assignment w1) :
  inst (persist _ G0 _ r1) ι1 = inst G0 (inst r1 ι1).
Proof. Admitted.

Lemma inst_persist_ty {R} {persR : Persistent R Ty}
  {instR : forall w, Inst (R w) (Assignment w)}
  {w0 w1} (r1 : R w0 w1) (t0 : Ty w0) (ι1 : Assignment w1) :
  inst (persist _ t0 _ r1) ι1 = inst t0 (inst r1 ι1).
Proof. Admitted.

Lemma inst_step {R} {stepR : Step R} {instR : forall w, Inst (R w) (Assignment w)}
  {w x} (ι : Assignment (w ▻ x)) :
  inst (step (R := R)) ι = let (ι',_) := env.view ι in ι'.
Proof. Admitted.

Lemma inst_step_snoc {R} {stepR : Step R} {instR : forall w, Inst (R w) (Assignment w)}
  {w x} (ι : Assignment w) (t : ty) :
  inst (step (R := R)) (env.snoc ι x t) = ι.
Proof. rewrite inst_step. reflexivity. Qed.

Definition thickIn [w x] (xIn : x ∈ w) (s : Ty (w - x)) :
  forall y, y ∈ w -> Ty (w - x) :=
  fun y yIn =>
    match ctx.occurs_check_view xIn yIn with
    | ctx.Same _     => s
    | ctx.Diff _ yIn => Ty_hole (w - x) _ yIn
    end.
#[global] Arguments thickIn [w x] xIn s [y] yIn.

Class InstThick {R} `{forall w, Inst (R w) (Assignment w), Thick R} : Prop :=
  inst_thick :
    forall {w} {x} (xIn : x ∈ w) (t : Ty (w - x)) (ι : Assignment (w - x)),
      inst (thick (R := R) x t) ι = env.insert xIn ι (inst t ι).
#[global] Arguments InstThick R {_ _}.

Class LkPreOrder {R} `{Lk R, Persistent R Ty, Refl R, Trans R} : Prop :=
  { lk_refl {w x} (xIn : x ∈ w) :
      lk refl xIn = Ty_hole w x xIn;
    lk_trans {w1 w2 w3 x} (xIn : x ∈ w1) (ζ1 : R w1 w2) (ζ2 : R w2 w3) :
      lk (trans ζ1 ζ2) xIn = persist _ (lk ζ1 xIn) _ ζ2;
  }.
#[global] Arguments LkPreOrder R {_ _ _ _}.

Class PersistPreOrder {R A} `{Persistent R A, Refl R, Trans R} : Prop :=
  { persist_refl {w} (a : A w) :
      persist _ a _ refl = a;
    persist_trans {w1} (a : A w1) {w2 w3} (ζ1 : R w1 w2) (ζ2 : R w2 w3) :
      persist _ a _ (trans ζ1 ζ2) = persist _ (persist _ a _ ζ1) _ ζ2;
  }.
#[global] Arguments PersistPreOrder R A {_ _ _}.

Lemma Ty_no_cycle {w} (t : Ty w) : ~ Ty_subterm t t.
Proof.
  induction (well_founded_Ty_subterm t) as [? _ IH].
  intros Hx. apply (IH _ Hx Hx).
Qed.

Lemma ty_no_cycle (t : ty) : ~ ty_subterm t t.
Proof.
  induction (well_founded_ty_subterm t) as [? _ IH].
  intros Hx. apply (IH _ Hx Hx).
Qed.

Lemma inst_direct_subterm {w} (t1 t2 : Ty w) (ι : Assignment w) :
  Ty_direct_subterm t1 t2 -> ty_direct_subterm (inst t1 ι) (inst t2 ι).
Proof. intros []; constructor. Qed.

Lemma inst_subterm {w} (ι : Assignment w) (t1 t2 : Ty w) :
  Ty_subterm t1 t2 -> ty_subterm (inst t1 ι) (inst t2 ι).
Proof.
  induction 1.
  - constructor 1. now apply inst_direct_subterm.
  - eapply t_trans; eauto.
Qed.

Section Thin.

  Fixpoint thin {w x} (xIn : x ∈ w) (T : Ty (w - x)) : Ty w :=
    match T with
    | Ty_hole _ _ yIn => Ty_hole _ _ (ctx.in_thin xIn yIn)
    | Ty_bool _ => Ty_bool _
    | Ty_func _ T1 T2 => Ty_func _ (thin xIn T1) (thin xIn T2)
    end.

  (* Definition fancy_thin : ⊢ ◁Ty -> Ty := *)
  (*   fun w '(x; (xIn; T)) => thin xIn T. *)

End Thin.

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

Section ShallowConstraints.
  Import World.notations.

  Inductive TyF (w : World) : Type :=
  | TyF_bool       : TyF w
  | TyF_func {x y} : x ∈ w -> y ∈ w -> TyF w.
  #[global] Arguments TyF_bool {w}.
  #[global] Arguments TyF_func {w x y}.

  Definition inj : ⊢ TyF -> Ty :=
    fun w t =>
      match t with
      | TyF_bool     => Ty_bool _
      | TyF_func x y => Ty_func _ (Ty_hole _ _ x) (Ty_hole _ _ y)
      end.

  Variant ShallowConstraint (w : World) : Type :=
    | FlexFlex {x y} (xIn : x ∈ w) (yIn : y ∈ w)
    | FlexRigid {x} (xIn : x ∈ w) (t : TyF w).

End ShallowConstraints.

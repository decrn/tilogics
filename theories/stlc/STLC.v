From Coq Require Import
     Lists.List
     Relations.Relation_Definitions
     Strings.String.
From Equations Require Import
     Equations.
From Em Require Import
     Definitions Context Environment Prelude.

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

Derive NoConfusion for ty.
(* Print noConfusion_ty_obligation_1. *)
(* Print NoConfusion_ty. *)

Inductive Ty (Σ : World) : Type :=
  | Ty_bool : Ty Σ
  | Ty_func : Ty Σ -> Ty Σ -> Ty Σ
  | Ty_hole : forall (i : nat), i ∈ Σ -> Ty Σ.

Definition ty_eqb (a b : ty) : {a = b} + {a <> b}.
Proof. decide equality. Defined.

Section DecEquality.

  #[local] Set Implicit Arguments.
  #[local] Set Equations With UIP.

  Derive NoConfusion Subterm for Ty.

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

(* ===== Typing Context ===== *)

Definition env := list (string * ty).

Definition Env Σ := list (string * Ty Σ).

(* Context lookup *)
Fixpoint value {X} (var : string) (ctx : list (string * X)) : option X :=
  match ctx with
  | nil => None
  | (var', val) :: ctx' =>
      if (string_dec var var') then Some val else (value var ctx')
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
      value v g = Some vt ->
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

Fixpoint compose {w1 w2 : World} (r12 : Alloc w1 w2)
  : Assignment w2 -> Assignment w1 :=
  match r12 in (Alloc _ c0) return (Assignment c0 -> Assignment w1) with
  | alloc.refl _ => fun X0 : Assignment w1 => X0
  | alloc.fresh _ α Σ₂ a0 =>
      fun X0 : Assignment Σ₂ =>
        match env.view (compose a0 X0) with
        | env.isSnoc E _ => E
        end
  end.

Lemma compose_refl {w} (ass : Assignment w) :
    compose refl ass = ass.
Proof. easy. Qed.

Lemma compose_trans {w1 w2 w3} (r12 : Alloc w1 w2)
  (r23 : Alloc w2 w3) (ass : Assignment w3) :
  compose r12 (compose r23 ass) = compose (trans r12 r23) ass.
Proof. induction r12. auto. cbn. rewrite IHr12. reflexivity. Qed.

Definition Lifted (A : Type) : TYPE :=
  fun w => Assignment w -> A.

(* pure  :: a -> f a *)
Definition pure {A} (a : A) : Valid (Lifted A) := fun _ _ => a.

(* app :: f (a -> b) -> f a -> f b *)
Definition app (A B : Type) : ⊢ (Lifted (A -> B)) -> Lifted A -> Lifted B :=
  fun w fab fa ass => fab ass (fa ass).

(* <*> : f a -> f b -> f (a * b) *)
Definition spaceship (A B : Type) : ⊢ (Lifted A) -> (Lifted B) -> (Lifted (A * B)) :=
  fun w fa fb ass => (fa ass, fb ass).

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

#[export] Instance inst_ty :
  Inst Ty ty :=
  fix inst_ty {w} T ass :=
  match T with
  | Ty_bool _ =>
      ty_bool
  | Ty_func _ σ τ =>
      ty_func (inst_ty σ ass) (inst_ty τ ass)
  | Ty_hole _ _ i =>
      env.lookup ass i
  end.

#[export] Instance inst_env :
  Inst Env env :=
  fix inst_env {w} E ass :=
  match E with
  | []%list      => []%list
  | (s,T) :: sTs => (s, inst T ass) :: inst_env sTs ass
  end.

#[export] Instance Persistent_Ty : Persistent Alloc Ty :=
  fix per {w} (t : Ty w) {w'} (r : Alloc w w') : Ty w' :=
    match t with
    | Ty_bool _ => Ty_bool w'
    | Ty_func _ t1 t2 => Ty_func w' (per t1 r) (per t2 r)
    | Ty_hole _ i i0 => Ty_hole w' i (persist w i0 w' r)
    end.

#[export] Instance PersistLaws_Ty : PersistLaws Ty.
Proof.
  constructor.
  - induction V; cbn; f_equal; auto.
  - induction V; cbn; f_equal; auto.
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

Require Import List.
Import ListNotations.
Require Import String.
From Em Require Import
     Context.
Import ctx.notations.

(* =================================== *)
(*  The Simply-Typed Lambda Calculus   *)
(*      extended with Booleans         *)
(* =================================== *)

(* ===== Types ===== *)

  Inductive ty : Type :=
    | ty_bool : ty
    | ty_func : ty -> ty -> ty.

  Inductive Ty (Σ : Ctx nat) : Type :=
    | Ty_bool : Ty Σ
    | Ty_func : Ty Σ -> Ty Σ -> Ty Σ
    | Ty_hole : forall (i : nat), i ∈ Σ -> Ty Σ.

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

(* ===== Typing relation ===== *)

  Inductive freeM (A : Type) : Type :=
    | ret_free : A -> freeM A
    | fail_free : freeM A
    | bind_assert_free : ty -> ty -> freeM A -> freeM A
    | bind_exists_free : (ty -> freeM A) -> freeM A.

  (* Context/environment of term variables and their types *)
  Definition env := list (string * ty).

  Fixpoint value {X: Type} (var : string) (ctx : list (string * X)) : option X :=
    match ctx with
    | nil => None
    | (var', val) :: ctx' =>
        if (string_dec var var') then Some val else (value var ctx')
    end.

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

  (* (λx : Bool . x) : Bool → Bool  ... is well-typed *)
  Example typed_bool_id_func :
    nil |-- (e_abst "x" ty_bool (e_var "x")) ; (ty_func ty_bool ty_bool) ~> (e_abst "x" ty_bool (e_var "x")).
  Proof.
    apply tpb_abst. apply tpb_var. cbn. reflexivity.
  Qed.

  (* (λx . x) : Bool → Bool  ... is well-typed *)
  Example untyped_bool_id_func :
    nil |-- (e_absu "x" (e_var "x")) ; (ty_func ty_bool ty_bool) ~> (e_abst "x" ty_bool (e_var "x")).
  Proof.
    apply tpb_absu. apply tpb_var. cbn. reflexivity.
  Qed.

Section Symbolic.

  Definition Env Σ := list (string * Ty Σ).

  Inductive Cstr (A : Ctx nat -> Type) (Σ : Ctx nat) : Type :=
    | C_val : A Σ -> Cstr A Σ
    | C_fls : Cstr A Σ
    | C_eqc : Ty Σ -> Ty Σ -> Cstr A Σ -> Cstr A Σ
    | C_exi : forall (i : nat), Cstr A (Σ ▻ i) -> Cstr A Σ.

End Symbolic.

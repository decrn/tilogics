Require Import List.
Import ListNotations.
Require Import String.

Inductive ty : Type :=
  | ty_bool : ty
  | ty_func : ty -> ty -> ty.

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
  | tpb_absu : forall v vt g e e' t, (* don't we have to come up with vt ? *)
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

Example ex_typing1 :
  nil |-- (e_abst "x" ty_bool (e_var "x")) ; (ty_func ty_bool ty_bool) ~> (e_abst "x" ty_bool (e_var "x")).
Proof.
  apply tpb_abst. apply tpb_var. cbn. reflexivity.
Qed.

Example ex_typing2 :
  nil |-- (e_absu "x" (e_var "x")) ; (ty_func ty_bool ty_bool) ~> (e_abst "x" ty_bool (e_var "x")).
Proof.
  apply tpb_absu. apply tpb_var. cbn. reflexivity.
Qed.

Fixpoint gensem (ctx : list (string * ty)) (expression : expr) (type : ty) : Prop :=
  match expression with
  | v_true  => type = ty_bool
  | v_false => type = ty_bool
  | e_if cnd coq alt =>
      gensem ctx cnd ty_bool /\
      gensem ctx coq type    /\
      gensem ctx alt type
  | e_var var =>
      match (value var ctx) with
      | None => False
      | Some t => t = type
      end
  | e_app e1 e2 =>
      exists t2,
      gensem ctx e1 (ty_func t2 type) /\
      gensem ctx e2 t2
  | e_absu var e =>
      exists t_e t_var,
      gensem ((var, t_var) :: ctx) e t_e /\
      type = (ty_func t_var t_e)
  | e_abst var t_var e =>
      exists t_e,
      gensem ((var, t_var) :: ctx) e t_e /\
      type = (ty_func t_var t_e)
  end.

Lemma ex_gensem1 :
  gensem nil (e_app (e_absu "x" (e_var "x")) v_false) ty_bool.
Proof.
  compute. repeat eexists.
Qed.

Example ex_gensem2 :
gensem nil (e_app (e_absu "x" (v_true)) (e_absu "x" (e_var "x"))) ty_bool.
Proof.
  compute. repeat eexists.
  Unshelve. apply ty_bool.
Qed.



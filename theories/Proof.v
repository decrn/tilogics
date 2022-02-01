Require Import Coq.Classes.RelationClasses.
Require Import Setoid.
Require Import List.
Require Import String.

Inductive ty : Type :=
  | ty_nat
  | ty_bool.

Inductive expr : Type :=
  (* values *)
  | v_true  : expr
  | v_false : expr
  | v_O     : expr
  | v_S     : expr   -> expr
  (* compound expressions *)
  | e_if    : expr   -> expr -> expr -> expr
  | e_plus  : expr   -> expr -> expr
  | e_lte   : expr   -> expr -> expr
  | e_and   : expr   -> expr -> expr
  | e_let   : string -> expr -> ty   -> expr -> expr (* type annotated *)
  | e_var   : string -> expr.

Inductive cstr : Set := 
  | CAnd (c1 c2 : cstr)
  | CEq (n1 n2 : ty)
  | CFalse.

Definition ctx := list (string * ty).

Fixpoint value {X: Type} (var : string) (ctx : list (string * X)) : option X :=
  match ctx with
  | nil => None
  | (var', val) :: ctx' =>
      if (string_dec var var') then Some val else (value var ctx')
  end.

Fixpoint gen (gamma : ctx) (expression : expr) (type : ty) : cstr :=
  match expression with
  | v_true  => CEq type ty_bool
  | v_false => CEq type ty_bool
  | v_O     => CEq type ty_nat
  | v_S e   =>
      CAnd (CEq type ty_nat)
           (gen gamma e ty_nat)
  | e_if cnd coq alt =>
      CAnd (gen gamma cnd ty_bool)
           (CAnd (gen gamma coq type)
                 (gen gamma alt type))
  | e_plus lop rop =>
      CAnd (CEq type ty_nat)
           (CAnd (gen gamma lop ty_nat)
                 (gen gamma rop ty_nat))
  | e_lte e1 e2 =>
      CAnd (CEq type ty_bool)
           (CAnd (gen gamma e1 ty_nat)
                 (gen gamma e2 ty_nat))
  | e_and e1 e2 =>
      CAnd (CEq type ty_bool)
           (CAnd (gen gamma e1 ty_bool)
                 (gen gamma e2 ty_bool))
  | e_let var val t_val e =>
      CAnd (gen gamma val t_val)
           (gen ((var, t_val) :: gamma) e type)
  | e_var var =>
      match (value var gamma) with
      | None   => CFalse
      | Some t => CEq t type
      end
  end.

Fixpoint sem (c : cstr) : Prop :=
  match c with
  | CAnd c1 c2 => and (sem c1) (sem c2)
  | CEq t1 t2  => t1 = t2
  | CFalse => False
  end.

Fixpoint gensem (gamma : ctx) (expression : expr) (type : ty) : Prop :=
  match expression with
  | v_true  => type = ty_bool
  | v_false => type = ty_bool
  | v_O     => type = ty_nat
  | v_S v   => 
      type = ty_nat /\
      gensem gamma v ty_nat
  | e_if cnd coq alt =>
     gensem gamma cnd ty_bool /\
     gensem gamma coq type    /\
     gensem gamma alt type
  | e_plus lop rop =>
     type = ty_nat  /\
     gensem gamma lop ty_nat /\
     gensem gamma rop ty_nat
  | e_lte e1 e2 =>
     type = ty_bool /\
     gensem gamma e1 ty_nat  /\
     gensem gamma e2 ty_nat
  | e_and e1 e2 =>
     type = ty_bool /\
     gensem gamma e1 ty_bool /\
     gensem gamma e2 ty_bool
  | e_let var val t_val e =>
      gensem gamma val t_val /\
      gensem ((var, t_val) :: gamma) e type
  | e_var var =>
      match (value var gamma) with
      | None => False
      | Some t => t = type
      end
  end.

Theorem sem_o_gen_eq_gensem : forall (e : expr) (g : ctx) (t : ty),
  sem (gen g e t) <-> gensem g e t.
Proof.
  (* Shorter proof that uses rewrites. now is a tactical that tries a couple of
     simple things to finish a goal, among other things it's trying the
     reflexivity tactic which finishes the goals here. *)
  induction e; cbn; try reflexivity; intros.
  * (* e = S <e1> *)
    now rewrite IHe.
  * (* e = if <cnd> then <e1> else <e2> *)
    now rewrite IHe1, IHe2, IHe3.
  * (* e = plus <e1> <e2> *)
    now rewrite IHe1, IHe2.
  * (* e = lte <e1> <e2> *)
    now rewrite IHe1, IHe2.
  * (* e = and <e1> <e2> *)
    now rewrite IHe1, IHe2.
  * (* e = let <var> = <e1> : <Tau> in <e2> *)
    now rewrite IHe1, IHe2.
  * (* e = var <var> *)
    now destruct value.
Restart.
  (* Like the above but uses Ltac to figure out what the induction hypotheses
     are to rewrite. *)
  induction e; cbn; intros;
    repeat
      match goal with
      | IH : context[sem (gen _ ?e _)] |- context[gensem _ ?e _] =>
          rewrite IH
      end; try reflexivity.
  now destruct value.
Restart.
  (* The firstorder solver (slow) can handle the rewrites too. *)
  induction e; cbn; intros; try (firstorder; fail).
  destruct value; reflexivity.
Qed.


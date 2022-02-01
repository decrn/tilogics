(* Copied from Homework.v *)
Inductive e : Type :=
  | e_true
  | e_false
  | e_O
  | e_S (exp : e).

Inductive v : Type :=
  | v_e (exp: e)
  | v_if (cnd coq alt : v)
  | v_plus (lop rop : v)
  | v_lte (e1 e2 : v)
  | v_and (e1 e2 : v).

Inductive ty : Type :=
  | ty_nat
  | ty_bool.

Fixpoint ty_eqb (a b : ty) : bool :=
  match a, b with
  | ty_nat , ty_nat  => true
  | ty_bool, ty_bool => true
  | _      , _       => false
  end.

(* New stuff *)
Definition option_bind {A B} (m : option A) (f : A -> option B) : option B :=
  option_rect _ f None m.
Definition option_assert_eq (a b : ty) : option unit :=
  if ty_eqb a b then Some tt else None.

Notation "x <- ma ;; mb" :=
        (option_bind ma (fun x => mb))
          (at level 80, ma at next level, mb at level 200, right associativity).
Notation "' x <- ma ;; mb" :=
        (option_bind ma (fun x => mb))
          (at level 80, x pattern, ma at next level, mb at level 200, right associativity,
           format "' x  <-  ma  ;;  mb").
Notation "ma ;; mb" := (option_bind ma (fun _ => mb)) (at level 80, right associativity).
Notation "a ~~ b" := (option_assert_eq a b) (at level 80, no associativity).

Definition test_pattern {A B} (x : option (A * B)) : option (B * A) :=
  '(a,b) <- x ;;
  Some (b,a).

Fixpoint infer (v_exp : v) : option ty :=
  match v_exp with
  | v_e exp => match exp with
               | e_true => Some ty_bool
               | e_false => Some ty_bool
               | e_O => Some ty_nat
               | e_S _ => Some ty_nat
               end
  | v_if cnd coq alt =>
    t1 <- infer cnd ;;
    t2 <- infer coq ;;
    t3 <- infer alt ;;
    t1 ~~ ty_bool ;;
    t2 ~~ t3 ;;
    Some t2
  | v_plus lop rop =>
    t1 <- infer lop ;;
    t2 <- infer rop ;;
    t1 ~~ ty_nat ;;
    t2 ~~ ty_nat ;;
    Some ty_nat
  | v_lte e1 e2 =>
    t1 <- infer e1 ;;
    t2 <- infer e2 ;;
    t1 ~~ ty_nat ;;
    t2 ~~ ty_nat ;;
    Some ty_bool
  | v_and e1 e2 =>
    t1 <- infer e1 ;;
    t2 <- infer e2 ;;
    t1 ~~ ty_bool ;;
    t2 ~~ ty_bool ;;
    Some ty_bool
  end.

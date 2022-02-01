Require Import Setoid.
Require Import List.
Import ListNotations.
Require Import String.

Set Implicit Arguments.

Inductive ty : Type :=
  | ty_nat
  | ty_bool.

Fixpoint ty_eqb (a b : ty) : bool :=
  match a, b with
  | ty_nat , ty_nat  => true
  | ty_bool, ty_bool => true
  | _      , _       => false
  end.

Definition option_assert_eq (a b : ty) : option unit :=
  if ty_eqb a b then Some tt else None.

Notation "a ~~ b" := (option_assert_eq a b) (at level 80, no associativity).

Class TypeCheckM (M : Set -> Set) : Type :=
  {
    ret  (A   : Set) :   A -> M A ;
    bind (A B : Set) : M A -> (A -> M B) -> M B ;
    assert           :  ty -> ty         -> M unit ;
  }.

Inductive cstr : Set := 
  | CEq (n1 n2 : ty).

Definition writer (W A : Set) := prod W A.

Instance TC_writer : TypeCheckM (writer (list cstr)) :=
  { bind T1 T2 m f :=
      let (cs, x) := m in
      let (cs', y) := f x in
      (cs ++ cs', y) ;
    ret T u := (nil, u) ;
    assert t1 t2 := ([(CEq t1 t2)], tt) (* ( [t1 ~~ t2] , () ) *)
  }.


Instance TC_option : TypeCheckM option :=
  { bind T1 T2 m f :=
      match m with
      | None   => None
      | Some x => f x
      end ;
    ret T u := Some u;
    assert t1 t2 := option_assert_eq t1 t2;
  }.

Notation "x <- ma ;; mb" :=
        (bind ma (fun x => mb))
          (at level 80, ma at next level, mb at level 200, right associativity).
Notation "ma ;; mb" := (bind ma (fun _ => mb)) (at level 80, right associativity).



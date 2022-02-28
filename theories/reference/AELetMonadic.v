Require Import Setoid.
Require Import List.
Import ListNotations.
Require Import String.

Set Implicit Arguments.

Inductive ty : Type :=
  | ty_nat
  | ty_bool
  | ty_func : ty -> ty -> ty.

Inductive expr : Type :=
  (* values *)
  | v_true  : expr
  | v_false : expr
  | v_O     : expr
  | v_S     : expr -> expr
  (* compound expressions *)
  | e_if    : expr -> expr -> expr -> expr
  | e_plus  : expr -> expr -> expr
  | e_lte   : expr -> expr -> expr
  | e_and   : expr -> expr -> expr
  | e_let   : string -> expr -> expr -> expr
  | e_tlet  : string -> ty -> expr -> expr -> expr
  | e_var   : string -> expr
  | e_app   : expr -> expr -> expr.

Definition ty_eqb (a b : ty) : {a = b} + {a <> b}.
Proof. decide equality. Defined.

Fixpoint value {X: Type} (var : string) (ctx : list (string * X)) : option X :=
  match ctx with
  | nil => None
  | (var', val) :: ctx' =>
      if (string_dec var var') then Some val else (value var ctx')
  end.

Definition env := list (string * ty).

Class TypeCheckM (M : Type -> Type) : Type :=
  {
    ret  {A   : Type} :   A -> M A ;
    bind {A B : Type} : M A -> (A -> M B) -> M B ;
    assert            :  ty -> ty         -> M unit ;
    fail {A   : Type} : M A ;
    magic {A   : Type} : M A ;
    }.

Definition option_assert_eq (a b : ty) : option unit :=
  if ty_eqb a b then Some tt else None.

Notation "a ~~ b" := (option_assert_eq a b) (at level 80, no associativity).

Notation "x <- ma ;; mb" :=
        (bind ma (fun x => mb))
          (at level 80, ma at next level, mb at level 200, right associativity).
Notation "ma ;; mb" := (bind ma (fun _ => mb)) (at level 80, right associativity).
Notation "' x <- ma ;; mb" :=
        (bind ma (fun x => mb))
          (at level 80, x pattern, ma at next level, mb at level 200, right associativity,
           format "' x  <-  ma  ;;  mb").

Section new_infer.

Context {m} `{TypeCheckM m}.

Context (magic : m ty).

Fixpoint infer (ctx : env) (expression : expr) : m (prod ty expr) :=
  match expression with
  | v_false => ret (ty_bool, expression)
  | v_true  => ret (ty_bool, expression)
  | v_O     => ret (ty_nat, expression)
  | v_S e   =>
      '(t,e') <- infer ctx e ;;
      (assert t ty_nat) ;;
      ret (ty_nat, v_S e')
  | e_if cnd coq alt =>
      '(t_cnd, e_cnd) <- infer ctx cnd ;;
      '(t_coq, e_coq) <- infer ctx coq ;;
      '(t_alt, e_alt) <- infer ctx alt ;;
      (assert t_cnd ty_bool) ;;
      (assert t_coq t_alt)   ;;
      ret (t_coq, e_if e_cnd e_coq e_alt)
  | e_plus lop rop =>
      '(t_lop, e_lop) <- infer ctx lop ;;
      '(t_rop, e_rop) <- infer ctx rop ;;
      (assert t_lop ty_nat) ;;
      (assert t_rop ty_nat) ;;
      ret (ty_nat, e_plus e_lop e_rop)
  | e_lte lop rop =>
      '(t_lop, e_lop) <- infer ctx lop ;;
      '(t_rop, e_rop) <- infer ctx rop ;;
      (assert t_lop ty_nat) ;;
      (assert t_rop ty_nat) ;;
      ret (ty_bool, e_lte e_lop e_rop)
  | e_and lop rop =>
      '(t_lop, e_lop) <- infer ctx lop ;;
      '(t_rop, e_rop) <- infer ctx rop ;;
      (assert t_lop ty_bool) ;;
      (assert t_rop ty_bool) ;;
      ret (ty_bool, e_and e_lop e_rop)
  | e_let var val bod =>
      '(t_val, e_val) <- infer ctx val ;;
      '(t_bod, e_bod) <- infer ((var, t_val) :: ctx) bod ;;
      ret (t_bod, e_tlet var t_val e_val e_bod)
  | e_tlet var et_val val bod =>
      '(at_val, e_val) <- infer ctx val ;;
      (assert at_val et_val) ;; (* expected/annotated type matches actual type *)
      '(t_bod, e_bod) <- infer ((var, at_val) :: ctx) bod ;;
      ret (t_bod, e_tlet var at_val e_val e_bod)
  | e_var var =>
      match (value var ctx) with
      | Some t_var => ret (t_var, expression)
      | None => fail
      end
  | e_app e1 e2 =>
      '(t_e1, e_e1) <- infer ctx e1 ;;
      '(t_e2, e_e2) <- infer ctx e2 ;;
      t_magic <- magic ;;
      (assert t_e1 (ty_func t_e2 t_magic)) ;;
      ret (t_magic, e_app e_e1 e_e2)
      (* | e_app e1 e2 =>
          exists t2,
          gensem ctx e1 (ty_func t2 type) /\
         gensem ctx e2 t2 *)
  end.


(* this one breaks monad laws *)
Inductive freeM' : Type -> Type :=
  | ret_free'  (A : Type)   :   A -> freeM' A
  | bind_free'  (A B : Type)  : freeM' A -> (A -> freeM' B) -> freeM' B
  | assert_free'  :  ty -> ty         -> freeM' unit.


  (*

    Q a
    -------------
    wlp (Some a) Q

  {P} ret a { \x -> Q x }



  *)

  (* Parametrized typeclass of "facts" about instances of the TypeCheckM class
     should contain the definitions for wp and wlp, as well as supporting lemmas.
     Instances of TypeCheckM should also instantiate this class, thereby proving
     the lemmas *)
Class TypeCheckAxioms m {super : TypeCheckM m} : Type :=
  {

  (* WLP / Partial correctness *)

  wlp {O: Type} (mv : m O) (Q : O -> Prop) : Prop;

  wlp_ty_eqb : forall (t1 t2 : ty) (Q : unit -> Prop),
    wlp (assert t1 t2) Q <-> (t1 = t2 -> Q tt);

(* wlp_do : forall {A B : Type} (m1 : m A) (m2 : m B) (Q : B -> Prop),
    @wlp B (m1 ;; m2) Q <-> wlp m1 (fun _ => wlp m2 Q); *)

  wlp_bind : forall {A B : Type} (m1 : m A) (m2 : A -> m B) (Q : B -> Prop),
    wlp (bind m1 m2) Q <-> wlp m1 (fun o => wlp (m2 o) Q);

  wlp_ret : forall {A : Type} (a : A) (Q : A -> Prop),
    wlp (ret a) Q <-> Q a ;

  wlp_fail : forall {A : Type} (Q : A -> Prop),
    wlp (fail) Q <-> True ;

  wlp_monotone : forall {O : Set} (P Q : O -> Prop) (m : m O),
    (forall o : O, P o -> Q o) -> wlp m P -> wlp m Q;

  (* WP / Total correctness *)

  wp {O : Type} (mv : m O) (Q : O -> Prop) : Prop;

  wp_ty_eqb : forall (t1 t2 : ty) (Q : unit -> Prop),
    wp (assert t1 t2) Q <-> t1 = t2 /\ Q tt;

(* wp_do : forall {A B : Type} (m1 : m A) (m2 : m B) (Q : B -> Prop),
    @wp B (m1 ;; m2) Q <-> wp m1 (fun _ => wp m2 Q); *)

  wp_bind : forall {A B : Type} (m1 : m A) (m2 : A -> m B) (Q : B -> Prop),
    wp (bind m1 m2) Q <-> wp m1 (fun o => wp (m2 o) Q);

  wp_ret : forall {A : Type} (a : A) (Q : A -> Prop),
    wp (ret a) Q <-> Q a ;

  wp_fail : forall {A : Type} (Q : A -> Prop),
    wp (fail) Q <-> False ;

  wp_monotone : forall {O : Set} (P Q : O -> Prop) (m : m O),
    (forall o : O, P o -> Q o) -> wp m P -> wp m Q;
}.

(* In the above typeclass definition, [m] is trailing implicit,
   therefore coq declares it maximally inserted. The below vernac command
   turns m explicit and super implicit & maximally inserted I think *)
Arguments TypeCheckAxioms _ {super}.

Check TypeCheckAxioms.

Inductive cstr : Set :=
  | CEq (n1 n2 : ty)
  | CTrue.

(* ================================================ *)
(*                 OPTION INSTANCE                  *)
(* ================================================ *)

#[global] Instance TC_option : TypeCheckM option :=
  { bind T1 T2 m f :=
      match m with
      | None   => None
      | Some x => f x
      end ;
    ret T u := Some u;
    assert t1 t2 := if ty_eqb t1 t2 then Some tt else None;
    fail _ := None ;
  }.

#[refine] Instance TCF_option : TypeCheckAxioms option :=
{
  wlp [O: Type] (m : option O) (Q : O -> Prop) :=
    match m with
    | Some o => Q o
    | None => True
    end;
  wp [O : Type] (m : option O) (Q : O -> Prop) :=
    match m with
    | Some o => Q o
    | None => False
    end;
}. Proof.
  * (* wlp_ty_eqb *)
    destruct t1, t2; cbn; intuition discriminate.
  * (* wlp_bind *)
    destruct m1; reflexivity.
  * (* wlp_ret *)
    intuition.
  * (* wlp_fail *)
    intuition.
  * (* wlp_monotone *)
    destruct m as [|]; intuition.
  * (* wp_ty_eqb *)
    unfold wp. intros t1 t2 Q. destruct (assert t1 t2) eqn:Heq.
    - destruct u. assert (t1 = t2).
      { simpl in Heq. destruct ty_eqb in Heq; congruence. }
      destruct H. clear Heq. firstorder.
    - assert (t1 <> t2).
      { simpl in Heq. destruct ty_eqb in Heq; congruence. }
      clear Heq. unfold not in H. firstorder.
  * (* wp_bind *)
    destruct m1; reflexivity.
  * (* wp_ret *)
    intuition.
  * (* wp_fail *)
    intuition.
  * (* wp_monotone *)
    destruct m; simpl; eauto.
Qed.

(* ================================================ *)
(*              OPTION WRITER INSTANCE              *)
(* ================================================ *)

Definition writer (W A : Type) := prod W A.
Definition option_writer (W A : Type) := option (prod W A).

Unset Printing Universes.

Check (writer (list cstr)).

Check (option_writer (list cstr)).

#[global] Instance TC_writer : TypeCheckM (option_writer (list cstr)) :=
{ bind T1 T2 ma f :=
    match ma with
    | None => None
    | Some ma' => let (cs, x) := ma' in
                 match (f x) with
                 | None => None
                 | Some mb => let (cs', y) := mb in
                              Some (cs ++ cs', y)
                 end
    end ;
  ret T u := Some (nil, u) ;
  assert t1 t2 := Some ([(CEq t1 t2)], tt) ; (* ( [t1 ~~ t2] , () ) *)
  fail _ := None
}.

Fixpoint sem (c : cstr) : Prop :=
  match c with
  | CEq t1 t2  => t1 = t2
  | CTrue  => True
  end.

Fixpoint sems (cs : list cstr) : Prop :=
  match cs with
  | [] => True
  | c :: cs => sem c /\ sems cs
  end.

Lemma sems_append : forall cs cs',
  sems (cs ++ cs') <-> sems cs /\ sems cs'.
Proof.
  intros. split.
  - induction cs; cbn.
    + intro. split. apply I. apply H.
    + intro. Search "and_assoc". rewrite and_assoc. destruct H. split. apply H. apply IHcs. apply H0.
  - intro. destruct H. induction cs; cbn.
    + apply H0.
    + destruct H. split. apply H. apply IHcs. apply H1.
Qed.

(* TODO: throughout, replace firstorder by intuition tactic
         firstorder changes between coq versions and takes longer *)
#[refine] Instance TCF_writer : TypeCheckAxioms (option_writer (list cstr)) :=
{
  wlp [A: Type] (m : option_writer (list cstr) A) (Q : A -> Prop) :=
    match m with
    | Some (cstrs, a) => sems cstrs -> Q a
    | None => True (* we make no distinction between failure in scope level
                      and failure in typeability *)
    end ;

  wp [A: Type] (m : option_writer (list cstr) A) (Q : A -> Prop) :=
    match m with
    | Some (cstrs, a) => sems cstrs /\ Q a
    | None => False
    end ;
}. Proof. (* Simplify some of these proofs *)
  * (* wlp_ty_eqb *)
    intros. destruct (assert t1 t2) eqn:?; inversion Heqy.
    destruct t1, t2; firstorder discriminate.
   (* * (* wlp_do *)
    intros. destruct m1; cbn. destruct p; cbn. destruct m2; cbn. destruct p; cbn. (* firstorder sems_append *)
      rewrite sems_append; firstorder. firstorder. firstorder. (* !!! *) *)
  * (* wlp_bind *)
    intros. destruct m1; cbn. destruct p; cbn. destruct (m2 a); cbn. destruct p; cbn.
    rewrite sems_append; firstorder. firstorder. firstorder.
  * (* wlp_ret *)
    intros. destruct (ret a) eqn:Heqy; inversion Heqy. cbn. intuition.
  * (* wlp_fail *)
    intuition.
  * (* wlp_monotone *)
    intros. destruct m as [[c a]|]; intuition.
  * (* wp_ty_eqb *)
    intros. destruct (assert t1 t2) eqn:?; inversion Heqy.
    destruct t1, t2; firstorder discriminate.
(*  * (* wp_do *)
    intros. destruct m1; cbn. destruct p; cbn. destruct m2; cbn. destruct p; cbn. (* firstorder sems_append *)
    rewrite sems_append; firstorder. firstorder. firstorder. (* !!! *) *)
  * (* wp_bind *)
    intros. destruct m1; cbn. destruct p; cbn. destruct m2; cbn. destruct p; cbn. (* firstorder sems_append *)
    rewrite sems_append; firstorder. firstorder. firstorder. (* !!! *)
  * (* wp_ret *)
    intros. destruct (ret a) eqn:?; inversion Heqy. cbn. intuition.
  * (* wp_fail *)
    intuition.
  * (* wp_monotone *)
    intros. destruct m as [[c a]|]; intuition.
Qed.


(* ================================================ *)
(*                FREE MONAD INSTANCE               *)
(* ================================================ *)


(* bind is encoded using continuations, essentially the
   free monoid forms a list of asserts *)
Inductive freeM (A : Type) : Type :=
  | ret_free  :   A -> freeM A
  | bind_assert_free :  ty -> ty -> freeM A -> freeM A
  | fail_free : freeM A.

Print app.
(* Evaluation of the continuation-based bind of freeM *)
Fixpoint freeM_bind [T1 T2 : Type] (m : freeM T1) (f: T1 -> freeM T2) : freeM T2 :=
  match m with
  | ret_free a => f a
  | fail_free _ => fail_free T2
  | bind_assert_free t1 t2 k =>
      bind_assert_free t1 t2 (freeM_bind k f)
  end.


#[global] Instance TC_free : TypeCheckM freeM :=
  { bind         := freeM_bind ;
    ret T u      := ret_free u ;
    assert t1 t2 := bind_assert_free t1 t2 (ret_free tt); (* equiv. cons (t1, t2) (ret_free tt) *)
    fail T       := fail_free T;
  }.

Fixpoint wlp_freeM [A : Type] (m : freeM A) (Q: A -> Prop) :=
  match m with
  | ret_free a => Q a
  | bind_assert_free t1 t2 k => t1 = t2 ->
      wlp_freeM k Q
  | fail_free _ => True
  end.

Fixpoint wp_freeM [A : Type] (m : freeM A) (Q: A -> Prop) :=
  match m with
  | ret_free a => Q a
  | bind_assert_free t1 t2 k => t1 = t2 /\
      wp_freeM k Q
  | fail_free _ => False
  end.

#[refine] Instance TCF_freeM : TypeCheckAxioms freeM :=
{ wlp := wlp_freeM ;
  wp  := wp_freeM  ;
}. Proof.
  * (* wlp_ty_eqb *)
    intros. destruct (assert t1 t2) eqn:?. firstorder discriminate.
    - destruct y; inversion Heqy. subst. reflexivity.
    - inversion Heqy.
  * (* wlp_bind *)
    split; induction m1; cbn; intuition.
  * (* wlp_ret *)
    intuition.
  * (* wlp_fail *)
    intuition.
  * (* wlp_monotone *)
    intros. induction m; cbn; auto.
  * (* wp_ty_eqb *)
    split; intros.
    - inversion H. cbn in H1. auto.
    - cbn. apply H.
  * (* wp_bind *)
    split; induction m1; cbn; intuition.
  * (* wp_ret *)
    intuition.
  * (* wp_fail *)
    intuition.
  * (* wp_monotone *)
    intros. induction m; cbn; auto.
    inversion H0.
    intuition.
Qed.


Fixpoint infer {m} `{TypeCheckM m} (ctx : env) (expression : expr) : m (prod ty expr) :=
  match expression with
  | v_false => ret (ty_bool, expression)
  | v_true  => ret (ty_bool, expression)
  | v_O     => ret (ty_nat, expression)
  | v_S e   =>
      '(t,e') <- infer ctx e ;;
      (assert t ty_nat) ;;
      ret (ty_nat, v_S e')
  | e_if cnd coq alt =>
      '(t_cnd, e_cnd) <- infer ctx cnd ;;
      '(t_coq, e_coq) <- infer ctx coq ;;
      '(t_alt, e_alt) <- infer ctx alt ;;
      (assert t_cnd ty_bool) ;;
      (assert t_coq t_alt)   ;;
      ret (t_coq, e_if e_cnd e_coq e_alt)
  | e_plus lop rop =>
      '(t_lop, e_lop) <- infer ctx lop ;;
      '(t_rop, e_rop) <- infer ctx rop ;;
      (assert t_lop ty_nat) ;;
      (assert t_rop ty_nat) ;;
      ret (ty_nat, e_plus e_lop e_rop)
  | e_lte lop rop =>
      '(t_lop, e_lop) <- infer ctx lop ;;
      '(t_rop, e_rop) <- infer ctx rop ;;
      (assert t_lop ty_nat) ;;
      (assert t_rop ty_nat) ;;
      ret (ty_bool, e_lte e_lop e_rop)
  | e_and lop rop =>
      '(t_lop, e_lop) <- infer ctx lop ;;
      '(t_rop, e_rop) <- infer ctx rop ;;
      (assert t_lop ty_bool) ;;
      (assert t_rop ty_bool) ;;
      ret (ty_bool, e_and e_lop e_rop)
  | e_let var val bod =>
      '(t_val, e_val) <- infer ctx val ;;
      '(t_bod, e_bod) <- infer ((var, t_val) :: ctx) bod ;;
      ret (t_bod, e_tlet var t_val e_val e_bod)
  | e_tlet var et_val val bod =>
      '(at_val, e_val) <- infer ctx val ;;
      (assert at_val et_val) ;; (* expected/annotated type matches actual type *)
      '(t_bod, e_bod) <- infer ((var, at_val) :: ctx) bod ;;
      ret (t_bod, e_tlet var at_val e_val e_bod)
  | e_var var =>
      match (value var ctx) with
      | Some t_var => ret (t_var, expression)
      | None => fail
      end
  end.

Inductive tpb : env -> expr -> ty -> expr -> Prop :=
  | tpb_false (g : env)
      : tpb g v_false ty_bool v_false
  | tpb_true  (g : env)
     : tpb g v_true ty_bool v_true
  | tpb_zero  (g : env)
     : tpb g v_O ty_nat v_O
  | tpb_succ  (g : env) (e e' : expr)
              (H : tpb g e ty_nat e')
      : tpb g (v_S e) ty_nat (v_S e')
  | tpb_if (g : env) (cnd cnd' : expr)
           (coq coq' : expr) (alt alt' : expr) (t : ty)
           (HCND : tpb g cnd ty_bool cnd')
           (HCOQ : tpb g coq t coq')
           (HALT : tpb g alt t alt')
      : tpb g (e_if cnd coq alt) t
              (e_if cnd' coq' alt')
  | tpb_plus (g : env) (e1 e1' : expr) (e2 e2' : expr)
             (HL : tpb g e1 ty_nat e1')
             (HR : tpb g e2 ty_nat e2')
      : tpb g (e_plus e1 e2) ty_nat
              (e_plus e1' e2')
  | tpb_lte (g : env) (e1 e1' : expr) (e2 e2' : expr)
            (HL : tpb g e1 ty_nat e1')
            (HR : tpb g e2 ty_nat e2')
      : tpb g (e_lte e1 e2) ty_bool
              (e_lte e1' e2')
  | tpb_and (g : env) (e1 e1' : expr) (e2 e2' : expr)
            (HL : tpb g e1 ty_bool e1')
            (HR : tpb g e2 ty_bool e2')
      : tpb g (e_and e1 e2) ty_bool
      (e_and e1' e2')
  | tpb_let (g : env) (v : string)
            (e1 e1' : expr) (e2 e2' : expr)
            (t1 : ty) (t2 : ty)
            (HE1 : tpb g e1 t1 e1')
            (HE2 : tpb ((v, t1) :: g) e2 t2 e2')
      : tpb g (e_let v e1 e2) t2
              (e_tlet v t1 e1' e2') (* provided e1 is typeable with t1,
                                     we can elaborate to an annot. let *)
  | tpb_tlet (g : env) (v : string)
             (e1 e1' : expr) (e2 e2' : expr)
             (t1 : ty) (t2 : ty)
             (HE1 : tpb g e1 t1 e1') (* if e1 is typeable with t1 and elaborates to e1' *)
             (HE2 : tpb ((v, t1) :: g) e2 t2 e2')
      : tpb g (e_tlet v t1 e1 e2) t2
              (e_tlet v t1 e1' e2')
  | tpb_var (g : env) (v : string) (vt : ty)
            (H : (value v g) = Some vt)
      : tpb g (e_var v) vt
              (e_var v).

Notation "G |-- E ; T ~> EE" := (tpb G E T EE) (at level 50).

Lemma infer_sound : forall {m} `{TypeCheckAxioms m} (G : env) (e : expr),
 wlp (infer G e) (fun '(t,ee) => G |-- e ; t ~> ee).
Proof.
  intros. generalize dependent G.
  induction e; cbn [infer].
  - intro. apply wlp_ret. constructor.
  - intro. apply wlp_ret. constructor.
  - intro. apply wlp_ret. constructor.
  - intro. apply wlp_bind. specialize (IHe G). revert IHe. apply wlp_monotone. intros t Ht.
    match goal with
    | |- wlp (match ?t with _ => _ end) _ => destruct t
    end.
    apply wlp_bind. apply wlp_ty_eqb. intro. subst. cbn. apply wlp_ret. constructor. assumption.
  - intro.
    apply wlp_bind. specialize (IHe1 G). revert IHe1. apply wlp_monotone. intros t1 H1. destruct t1.
    apply wlp_bind. specialize (IHe2 G). revert IHe2. apply wlp_monotone. intros t2 H2. destruct t2.
    apply wlp_bind. specialize (IHe3 G). revert IHe3. apply wlp_monotone. intros t3 H3. destruct t3.
    apply wlp_bind. apply wlp_ty_eqb. intros ->.
    apply wlp_bind. apply wlp_ty_eqb. intros ->.
    cbn. apply wlp_ret. constructor; assumption.
  - intro.
    apply wlp_bind. specialize (IHe1 G). revert IHe1. apply wlp_monotone. intros t1 H1. destruct t1.
    apply wlp_bind. specialize (IHe2 G). revert IHe2. apply wlp_monotone. intros t2 H2. destruct t2.
    apply wlp_bind. apply wlp_ty_eqb. intros ->.
    apply wlp_bind. apply wlp_ty_eqb. intros ->.
    cbn. apply wlp_ret. constructor; assumption.
  - intro.
    apply wlp_bind. specialize (IHe1 G). revert IHe1. apply wlp_monotone. intros t1 H1. destruct t1.
    apply wlp_bind. specialize (IHe2 G). revert IHe2. apply wlp_monotone. intros t2 H2. destruct t2.
    apply wlp_bind. apply wlp_ty_eqb. intros ->.
    apply wlp_bind. apply wlp_ty_eqb. intros ->.
    cbn. apply wlp_ret. constructor; assumption.
  - intro.
    apply wlp_bind. specialize (IHe1 G). revert IHe1. apply wlp_monotone. intros t1 H1. destruct t1.
    apply wlp_bind. specialize (IHe2 G). revert IHe2. apply wlp_monotone. intros t2 H2. destruct t2.
    apply wlp_bind. apply wlp_ty_eqb. intros ->.
    apply wlp_bind. apply wlp_ty_eqb. intros ->.
    cbn. apply wlp_ret. constructor; assumption.
  - intro.
    apply wlp_bind. specialize (IHe1 G).             revert IHe1. apply wlp_monotone. intros t1 H1. destruct t1.
    apply wlp_bind. specialize (IHe2 ((s, t) :: G)). revert IHe2. apply wlp_monotone. intros t2 H2. destruct t2.
    cbn. apply wlp_ret. constructor; assumption.
  - intro.
    apply wlp_bind. specialize (IHe1 G).             revert IHe1. apply wlp_monotone. intros t1 H1. destruct t1.
    apply wlp_bind. apply wlp_ty_eqb. intro. subst.
    apply wlp_bind. specialize (IHe2 ((s, t) :: G)). revert IHe2. apply wlp_monotone. intros t2 H2. destruct t2.
    apply wlp_ret. constructor; assumption.
  - intro. destruct (value s G) eqn:?.
    + apply wlp_ret. constructor. apply Heqo.
    + apply wlp_fail. auto.
Restart.
  intros. generalize dependent G. induction e; cbn [infer]; intro;
  repeat (rewrite ?wlp_bind, ?wlp_ty_eqb, ?wlp_ret, ?wlp_fail; try destruct o;
      try match goal with
      | IHe : forall G, wlp (infer G ?e) _ |- wlp (infer ?g ?e) _ =>
          specialize (IHe g); revert IHe; apply wlp_monotone; intros
      | |- tpb _ _ _ _ =>
          constructor
      | |- ?x = ?y -> _ =>
          intro; subst
      | |- wlp (match ?t with _ => _ end) _ => destruct t eqn:?
      end; try reflexivity; try assumption).
Qed.

Lemma infer_complete : forall {m} `{TypeCheckAxioms m} (G : env) (e ee : expr) (t : ty),
  (G |-- e ; t ~> ee) -> wp (infer G e) (fun '(t',ee')  => t = t' /\ ee = ee').
Proof.
  intros. induction H0; cbn;
  repeat (rewrite ?wp_bind, ?wp_ty_eqb, ?wp_ret, ?wp_fail; try destruct o;
      try match goal with
      | IH : wp (infer ?g ?e) _ |- wp (infer ?g ?e) _ =>
          revert IH; apply wp_monotone; intros; subst
      | |- ?x = ?y /\ _ =>
          split
      | H : ?x = ?y /\ _ |- _ =>
          destruct H; subst
      end; try reflexivity). rewrite H0. apply wp_ret. auto.
Qed.

Definition three := (v_S (v_S (v_S v_O))).
Definition two := (v_S (v_S v_O)).
Compute (infer nil (e_plus three two)).
Compute (infer nil
  (e_let "x" three
    (e_lte (e_var "x") two))).

(* Add example using if for boolean constraint *)
(* Add failing example *)

Theorem infer_elaborates : forall G e t ee,
  G |-- e ; t ~> ee -> is_annotated ee.
Proof.
  induction ee; cbn; intros.
Admitted.

Theorem uniqueness_of_typing : forall G e t1 t2 ee,
  G |-- e ; t1 ~> ee ->
  G |-- e ; t2 ~> ee ->
  t1 = t2.
Proof.
Admitted.

Theorem uniqueness_of_elaboration : forall G e t ee1 ee2,
  G |-- e ; t ~> ee1 ->
  G |-- e ; t ~> ee2 ->
  ee1 = ee2.
Proof.
Admitted.

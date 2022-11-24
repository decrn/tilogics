Require Import List.
Require Import String.
Import ListNotations.
From Em Require Import
     STLC.

(* This module implements type inference for STLC
   using a shallow representation of constraints.
   Essentially, constraints are nothing more than propositions in Coq.
   This results in a fairly straightforward implementation,
   but one which is essentially unusable, because we cannot inspect
   the witnesses for these propositions. This is problematic,
   because these witnesses are the unified type variables
   which give the type and the elaboration of the term. *)

(* Monadic type inference for STLC is expressed as a computation inside TypeCheckM.
   Note that STLC requires unification of type variables.
   These type variables are introduced by the exists_ty computation *)
Class TypeCheckM (M : Type -> Type) : Type :=
  {
    ret    {A : Type} :   A -> M A ;
    bind {A B : Type} : M A -> (A -> M B) -> M B ;
    assert            :  ty -> ty         -> M unit ;
    fail   {A : Type} : M A ;
    exists_ty         : M ty ; (* NEW *)
  }.

Notation "x <- ma ;; mb" := (bind ma (fun x => mb))
  (at level 80, ma at next level, mb at level 200, right associativity).
Notation "ma ;; mb" := (bind ma (fun _ => mb))
  (at level 80, right associativity).
Notation "' x <- ma ;; mb" := (bind ma (fun x => mb))
  (at level 80, x pattern, ma at next level, mb at level 200,
    right associativity, format "' x  <-  ma  ;;  mb").

Fixpoint freeM_bind [T1 T2 : Type] (m : freeM T1) (f : T1 -> freeM T2) : freeM T2 :=
  match m with
  | ret_free _ a => f a
  | fail_free _ => fail_free T2
  | bind_asserteq_free _ t1 t2 k =>
      bind_asserteq_free T2 t1 t2 (freeM_bind k f)
  | bind_exists_free _ tf =>
      bind_exists_free T2 (fun t : ty => freeM_bind (tf t) f)
  end.

#[global] Instance TC_free : TypeCheckM freeM :=
  { bind         := freeM_bind ;
    ret T u      := ret_free T u ;
    assert t1 t2 := bind_asserteq_free _ t1 t2 (ret_free _ tt);
    fail T       := fail_free T;
    exists_ty    := bind_exists_free _ (fun t => ret_free _ t);
  }.

Fixpoint generate {m} `{TypeCheckM m} (expression : expr) (ctx : env) : m (prod ty expr) :=
  match expression with
  | v_false => ret (ty_bool, expression)
  | v_true  => ret (ty_bool, expression)
  | e_if cnd coq alt =>
      '(Tcnd, Ecnd) <- generate cnd ctx ;;
      '(Tcoq, Ecoq) <- generate coq ctx ;;
      '(Talt, Ealt) <- generate alt ctx ;;
      assert Tcnd ty_bool            ;;
      assert Tcoq Talt               ;;
      ret (Tcoq, e_if Ecnd Ecoq Ealt)
  | e_var var =>
      match (value var ctx) with
      | Some Tvar => ret (Tvar, expression)
      | None => fail
      end
  | e_app e1 e2 =>
      '(T1, E1) <- generate e1 ctx ;;
      '(T2, E2) <- generate e2 ctx ;;
      T0 <- exists_ty           ;;
      assert T1 (ty_func T2 T0) ;;
      ret (T0, e_app E1 E2)
  | e_absu var e =>
      Tvar <- exists_ty ;;
      '(T, E) <- generate e (cons (var, Tvar) ctx) ;;
      ret (ty_func Tvar T, e_abst var Tvar E)
  | e_abst var Tvar e =>
      '(T, E) <- generate e (cons (var, Tvar) ctx) ;;
      ret (ty_func Tvar T, e_abst var Tvar E)
  end.

Compute (generate (e_app (e_abst "x" ty_bool (e_var "x")) v_true) nil).
Compute (generate (e_app (e_absu "x" (e_var "x")) v_true) nil).

Example K1 := (e_absu "k1" (e_absu "l" (e_var "k1"))).
Example K2 := (e_absu "k2" (e_absu "l" (e_var "k2"))).
Example I := (e_absu "i" (e_var "i")).

Example KKI := (e_app K1 (e_app K2 I)).
Compute (generate KKI nil).

Fixpoint wlp_freeM [A : Type] (m : freeM A) (Q: A -> Prop) : Prop :=
  match m with
  | ret_free _ a => Q a
  | bind_asserteq_free _ t1 t2 k => t1 = t2 ->
      wlp_freeM k Q
  | fail_free _ => True
  | bind_exists_free _ tf => forall t : ty, wlp_freeM (tf t) Q
  end.

Fixpoint wp_freeM [A : Type] (m : freeM A) (Q: A -> Prop) :=
  match m with
  | ret_free _ a => Q a
  | bind_asserteq_free _ t1 t2 k => t1 = t2 /\
      wp_freeM k Q
  | fail_free _ => False
  | bind_exists_free _ tf => exists t : ty, wp_freeM (tf t) Q
  end.

Lemma wlp_ty_eqb : forall (t1 t2 : ty) (Q : unit -> Prop),
  wlp_freeM (assert t1 t2) Q <-> (t1 = t2 -> Q tt).
Proof. destruct t1, t2; cbn; intuition discriminate. Qed.

Lemma wlp_exists_type : forall (Q: ty -> Prop),
  wlp_freeM (exists_ty) Q <-> (forall t : ty, Q t).
Proof.  intuition.  Qed.

Lemma wlp_bind : forall {A B : Type} (m1 : freeM A) (m2 : A -> freeM B) (Q : B -> Prop),
  wlp_freeM (freeM_bind m1 m2) Q <-> wlp_freeM m1 (fun o => wlp_freeM (m2 o) Q).
Proof. split; induction m1; cbn; intuition; destruct H0; exists x; intuition. Qed.

Lemma wlp_ret : forall {A : Type} (a : A) (Q : A -> Prop),
  wlp_freeM (ret a) Q <-> Q a.
Proof.  intuition.  Qed.

Lemma wlp_fail : forall {A : Type} (Q : A -> Prop),
  wlp_freeM (fail) Q <-> True.
Proof.  intuition.  Qed.

Lemma wlp_monotone : forall {O : Set} (P Q : O -> Prop) (m : freeM O),
  (forall o : O, P o -> Q o) -> wlp_freeM m P -> wlp_freeM m Q.
Proof.  intros. induction m; cbn; auto.  Qed.

Lemma wp_ty_eqb : forall (t1 t2 : ty) (Q : unit -> Prop),
  wp_freeM (assert t1 t2) Q <-> t1 = t2 /\ Q tt.
Proof.
  split; intros.
    - inversion H. cbn in H1. auto.
    - cbn. apply H.
Qed.

Lemma wp_exists_type : forall (Q: ty -> Prop),
  wp_freeM (exists_ty) Q <-> (exists t : ty, Q t).
Proof.  intuition.  Qed.

Lemma wp_bind : forall {A B : Type} (m1 : freeM A) (m2 : A -> freeM B) (Q : B -> Prop),
  wp_freeM (freeM_bind m1 m2) Q <-> wp_freeM m1 (fun o => wp_freeM (m2 o) Q).
Proof.  split; induction m1; cbn; intuition; destruct H0; exists x; intuition.  Qed.

Lemma wp_ret : forall {A : Type} (a : A) (Q : A -> Prop),
  wp_freeM (ret a) Q <-> Q a.
Proof.  intuition.  Qed.

Lemma wp_fail : forall {A : Type} (Q : A -> Prop),
  wp_freeM (fail) Q <-> False.
Proof.  cbn. intuition.  Qed.

Lemma wp_monotone : forall {O : Set} (P Q : O -> Prop) (m : freeM O),
  (forall o : O, P o -> Q o) -> wp_freeM m P -> wp_freeM m Q.
Proof.
    intros. induction m; cbn; auto;
    inversion H0; intuition.
    exists x. apply H1. apply H2.
Qed.

(*
(* WP but in Type instead of Prop *)
Fixpoint gen [A : Type] (m : freeM A) : Type :=
  match m with
  | ret_free _ a => unit (* equiv. True in Prop *)
  | bind_asserteq_free _ t1 t2 k => (t1 = t2) * gen k
  | fail_free _ => Empty_set (* equiv. False in Prop *)
  | bind_exists_free _ tf => { τ : ty & gen (tf τ)}
  end%type.

(* Generates an A from a computation m and its proof *)
Fixpoint extract [A : Type] [m : freeM A] {struct m} : gen m -> A.
Proof.
  destruct m; intros P; cbn in P.
  - destruct P. apply (extract _ _ g).
  - apply a.
  - contradiction P.
  - destruct P. apply (extract _ _ g).
Defined.

Print extract.

Eval compute [extract] in extract. (* normalised *)

Lemma test : forall (τ : ty),
  gen (generate
  (e_app (e_absu "x" (e_var "x")) (e_absu "y" (e_var "y"))) nil).
Proof.
  repeat eexists; eauto.
Unshelve.
  exact τ.
Qed.

Eval compute in fun t => extract (test t).
*)

Lemma generate_sound : forall (G : env) (e : expr),
 wlp_freeM (generate e G) (fun '(t,ee) => G |-- e ; t ~> ee).
Proof.
  intros. generalize dependent G. induction e; cbn [generate]; intro;
  repeat (rewrite ?wlp_exists_type, ?wlp_bind, ?wlp_ty_eqb, ?wlp_ret, ?wlp_fail; try destruct o;
      try match goal with
      | IHe : forall G, wlp_freeM (generate ?e G) _
        |- wlp_freeM (generate ?e ?g) _ =>
          specialize (IHe g); revert IHe; apply wlp_monotone; intros
      | |- tpb _ _ _ _ =>
          constructor
      | |- ?x = ?y -> _ =>
          intro; subst
      | |- wlp_freeM (match ?t with _ => _ end) _ =>
          destruct t eqn:?
      | H : ?g |-- ?e ; ?t ~> ?ee
        |- ?g' |-- e_app ?e1 ?e2 ; ?t' ~> e_app ?e1' ?e2' =>
          apply (tpb_app _ _ _ _ _ t0 _)
      end; try firstorder).
Qed.

Lemma generate_complete : forall  (G : env) (e ee : expr) (t : ty),
  (G |-- e ; t ~> ee) ->
  wp_freeM (generate e G) (fun '(t',ee') => t = t' /\ ee = ee').
Proof.
  intros. induction H; cbn;
    repeat (rewrite ?wp_bind, ?wp_ty_eqb, ?wp_ret, ?wp_fail;
            try destruct o; cbn; try rewrite H;
      try match goal with
      | IH : wp_freeM (generate ?e ?g) _ |- wp_freeM (generate ?e ?g) _ =>
          revert IH; apply wp_monotone; intros; subst
      | |- ?x = ?y /\ _ =>
          split
      | H : ?x = ?y /\ _ |- _ =>
          destruct H; subst
      end; try reflexivity).
      - exists vt. apply wp_bind. revert IHtpb. apply wp_monotone.
        intro. destruct o. intro. firstorder; subst; reflexivity.
      - exists t1. firstorder.
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

Example ex_gensem1 :
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


Fixpoint generate_no_elab {m} `{TypeCheckM m} (expression : expr) (ctx : env) : m ty :=
  match expression with
  | v_false => ret ty_bool
  | v_true  => ret ty_bool
  | e_if cnd coq alt =>
      Tcnd <- generate_no_elab cnd ctx  ;;
      assert Tcnd ty_bool            ;;
      Tcoq <- generate_no_elab coq ctx  ;;
      Talt <- generate_no_elab alt ctx  ;;
      assert Tcoq Talt               ;;
      ret Tcoq
  | e_var var =>
      match (value var ctx) with
      | Some Tvar => ret Tvar
      | None      => fail
      end
  | e_app e1 e2 =>
      T0 <- exists_ty            ;;
      T2 <- generate_no_elab e2 ctx ;;
      T1 <- generate_no_elab e1 ctx ;;
      assert T1 (ty_func T2 T0)  ;;
      ret T0
  | e_abst var Tvar e =>
      T <- generate_no_elab e (cons (var, Tvar) ctx) ;;
      ret (ty_func Tvar T)
  | e_absu var e =>
      Tvar <- exists_ty ;;
      T <- generate_no_elab e (cons (var, Tvar) ctx) ;;
      ret (ty_func Tvar T)
  end.

Fixpoint solve a (m : freeM a) : solvedM a :=
  match m with
  | fail_free _ => fail_solved _
  | ret_free _ a => ret_solved _ a
  | bind_asserteq_free _ t1 t2 k => if ty_eqb t1 t2 then solve a k else fail_solved _
  | bind_exists_free _ k => bind_exists_solved a (fun t => solve a (k t))
  end.

Definition infer_ng : expr -> solvedM ty.
Proof.
  intros e.
  pose (generate_no_elab e []%list) as res.
  now apply solve in res.
Defined.

Lemma generate_no_elab_sound : forall (G : env) (e : expr),
  exists ee, wlp_freeM (generate_no_elab e G) (fun '(t) => G |-- e ; t ~> ee).
Admitted.

Lemma generate_no_elab_complete : forall  (G : env) (e ee : expr) (t : ty),
  (G |-- e ; t ~> ee) ->
  wp_freeM (generate_no_elab e G) (fun '(t') => t = t').
Admitted.

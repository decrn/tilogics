Require Import Coq.Classes.RelationClasses.
Require Import Setoid.
Require Import List.
Require Import String.
(* Inductive value : Type :=
  | my_bool : bool -> value
  | my_nat  : nat  -> value.
 *)

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
  | e_var   : string -> expr.

Inductive ty : Type :=
  | ty_nat
  | ty_bool.

Definition ty_eqb (a b : ty) : {a = b} + {a <> b}.
Proof.
  decide equality.
Defined.

(* Small scale reflections *)
(* Fixpoint ty_eqb (a b : ty) : bool :=
  match a, b with
  | ty_nat , ty_nat  => true
  | ty_bool, ty_bool => true
  | _      , _       => false
   end. *)


Definition option_bind {A B} (m : option A) (f : A -> option B) : option B :=
  option_rect _ f None m.
Definition option_assert_eq (a b : ty) : option unit :=
  if ty_eqb a b then Some tt else None.

Notation "x <- ma ;; mb" :=
        (option_bind ma (fun x => mb))
          (at level 80, ma at next level, mb at level 200, right associativity).
Notation "ma ;; mb" := (option_bind ma (fun _ => mb)) (at level 80, right associativity).
Notation "a ~~ b" := (option_assert_eq a b) (at level 80, no associativity).

Fixpoint value {X: Type} (var : string) (ctx : list (string * X)) : option X :=
  match ctx with
  | nil => None
  | (var', val) :: ctx' =>
      if (string_dec var var') then Some val else (value var ctx')
  end.

Fixpoint infer (ctx : list (string * ty)) (expression : expr) : option ty :=
  match expression with
  | v_false => Some ty_bool
  | v_true  => Some ty_bool
  | v_O     => Some ty_nat
  | v_S e   =>
     te <- infer ctx e ;;
     te ~~ ty_nat ;;
     Some te
  | e_if cnd coq alt =>
    t1 <- infer ctx cnd ;;
    t2 <- infer ctx coq ;;
    t3 <- infer ctx alt ;;
    t1 ~~ ty_bool ;;
    t2 ~~ t3 ;;
    Some t2
  | e_plus lop rop =>
    t1 <- infer ctx lop ;;
    t2 <- infer ctx rop ;;
    t1 ~~ ty_nat ;;
    t2 ~~ ty_nat ;;
    Some ty_nat
  | e_lte e1 e2 =>
    t1 <- infer ctx e1 ;;
    t2 <- infer ctx e2 ;;
    t1 ~~ ty_nat ;;
    t2 ~~ ty_nat ;;
    Some ty_bool
  | e_and e1 e2 =>
    t1 <- infer ctx e1 ;;
    t2 <- infer ctx e2 ;;
    t1 ~~ ty_bool ;;
    t2 ~~ ty_bool ;;
    Some ty_bool
  | e_let var val e =>
    tval <- infer ctx val ;;
    te <- infer ((var, tval) :: ctx) e ;;
    Some te
  | e_var var =>
    value var ctx
  end.

Definition env := list (string * ty).

Inductive tpb : env -> expr -> ty -> Prop :=
  | tpb_false (g : env)
     : tpb g v_false ty_bool
  | tpb_true  (g : env)
     : tpb g v_true ty_bool
  | tpb_zero  (g : env)
     : tpb g v_O ty_nat
  | tpb_succ  (g : env) (e : expr)
              (H : tpb g e ty_nat)
      : tpb g (v_S e) ty_nat
  | tpb_if (g : env) (cnd : expr)
           (coq : expr) (alt : expr) (t : ty)
           (HCND : tpb g cnd ty_bool)
           (HCOQ : tpb g coq t)
           (HALT : tpb g alt t)
      : tpb g (e_if cnd coq alt) t
  | tpb_plus (g : env) (e1 : expr) (e2 : expr)
             (HL : tpb g e1 ty_nat)
             (HR : tpb g e2 ty_nat)
      : tpb g (e_plus e1 e2) ty_nat
  | tpb_lte (g : env) (e1 : expr) (e2 : expr)
            (HL : tpb g e1 ty_nat)
            (HR : tpb g e2 ty_nat)
      : tpb g (e_lte e1 e2) ty_bool
  | tpb_and (g : env) (e1 : expr) (e2 : expr)
            (HL : tpb g e1 ty_bool)
            (HR : tpb g e2 ty_bool)
      : tpb g (e_and e1 e2) ty_bool
  | tpb_let (g : env) (v : string)
            (e1 : expr) (e2 : expr)
            (t1 : ty) (t2 : ty)
            (HE1 : tpb g e1 t1)
            (HE2 : tpb ((v, t1) :: g) e2 t2)
      : tpb g (e_let v e1 e2) t2
  | tpb_var (g : env) (v : string) (vt : ty)
            (H : (value v g) = Some vt)
      : tpb g (e_var v) vt.

Notation "G |-- E ; T" := (tpb G E T) (at level 50).

Lemma infer_sound : forall (G : env) (e : expr) (t : ty),
  infer G e = Some t -> G |-- e ; t.
Proof.
  intros G e t E.
  induction e.
  - inversion E. apply tpb_true.
  - inversion E. apply tpb_false.
  - inversion E. apply tpb_zero.
  - cbn in E. destruct (infer G e). cbn in E.
    destruct option_assert_eq eqn:? in E.
    unfold option_assert_eq in Heqo.
    admit.
  (* .... *)
Admitted.

(* True => [ infer G e ] => (fun t => G |-- e ; t) *)

Definition HT I O
  (pre : I -> Prop)
  (comp : I -> option O)
  (post : O -> Prop) : Prop :=
  forall i, pre i -> match comp i with
                     | Some o => post o
                     | None => True
                     end.

Definition HT' O
  (pre : Prop)
  (comp : option O)
  (post : O -> Prop) : Prop :=
  pre -> match comp with
         | Some o => post o
         | None => True
         end.

Definition wlp {O: Type}
    (m : option O)
    (Q : O -> Prop) : Prop :=
  match m with
  | Some o => Q o
  | None => True
  end.

Theorem foobar : forall {O} (pre : Prop) (comp : option O) (post : O -> Prop),
  HT' O pre comp post <-> pre -> (wlp comp post).
Proof.
  intros.
  destruct comp; firstorder.
Qed.


Lemma HSome : forall O (o : O) (P : Prop) (Q : O -> Prop),
  (P -> Q o) -> HT' O P (Some o) Q.
Proof.
  intros.
  unfold HT'.
  eauto.
Qed.

Lemma infer_sound' : forall (G : env) (e : expr),
  (HT' ty True (infer G e) (fun t => G |-- e ; t)).
Proof.
  unfold HT'.
Abort.

Lemma wlp_ty_eqb : forall (t1 t2 : ty) (Q : Prop),
  wlp (t1 ~~ t2) (fun _ : unit => Q) <-> (t1 = t2) -> Q.
Proof.
  intros t1 t2 Q.
  unfold wlp.
  unfold option_assert_eq.
  (* I need SSR, but don't understand it yet *)
  (* this proof is not extensible *)
  destruct t1; destruct t2; simpl; try firstorder; try discriminate.
Qed.

(* STEVE: You will want to use these equivalences when rewriting. This one
   in particular to rewrite from left to right. Therefore it's important to
   make matching it as easy as possible. Having an arbitrary Q instead of the
   structure (fun _ => Q) is easier.
 *)
Lemma wlp_ty_eqb' (t1 t2 : ty) (Q : unit -> Prop) :
  wlp (t1 ~~ t2) Q <-> (t1 = t2 -> Q tt).
Proof. destruct t1, t2; cbn; firstorder discriminate. Qed.

(* both of these seem fishy *)
Lemma wlp_do : forall {A B : Type} (m1 : option A) (m2 : option B) (Q : B -> Prop),
     @wlp B (m1 ;; m2) Q <-> wlp m1 (fun _ => wlp m2 Q).
Proof.
  destruct m1; reflexivity.
Qed.

  Check option_bind.
Lemma wlp_bind : forall {A B : Type} (m1 : option A) (m2 : A -> option B) (Q : B -> Prop),
  (*  wlp (option_bind m1 (fun x => m2)) Q <-> wlp m1 (fun x => wlp m2 Q). *)

  wlp (option_bind m1 m2) Q <-> wlp m1 (fun o => wlp (m2 o) Q).
Proof.
  destruct m1; reflexivity.
Qed.

Lemma wlp_monotone : forall {O : Set} (P Q : O -> Prop) (m : option O),
  (forall o : O, P o -> Q o) -> wlp m P -> wlp m Q.
Proof.
  destruct m; simpl; eauto.
Qed.

Lemma wlp_value : forall (G : env) (s : string) (Q : ty -> Prop),
wlp (value s G) Q <-> forall t, value s G = Some t -> Q t.
Proof.
  unfold wlp. intros. destruct (value s G) eqn:?; split; try congruence.
  - intro. specialize (H t). apply H. reflexivity.
  - intro. admit.
Admitted.

Lemma infer_sound'' : forall (G : env) (e : expr),
  wlp (infer G e) (fun t => G |-- e ; t).
Proof.
  intros. generalize dependent G.
  induction e; cbn.
  - apply tpb_true.
  - apply tpb_false.
  - apply tpb_zero.
  - intro. apply wlp_bind. specialize (IHe G). revert IHe. apply wlp_monotone. intros t H.
    apply wlp_do. apply wlp_ty_eqb'. intro. subst. cbn. constructor. assumption.
  - intro. apply wlp_bind. specialize (IHe1 G). revert IHe1. apply wlp_monotone. intros t1 H1.
    apply wlp_bind. specialize (IHe2 G). revert IHe2. apply wlp_monotone. intros t2 H2.
    apply wlp_bind. specialize (IHe3 G). revert IHe3. apply wlp_monotone. intros t3 H3.
    apply wlp_do. apply wlp_ty_eqb'. intros ->.
    apply wlp_do. apply wlp_ty_eqb'. intros ->.
    cbn. constructor; assumption.
  - intro. apply wlp_bind. specialize (IHe1 G). revert IHe1. apply wlp_monotone. intros t1 H1.
    apply wlp_bind. specialize (IHe2 G). revert IHe2. apply wlp_monotone. intros t2 H2.
    apply wlp_do. apply wlp_ty_eqb'. intros ->.
    apply wlp_do. apply wlp_ty_eqb'. intros ->.
    cbn. constructor; assumption.
  - intro. apply wlp_bind. specialize (IHe1 G). revert IHe1. apply wlp_monotone. intros t1 H1.
    apply wlp_bind. specialize (IHe2 G). revert IHe2. apply wlp_monotone. intros t2 H2.
    apply wlp_do. apply wlp_ty_eqb'. intros ->.
    apply wlp_do. apply wlp_ty_eqb'. intros ->.
    cbn. constructor; assumption.
  - intro. apply wlp_bind. specialize (IHe1 G). revert IHe1. apply wlp_monotone. intros t1 H1.
    apply wlp_bind. specialize (IHe2 G). revert IHe2. apply wlp_monotone. intros t2 H2.
    apply wlp_do. apply wlp_ty_eqb'. intros ->.
    apply wlp_do. apply wlp_ty_eqb'. intros ->.
    cbn. constructor; assumption.
  - intro. apply wlp_bind. specialize (IHe1 G). revert IHe1. apply wlp_monotone. intros t1 H1.
    apply wlp_bind. specialize (IHe2 ((s, t1) :: G)). revert IHe2. apply wlp_monotone. intros t2 H2.
    cbn. apply tpb_let with t1; assumption.
  - intro. rewrite wlp_value. intros. constructor. apply H.
Qed.


Lemma infer_complete : forall (G : env) (e : expr) (t : ty),
  G |-- e ; t -> infer G e = Some t.
Proof.
  intros G e t E.
  induction E; simpl; try reflexivity.
  + now rewrite IHE.
  + now rewrite IHE1, IHE2, IHE3; destruct t; reflexivity.
  + now rewrite IHE1, IHE2.
  + now rewrite IHE1, IHE2.
  + now rewrite IHE1, IHE2.
  + rewrite IHE1.
    destruct t1; simpl; rewrite IHE2; reflexivity.
  + apply H.
Restart.
  intros G e t E.
  induction E; simpl;
    repeat
      match goal with
      | IH : context[infer _ ?e = Some _] |- context[_ = _] => rewrite IH
      end; simpl; try reflexivity; try firstorder.
    now destruct t.
    now rewrite IHE2.
Qed.

Theorem infer_equiv : forall (G : env) (e : expr) (t : ty),
  infer G e = Some t <-> G |-- e ; t.
Proof.
  split.
  - apply infer_sound.
  - apply infer_complete.
Qed.

Definition wp {O : Type}
    (m : option O)
    (Q : O -> Prop) : Prop :=
  match m with
  | Some o => Q o
  | None => False
  end.

Lemma wp_ty_eqb : forall (t1 t2 : ty) (Q : unit -> Prop),
  wp (t1 ~~ t2) Q <-> t1 = t2 /\ Q tt.
Proof.
  unfold wp. intros t1 t2 Q. destruct (t1 ~~ t2) eqn:?.
  - destruct u. assert (t1 = t2).
    { unfold option_assert_eq in Heqo. destruct ty_eqb in Heqo; congruence. }
    clear Heqo. firstorder.
  - assert (t1 <> t2).
    { unfold option_assert_eq in Heqo. destruct ty_eqb in Heqo; congruence. }
    clear Heqo. unfold not in H. firstorder.
Qed.

Lemma wp_do : forall {A B : Type} (m1 : option A) (m2 : option B) (Q : B -> Prop),
     @wp B (m1 ;; m2) Q <-> wp m1 (fun _ => wp m2 Q).
Proof.
  destruct m1; reflexivity.
Qed.

Lemma wp_value : forall (G : env) (s : string) (Q : ty -> Prop),
  wp (value s G) Q <-> exists t, value s G = Some t /\ Q t.
Proof.
  intros. destruct (value s G); unfold wp; firstorder congruence.
Qed.

(* No longer that useful because of reformulation of completeness proof *)
Lemma wp_var : forall (G : env) (s : string),
  wp (value s G) (fun t : ty => G |-- e_var s; t) <-> exists t, (value s G) = Some t.
Proof.
  intros G s.
  split.
  * intro. destruct value.
    - exists t. reflexivity.
    - cbn in H. exfalso. apply H.
  * intro. destruct H. rewrite H. cbn. constructor. assumption.
Qed.

Lemma wp_bind : forall {A B : Type} (m1 : option A) (m2 : A -> option B) (Q : B -> Prop),
  wp (option_bind m1 m2) Q <-> wp m1 (fun o => wp (m2 o) Q).
Proof.
  destruct m1; reflexivity.
Qed.

Lemma wp_monotone : forall {O : Set} (P Q : O -> Prop) (m : option O),
  (forall o : O, P o -> Q o) -> wp m P -> wp m Q.
Proof.
  destruct m; simpl; eauto.
Qed.

(* {G |-- e ; t} infer G e { fun t' => t = t' } *)
Lemma infer_complete' : forall (G : env) (e : expr) (t : ty),
  (G |-- e ; t) -> wp (infer G e) (fun t' => t = t').
Proof.
  intros. induction H; cbn;
  repeat (rewrite ?wp_bind, ?wp_do, ?wp_ty_eqb;
      try match goal with
      | IH : wp (infer ?g ?e) _ |- wp (infer ?g ?e) _ =>
          revert IH; apply wp_monotone; intros; subst
      | |- ?x = ?x /\ _ =>
          split
      end; try reflexivity). rewrite H. cbn. reflexivity.
Qed.

(* Completeness of check *)
(* {G |-- e ; t} check G e t { True } *)


(* TODO: formulate wp and wlp for writer monad *)
(* TODO: formulate infer with (TypeCheckM m) argument *)
(* TODO: proof soundness + completeness of aformentioned generic infer *)

(*
Lemma infer_complete' : forall (G : env) (e : expr) (t : ty),
  wp (infer G e) (fun t' => t = t').
Proof.
  intros. generalize dependent G.
  induction e; cbn; try (constructor; fail).
  - intros. apply wp_bind. specialize (IHe G). revert IHe. apply wp_monotone.
    intros. apply wp_do. apply wp_ty_eqb.
    intros ->. cbn. constructor. assumption.
  - intro. apply wp_bind. specialize (IHe1 G). revert IHe1. apply wp_monotone. intros t1 H1.
    apply wp_bind. specialize (IHe2 G). revert IHe2. apply wp_monotone. intros t2 H2.
    apply wp_bind. specialize (IHe3 G). revert IHe3. apply wp_monotone. intros t3 H3.
    apply wp_do. apply wp_ty_eqb. intros ->.
    apply wp_do. apply wp_ty_eqb. intros ->.
    cbn. constructor; assumption.
  - intro. apply wp_bind. specialize (IHe1 G). revert IHe1. apply wp_monotone. intros t1 H1.
    apply wp_bind. specialize (IHe2 G). revert IHe2. apply wp_monotone. intros t2 H2.
    apply wp_do. apply wp_ty_eqb. intros ->.
    apply wp_do. apply wp_ty_eqb. intros ->.
    cbn. constructor; assumption.
  - intro. apply wp_bind. specialize (IHe1 G). revert IHe1. apply wp_monotone. intros t1 H1.
    apply wp_bind. specialize (IHe2 G). revert IHe2. apply wp_monotone. intros t2 H2.
    apply wp_do. apply wp_ty_eqb. intros ->.
    apply wp_do. apply wp_ty_eqb. intros ->.
    cbn. constructor; assumption.
  - intro. apply wp_bind. specialize (IHe1 G). revert IHe1. apply wp_monotone. intros t1 H1.
    apply wp_bind. specialize (IHe2 G). revert IHe2. apply wp_monotone. intros t2 H2.
    apply wp_do. apply wp_ty_eqb. intros ->.
    apply wp_do. apply wp_ty_eqb. intros ->.
    cbn. constructor; assumption.
  - intro. apply wp_bind. specialize (IHe1 G). revert IHe1. apply wp_monotone. intros t1 H1.
    apply wp_bind. specialize (IHe2 ((s, t1) :: G)). revert IHe2. apply wp_monotone. intros t2 H2.
    cbn. apply tpb_let with t1; assumption.
  - intro. rewrite wp_var. destruct value; cbn.
    + exists t0. reflexivity.
    +  exists t. admit.
Admitted.

 *)

Theorem infer_equiv' : forall (G : env) (e : expr) (t : ty),
  infer G e = Some t <-> G |-- e ; t.
Proof.
  split.
  - apply infer_sound.
  - apply infer_complete.
Qed.

Locate decidable.
Print Decidable.decidable.

(* (Decidable.decidable (G |-- e ; t)). *)
Lemma tpb_decidable : forall (G : env) (e : expr) (t : ty),
  Decidable.decidable (G |-- e ; t).
Proof.
  intros. unfold Decidable.decidable.
  destruct (infer G e) eqn:?.
  - destruct (ty_eqb t t0). subst. left. auto. apply infer_equiv'. apply Heqo.
    right. intro. apply infer_complete' in H. rewrite Heqo in H. cbn in H. congruence.
  - right. intro. apply infer_complete' in H. rewrite Heqo in H. cbn in H. congruence.
Qed.

Definition fun_computation : expr :=
  (e_let "x" (v_S (v_S (v_S (v_S v_O))))
  (e_let "y" (v_S v_O)
    (e_if
      (e_lte (e_var "x") (e_var "y"))
      (e_var "x")
      (e_var "y")))).

Example test_infer_let1 :
  Some ty_nat = infer nil fun_computation.
Proof. reflexivity. Qed.

(* Fixpoint infer' (expression : expr) : cstr * ty := *)

(* something something all inductively defined types
   with two constructors correspond to the bools
   so this is probably useless *)
Definition isSome {X : Type} (opt : option X) : bool :=
  match opt with
  | Some _ => true
  | None   => false
  end.


Notation "ma ??" := (isSome ma)  (at level 80, no associativity).

(* Fixpoint check (ctx : list (string * ty)) (expression : expr) (type : ty) : bool :=
  match expression with
  | v_true  => type ~~ ty_bool ??
  | v_false => type ~~ ty_bool ??
  | v_O     => type ~~ ty_nat  ??
  | v_S v   => check ctx v ty_nat
  | e_if cnd coq alt =>
      check ctx cnd ty_bool &&
      check ctx coq type    &&
      check ctx alt type
  | e_plus lop rop =>
      type ~~ ty_nat ?? &&
      check ctx lop ty_nat  &&
      check ctx rop ty_nat
  | e_lte e1 e2 =>
      type ~~ ty_bool ?? &&
      check ctx e1 ty_nat    &&
      check ctx e2 ty_nat
  | e_and e1 e2 =>
      type ~~ ty_bool ?? &&
      check ctx e1 ty_bool   &&
      check ctx e2 ty_bool
  | e_let var t val e =>
      check val t &&
      check ((var, t) :: ctx) e type
  | e_var var =>
      match (value var ctx) with
      | None => false
   (* | Some exp => check ctx exp type *)
      | _ => false
      end
  end.
 *)
Example test_infer_if1 :
  Some ty_nat = infer nil (e_if v_true v_O (v_S v_O)).
Proof. reflexivity. Qed.

Example test_infer_if2 :
  None = infer nil (e_if v_true v_false (v_S v_O)).
Proof. reflexivity. Qed.

Example test_infer_if3 :
  None = infer nil (e_if v_O v_O (v_S v_O)).
Proof. reflexivity. Qed.

Example test_successor_false :
  None = infer nil (v_S v_false).
Proof. reflexivity. Qed.

Example test_infer_plus1 :
  Some ty_nat = infer nil (e_plus v_O (v_S v_O)).
Proof. reflexivity. Qed.

Example test_infer_plus2 :
  None = infer nil (e_plus v_true (v_S v_O)).
Proof. reflexivity. Qed.

Example test_infer_lte1 :
  Some ty_bool = infer nil (e_lte v_O (v_S v_O)).
Proof. reflexivity. Qed.

Example test_infer_lte2 :
  None = infer nil (e_lte v_true (v_S v_O)).
Proof. reflexivity. Qed.

Example test_infer_and1 :
  None = infer nil (e_and v_O (v_S v_O)).
Proof. reflexivity. Qed.

Example test_infer_and2 :
  None = infer nil (e_and v_true (v_S v_O)).
Proof. reflexivity. Qed.

Example test_infer_and3 :
  Some ty_bool = infer nil (e_and v_true v_false).
Proof. reflexivity. Qed.

(*
Eval cbv in infer (e_and v_true v_false).
Compute infer (e_and v_true v_false).
 *)

Locate "a /\ b".

Fixpoint gensem (ctx : list (string * ty)) (expression : expr) (type : ty) : Prop :=
  match expression with
  | v_true  => type = ty_bool
  | v_false => type = ty_bool
  | v_O     => type = ty_nat
  | v_S v   => gensem ctx v ty_nat
  | e_if cnd coq alt =>
     gensem ctx cnd ty_bool /\
     gensem ctx coq type    /\
     gensem ctx alt type
  | e_plus lop rop =>
     type = ty_nat  /\
     gensem ctx lop ty_nat /\
     gensem ctx rop ty_nat
  | e_lte e1 e2 =>
     type = ty_bool /\
     gensem ctx e1 ty_nat  /\
     gensem ctx e2 ty_nat
  | e_and e1 e2 =>
     type = ty_bool /\
     gensem ctx e1 ty_bool /\
     gensem ctx e2 ty_bool
  | e_let var val e =>
      exists (t : ty),
      gensem ctx val t /\
      gensem ((var, t) :: ctx) e type
  | e_var var =>
      match (value var ctx) with
      | None => False
      | Some t => t = type
      end
  end.


Lemma some_test :
  gensem nil (e_and v_true v_false) ty_bool.
Proof.
  compute.
  (* reflexivity. *)
  split. split. split. reflexivity. reflexivity.
Qed.

Definition infer' (expression : expr) : Prop :=
  exists type : ty, gensem nil expression type.
  (* exists really unifies a type variable to make it "fit" *)

Print True.
Print False.
Print and.
Print eq.

(* are these really all that I needed? *)
Inductive cstr : Set :=
  | CAnd (c1 c2 : cstr)
  | CEq (n1 n2 : ty).

Fixpoint gen (ctx : list (string * expr)) (expression : expr) (type : ty) : cstr :=
  match expression with
  | v_true  => CEq type ty_bool
  | v_false => CEq type ty_bool
  | v_O     => CEq type ty_nat
  | v_S e   => gen ctx e type
  | e_if cnd coq alt =>
      CAnd (gen ctx cnd ty_bool)
           (CAnd (gen ctx coq type)
                 (gen ctx alt type))
  | e_plus lop rop =>
      CAnd (CEq type ty_nat)
           (CAnd (gen ctx lop ty_nat)
                 (gen ctx rop ty_nat))
  | e_lte e1 e2 =>
      CAnd (CEq type ty_bool)
           (CAnd (gen ctx e1 ty_nat)
                 (gen ctx e2 ty_nat))
  | e_and e1 e2 =>
      CAnd (CEq type ty_bool)
           (CAnd (gen ctx e1 ty_bool)
                 (gen ctx e2 ty_bool))
  | e_let var val e =>
      (* let var = val in e *)
      gen ((var, val) :: ctx) e type
  | e_var var =>
      match (value var ctx) with
      | None => CEq ty_nat ty_bool
   (* | Some exp => gen ctx exp type *)
      | _ => CEq ty_nat ty_nat
      end
  end.

Fixpoint sem (c : cstr) : Prop :=
  match c with
  | CAnd c1 c2 => and (sem c1) (sem c2)
  | CEq t1 t2  => t1 = t2
  end.

Compute sem (gen nil v_O ty_nat).
Compute gensem nil v_O ty_nat.

Theorem sem_o_gen_eq_gensem : forall (e : expr) (t : ty),
  sem (gen nil e t) <-> gensem nil e t.
Proof.
  intros.
  induction e; cbn.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct t.
    + rewrite IHe. reflexivity.
Abort.

(* solve returns true if the given constraint
   is satisfiable *)
Fixpoint solve (constraint : cstr) : bool :=
  match constraint with
  | CEq t1 t2 => t1 ~~ t2 ??
  | CAnd c1 c2 => andb (solve c1) (solve c2)
  end.

Example test_solve_true1 :
  true = solve (CAnd (CEq ty_nat ty_nat) (CEq ty_bool ty_bool)).
Proof. reflexivity. Qed.

Example test_solve_false1 :
  false = solve (CAnd (CEq ty_nat ty_bool) (CEq ty_bool ty_bool)).
Proof. reflexivity. Qed.


(*

================ [True]
 true : ty_bool

================ [False]
 false : ty_bool

================ [Zero]
 zero : ty_nat

   n : ty_nat
================= [Succ]
 succ n : ty_nat

cnd : ty_bool        coq : ty           alt : ty
================================================    [If]
          if cnd then coq else alt : ty

lop : ty_nat     rop : ty_nat
=============================   [Plus]
    plus lop rop : ty_nat

e1 : ty_nat       e2 : ty_nat
=============================   [Lte]
    lte e1 e2 : ty_bool

e1 : ty_bool     e2 : ty_bool
=============================   [And]
    and e1 e2 : ty_bool

 G |-- e1 : ty1   G U { x : ty1 } |-- e2 : ty2
=========================================   [Let]
     G |-- let x = e1 in e2 : ty2


x : ty  in Gamma there exists an x : ty
============ [Var]
  x : ty

  ^--- x as an expression
  *)


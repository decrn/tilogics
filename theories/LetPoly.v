From Coq Require Import
  Classes.Morphisms
  Relations.Relation_Definitions
  Strings.String.
From Equations Require Import
     Equations.
From Em Require Import
     Context Environment Prelude.

Set Implicit Arguments.
Set Transparent Obligations.

(* =================================== *)
(*  The Simply-Typed Lambda Calculus   *)
(*      extended with Booleans         *)
(* =================================== *)

(* ===== Types ===== *)
Notation TVarCtx := (Ctx unit).

Module ty.
  Inductive Mono (Δ : TVarCtx) : Type :=
  | var {b} (i : ctx.In b Δ)
  | bool
  | func (t1 t2 : Mono Δ).
  Derive NoConfusion Subterm for Mono.
  #[global] Arguments bool {Δ}.

  Lemma mono_no_cycle {Δ} (t : Mono Δ) : ~ Mono_subterm t t.
  Proof.
    induction (well_founded_Mono_subterm t) as [? _ IH].
    intros Ht. apply (IH _ Ht Ht).
  Qed.

  Set Primitive Projections.
  Record Poly (Δ : TVarCtx) : Type :=
    poly
      { vars : TVarCtx;
        to   : Mono (ctx.cat Δ vars);
      }.

  Definition of {Δ} (t : Mono Δ) : Poly Δ :=
    @poly Δ ctx.nil t.

End ty.
Export ty (Mono, Poly).
Export (hints) ty.

(* ===== Terms / Expressions ===== *)

Module exp.
  Inductive Exp (Δ : TVarCtx) : Type :=
  | var (x : string)
  | true
  | false
  | ifte (e1 e2 e3 : Exp Δ)
  | absu (x : string) (e : Exp Δ)
  | abst (x : string) (t : Mono Δ) (e : Exp Δ)
  | app (e1 e2 : Exp Δ)
  | letp (x : string) (σ : Poly Δ) (e1 : Exp (ctx.cat Δ (ty.vars σ))) (e2 : Exp Δ).
  Derive NoConfusion for Exp.
End exp.
Export exp (Exp).
Export (hints) exp.


(* ===== Typing Context ===== *)

Definition Env Δ := list (string * Poly Δ).

(* Definition Env Σ := list (string * Ty Σ). *)

(* Context lookup *)
Fixpoint resolve {A} (x : string) (G : list (string * A)) : option A :=
  match G with
  | nil           => None
  | cons (y,a) G' => if eq_dec x y then Some a else resolve x G'
  end.

Module Import Sub.
  Definition Sub (Δ0 Δ1 : TVarCtx) : Type :=
    @env.Env unit (fun _ => Mono Δ1) Δ0.

  Definition refl {Δ} : Sub Δ Δ :=
    env.tabulate (fun α αIn => ty.var αIn).

  Definition injl {Δ0 Δ1} : Sub Δ0 (ctx.cat Δ0 Δ1) :=
    env.tabulate (fun α αIn => ty.var (ctx.in_cat_left Δ1 αIn)).

  Definition injr {Δ0 Δ1} : Sub Δ1 (ctx.cat Δ0 Δ1) :=
    env.tabulate (fun α αIn => ty.var (ctx.in_cat_right αIn)).

  Class Subst (T : TVarCtx -> Type) : Type :=
    subst : forall {Δ0} (t : T Δ0) {Δ1} (θ : Sub Δ0 Δ1), T Δ1.
  #[global] Arguments subst {T _} [Δ0] t [Δ1] θ.

  #[export] Instance subst_mono : Subst Mono :=
    fix subst_mono {Δ0} t {Δ1} θ :=
      match t with
      | ty.var αIn    => env.lookup θ αIn
      | ty.bool       => ty.bool
      | ty.func t1 t2 => ty.func (subst_mono t1 θ) (subst_mono t2 θ)
      end.

  Definition comp {Δ0 Δ1 Δ2} (θ1 : Sub Δ0 Δ1) (θ2 : Sub Δ1 Δ2) : Sub Δ0 Δ2 :=
    env.map (fun _ (t : Mono Δ1) => subst t θ2) θ1.

  Definition up {Δ0 Δ1} (θ : Sub Δ0 Δ1) αs :
    Sub (ctx.cat Δ0 αs) (ctx.cat Δ1 αs) :=
    env.cat (comp θ injl) injr.

  Definition up1 {Δ0 Δ1} (θ : Sub Δ0 Δ1) {b} : Sub (ctx.snoc Δ0 b) (ctx.snoc Δ1 b) :=
    up θ (ctx.snoc ctx.nil b).

  #[export] Instance subst_poly : Subst Poly :=
    fun Δ0 t Δ1 θ =>
      {| ty.vars := ty.vars t;
         ty.to   := subst (ty.to t) (up θ (ty.vars t))
      |}.

  #[export] Instance subst_env : Subst Env.
  Proof. Admitted.

  #[export] Instance subst_exp : Subst Exp :=
    fix F {Δ0} (e : Exp Δ0) {Δ1} (θ : Sub Δ0 Δ1) {struct e} : Exp Δ1 :=
      match e with
      | exp.var _ x        => exp.var Δ1 x
      | exp.true _         => exp.true _
      | exp.false _        => exp.false _
      | exp.ifte e1 e2 _   => exp.ifte (F e1 θ) (F e2 θ) (F e2 θ)
      | exp.absu x e1      => exp.absu x (F e1 θ)
      | exp.abst x t e1    => exp.abst x (subst t θ) (F e1 θ)
      | exp.app e1 e2      => exp.app (F e1 θ) (F e2 θ)
      | exp.letp x σ e1 e2 => exp.letp x (subst σ θ)
                                (F e1 (up θ (ty.vars (@subst Poly subst_poly _ σ _ θ))))
                                (F e2 θ)
      end.

  Lemma subst_refl {T Δ} `{Subst T} :
    forall t : T Δ, subst t refl = t.
  Proof. Admitted.

End Sub.

#[local] Notation "s [ θ ]" :=
  (subst s θ)
    (at level 8, left associativity,
      format "s [ θ ]").

(* ===== Typing relation ===== *)

Definition is_instance {Δ} (σ : Poly Δ) (t : Mono Δ) : Prop :=
  exists θ : Sub (ty.vars σ) Δ, (ty.to σ)[env.cat Sub.refl θ] = t.

(* Coercion ty.mono : Mono >-> Poly. *)

Definition sub {Δ} (σ1 : Poly Δ) (σ2 : Poly Δ) : Prop :=
  match σ1 , σ2 with
  | ty.poly _ αs τ1, ty.poly _ βs τ2 =>
      exists θ : Sub αs (ctx.cat Δ βs),
        subst τ1 (env.cat injl θ) = τ2
  end.

Module JustTyping.

  Reserved Notation "G ∣ w ⊢ᴰ E ∷ T" (at level 90).
  Reserved Notation "G ∣ w ⊢ᴬ E ∷ T" (at level 90).

  Inductive decl {Δ} (Γ : Env Δ) : Exp Δ -> Poly Δ -> Prop :=

  | tpb_var x σ :
    resolve x Γ = Some σ ->
    Δ ∣ Γ ⊢ᴰ exp.var Δ x ∷ σ

  | tpb_true :
    Δ ∣ Γ ⊢ᴰ exp.true _ ∷ ty.of ty.bool
  | tpb_false :
    Δ ∣ Γ ⊢ᴰ exp.false _ ∷ ty.of ty.bool
  | tpb_ifte σ e1 e2 e3 :
    Δ ∣ Γ ⊢ᴰ e1 ∷ ty.of ty.bool ->
    Δ ∣ Γ ⊢ᴰ e2 ∷ σ ->
    Δ ∣ Γ ⊢ᴰ e3 ∷ σ ->
    Δ ∣ Γ ⊢ᴰ exp.ifte e1 e2 e3 ∷ σ

  | tpb_absu x t1 t2 e :
    Δ ∣ cons (x,ty.of t1) Γ ⊢ᴰ e ∷ ty.of t2 ->
    Δ ∣ Γ ⊢ᴰ exp.absu x e ∷ ty.of (ty.func t1 t2)
  | tpb_abst x t1 t2 e :
    Δ ∣ cons (x,ty.of t1) Γ ⊢ᴰ e ∷ ty.of t2 ->
    Δ ∣ Γ ⊢ᴰ exp.abst x t1 e ∷ ty.of (ty.func t1 t2)
  | tpb_app t1 t2 e1 e2 :
    Δ ∣ Γ ⊢ᴰ e1 ∷ ty.of (ty.func t1 t2) ->
    Δ ∣ Γ ⊢ᴰ e2 ∷ ty.of t1 ->
    Δ ∣ Γ ⊢ᴰ exp.app e1 e2 ∷ ty.of t2

  | tpb_letp x (σ1 : Poly Δ) σ2 e1 e2 :
    (* This rule is just broken. *)
    _ ∣ Γ[injl] ⊢ᴰ e1 ∷ σ1[injl] ->
    Δ ∣ cons (x,σ1) Γ ⊢ᴰ e2 ∷ σ2 ->
    Δ ∣ Γ ⊢ᴰ exp.letp x σ1 e1 e2 ∷ σ2

  | tpb_inst e (σ : Poly Δ) (t : Mono Δ) :
    Δ ∣ Γ ⊢ᴰ e ∷ σ ->
    is_instance σ t ->
    Δ ∣ Γ ⊢ᴰ e ∷ ty.of t

  | tpb_gen Δ' e t :
    ctx.cat Δ Δ' ∣ Γ[injl] ⊢ᴰ e[injl] ∷ ty.of t ->
    Δ ∣ Γ ⊢ᴰ e ∷ @ty.poly Δ Δ' t

  where "Δ ∣ Γ ⊢ᴰ e ∷ σ" := (@decl Δ Γ e σ).

  Inductive algo {Δ} (Γ : Env Δ) : Exp Δ -> Mono Δ -> Prop :=

  | algo_var x σ t :
    resolve x Γ = Some σ ->
    is_instance σ t ->
    Δ ∣ Γ ⊢ᴬ exp.var _ x ∷ t

  | algo_true :
    Δ ∣ Γ ⊢ᴬ exp.true _ ∷ ty.bool
  | algo_false :
    Δ ∣ Γ ⊢ᴬ exp.false _ ∷ ty.bool
  | algo_ifte τ e1 e2 e3 :
    Δ ∣ Γ ⊢ᴬ e1 ∷ ty.bool ->
    Δ ∣ Γ ⊢ᴬ e2 ∷ τ ->
    Δ ∣ Γ ⊢ᴬ e3 ∷ τ ->
    Δ ∣ Γ ⊢ᴬ exp.ifte e1 e2 e3 ∷ τ

  | algo_absu x t1 t2 e :
    Δ ∣ cons (x,ty.of t1) Γ ⊢ᴬ e ∷ t2 ->
    Δ ∣ Γ ⊢ᴬ exp.absu x e ∷ ty.func t1 t2
  | algo_abst x t1 t2 e :
    Δ ∣ cons (x,ty.of t1) Γ ⊢ᴬ e ∷ t2 ->
    Δ ∣ Γ ⊢ᴬ exp.abst x t1 e ∷ ty.func t1 t2
  | algo_app t1 t2 e1 e2 :
    Δ ∣ Γ ⊢ᴬ e1 ∷ ty.func t1 t2 ->
    Δ ∣ Γ ⊢ᴬ e2 ∷ t1 ->
    Δ ∣ Γ ⊢ᴬ exp.app e1 e2 ∷ t2

  | algo_letp x σ1 (τ2 : Mono Δ) e1 e2 :
    ctx.cat Δ (ty.vars σ1) ∣ Γ[injl] ⊢ᴬ e1 ∷ ty.to σ1 ->
    Δ ∣ cons (x,σ1) Γ ⊢ᴬ e2 ∷ τ2 ->
    Δ ∣ Γ ⊢ᴬ exp.letp x σ1 e1 e2 ∷ τ2

  where "Δ ∣ Γ ⊢ᴬ e ∷ t" := (@algo Δ Γ e t).

  Module Equivalence.

    Lemma soundness Δ Γ e t :
      @algo Δ Γ e t -> @decl Δ Γ e (ty.of t).
    Proof.
      intros T. induction T; cbn.
      - eapply tpb_inst. constructor; eauto. auto.
      - constructor.
      - constructor.
      - constructor; auto.
      - constructor; auto.
      - constructor; auto.
      - econstructor; eauto.
      - admit.
    Admitted.

    Lemma completeness Δ Γ e σ :
      @decl Δ Γ e σ ->
      exists αs t,
        @algo
          (ctx.cat Δ αs)
          Γ[injl] e[injl] t /\ sub (@ty.poly Δ αs t) σ.
    Proof.
      intros T. induction T; cbn.
      - destruct σ as [αs τσ]. exists αs. exists τσ. split.
        + econstructor.  Unshelve.
          3: {
            exists αs. apply (subst τσ). apply (up Sub.injl).
          }
          admit.
          unfold is_instance. cbn.
          exists Sub.injr.
          unfold up.
          etransitivity; [|apply subst_refl].
          f_equal.
          admit.
        + unfold sub. exists injr. admit.
      - exists ctx.nil. exists ty.bool. cbn. split.
        + constructor.
        + unfold sub. exists env.nil. cbn. reflexivity.
      - exists ctx.nil. exists ty.bool. cbn. split.
        + constructor.
        + unfold sub. exists env.nil. cbn. reflexivity.
    Admitted.

  End Equivalence.

  Module ShallowConstraintsOnly.

    Inductive Constraint (Δ : TVarCtx) : Type :=
    | Tru
    | Fls
    | Eq (t1 t2 : Mono Δ)
    | And (c1 c2 : Constraint Δ)
    | Ex (c : Mono Δ -> Constraint Δ)
    | All {b} (c : Constraint (ctx.snoc Δ b)).
    #[global] Arguments Tru {Δ}.
    #[global] Arguments Fls {Δ}.

    Fixpoint denote {Δ} (c : Constraint Δ) : Prop :=
      match c with
      | Tru       => True
      | Fls       => False
      | Eq t1 t2  => t1 = t2
      | And c1 c2 => denote c1 /\ denote c2
      | Ex f      => exists t : Mono Δ, denote (f t)
      | All c     => denote c
      end.

    Fixpoint assume {Δ} (c : Constraint Δ) (P : Prop) : Prop :=
      match c with
      | Tru       => P
      | Fls       => True
      | Eq t1 t2  => t1 = t2 -> P
      | And c1 c2 => assume c1 (assume c2 P)
      | Ex f      => forall t : Mono Δ, assume (f t) P
      | All c     => assume c P
      end.

    Lemma denote_assume {Δ} (c : Constraint Δ) :
      forall P : Prop, (denote c -> P) <-> assume c P.
    Proof.
      induction c; cbn.
      - intuition.
      - intuition.
      - intuition.
      - firstorder.
      - firstorder.
      - auto.
    Qed.

    Notation "C1 ∧ C2" := (And C1 C2).
    Notation "t1 ≡ t2" := (Eq t1 t2) (at level 80).
    Notation "∃ x , C" := (Ex (fun x => C)) (at level 80, x binder, right associativity, format "∃ x ,  C").
    (* Notation "∀ x , C" := (All (fun x => C)) (at level 80, x binder, right associativity, format "∀ x ,  C"). *)

    Fixpoint existentials {Δ0} Δ : (Sub Δ Δ0 -> Constraint Δ0) -> Constraint Δ0 :=
      match Δ with
      | ctx.nil      => fun P => P env.nil
      | ctx.snoc w b => fun P => existentials (fun θ => ∃t, P (env.snoc θ b t))
      end.
    #[global] Arguments existentials {Δ0} Δ _.

    Lemma denote_existentials (Δ0 Δ : TVarCtx) (P : Sub Δ Δ0 -> Constraint Δ0) :
      denote (@existentials Δ0 Δ P) <-> exists θ : Sub Δ Δ0, denote (P θ).
    Proof.
      induction Δ; cbn.
      - split; intros H.
        + exists env.nil. apply H.
        + destruct H as [θ H]. now destruct (env.view θ).
      - rewrite IHΔ. clear IHΔ. cbn. firstorder.
        destruct (env.view x). firstorder.
    Qed.

    Fixpoint universal {Δ0} Δ : Constraint (ctx.cat Δ0 Δ) -> Constraint Δ0 :=
      match Δ with
      | ctx.nil      => fun c => c
      | ctx.snoc Δ b => fun c => universal Δ (All c)
      end.

    Lemma denote_universals (Δ0 Δ : TVarCtx) (c : Constraint (ctx.cat Δ0 Δ)) :
      denote (universal Δ c) <->
      denote c.
    Proof.
      induction Δ; cbn.
      - reflexivity.
      - apply IHΔ.
    Qed.

    Definition gen_is_instance {Δ} (σ : Poly Δ) (t : Mono Δ) : Constraint Δ :=
       existentials (ty.vars σ) (fun θ => (ty.to σ)[env.cat refl θ] ≡ t).

    Fixpoint check {Δ} (G : Env Δ) (e : Exp Δ) (t : Mono Δ) : Constraint Δ :=
      match e with
      | exp.var _ x =>
          match resolve x G with
          | Some σ => gen_is_instance σ t
          | None   => Fls
          end
      | exp.true _  => ty.bool ≡ t
      | exp.false _ => ty.bool ≡ t
      | exp.ifte e1 e2 e3 =>
          check G e1 ty.bool ∧
          check G e2 t ∧
          check G e3 t
      | exp.absu x e =>
          ∃t1, ∃t2,
            (ty.func t1 t2 ≡ t) ∧
            check (cons (x, ty.of t1) G) e t2
      | exp.abst x t1 e =>
          ∃t2,
            (ty.func t1 t2 ≡ t) ∧
            check (cons (x, ty.of t1) G) e t2
      | exp.app e1 e2 =>
          ∃t1,
            check G e1 (ty.func t1 t) ∧
            check G e2 t1
      | exp.letp x σ e1 e2 =>
          universal
            (ty.vars σ)
            (check G[injl] e1 (ty.to σ)) ∧
          check (cons (x, σ) G) e2 t
      end.

    Lemma complete Δ G e t :
      @algo Δ G e t -> denote (check G e t).
    Proof.
      intros T; induction T; cbn.
      - rewrite H. clear H. destruct H0 as [θ].
        unfold gen_is_instance in *.
        rewrite denote_existentials. cbn.
        now exists θ.
      - constructor.
      - constructor.
      - auto.
      - exists t1, t2. auto.
      - exists t2. auto.
      - exists t1. auto.
      - split.
        + rewrite denote_universals. apply IHT1.
        + apply IHT2.
    Qed.

    Lemma sound Δ G e t :
      denote (check G e t) -> @algo Δ G e t.
    Proof.
      revert G t. induction e; cbn; intros * HT; intros; subst.
      - destruct (resolve x G) as [σ|] eqn:?; cbn in HT.
        + unfold gen_is_instance in HT.
          rewrite denote_existentials in HT.
          destruct HT as [θ HT]. cbn in HT.
          econstructor. eauto.
          firstorder.
        + contradiction.
      - constructor.
      - constructor.
      - destruct HT as (HT1 & HT2 & HT3). constructor; auto.
      - destruct HT as (t1 & t2 & Heq & HT); subst.
        constructor; eauto.
      - destruct HT as (t2 & Heq & HT); subst.
        constructor; eauto.
      - destruct HT as (t1 & HT1 & HT2); subst.
        econstructor; eauto.
      - destruct HT as (HT1 & HT2).
        rewrite denote_universals in HT1.
        econstructor; eauto.
    Qed.

  End ShallowConstraintsOnly.

  Module ShallowConstraintsStuff.

    Definition CtxMod (Δe : TVarCtx) (A : TVarCtx -> Type) : TVarCtx -> Type :=
      fun Δ => A (ctx.cat Δ Δe).

    Inductive Constraint (A : TVarCtx -> Type) (Δ : TVarCtx) : Type :=
    | Ret (a : A Δ)
    | Fls
    | Eq (t1 t2 : Mono Δ) (k : Constraint A Δ)
    | Ex (c : Mono Δ -> Constraint A Δ)
    | And {B} Δ'
        (c1 : Constraint B (ctx.cat Δ Δ'))
        (c2 : B (ctx.cat Δ Δ') -> Constraint A Δ).
    #[global] Arguments Ret {A Δ} a.
    #[global] Arguments Fls {A Δ}.
    #[global] Arguments And {A} [Δ] {B} Δ'.

    Definition universals {A Δ} Δ' (c : Constraint A (ctx.cat Δ Δ')) :
        Constraint (CtxMod Δ' A) Δ :=
      And Δ' c Ret.

    Fixpoint bind {A B Δ} (c : Constraint A Δ)
      (f : A Δ -> Constraint B Δ) {struct c} : Constraint B Δ :=
      match c with
      | Ret a        => f a
      | Fls          => Fls
      | Eq t1 t2 k   => Eq t1 t2 (bind k f)
      | Ex c         => Ex (fun t => bind (c t) f)
      | And Δ' c1 c2 => And Δ' c1 (fun t => bind (c2 t) f)
      end.

    (* Definition Box (A : TVarCtx -> Type) : TVarCtx -> Type := *)
    (*   fun Δ => forall Δ', A (ctx.cat Δ Δ'). *)

    Fixpoint wp {A Δ} (c : Constraint A Δ) (P : A Δ -> Prop) {struct c} : Prop :=
      match c with
      | Ret a        => P a
      | Fls          => False
      | Eq t1 t2 k   => t1 = t2 /\ wp k P
      | Ex c0        => exists t : Mono Δ, wp (c0 t) P
      | And Δ' c1 c2 => wp c1 (fun l => wp (c2 l) P)
      end.

    Fixpoint wlp {A Δ} (c : Constraint A Δ) (P : A Δ -> Prop) {struct c} : Prop :=
      match c with
      | Ret a        => P a
      | Fls          => True
      | Eq t1 t2 k   => t1 = t2 -> wlp k P
      | Ex c0        => forall t : Mono Δ, wlp (c0 t) P
      | And Δ' c1 c2 => wlp c1 (fun l => wlp (c2 l) P)
      end.

    #[export] Instance proper_wp_impl {A Δ} :
      Proper (pointwise_relation (Constraint A Δ) (pointwise_relation (A Δ) Basics.impl ==> Basics.impl)) (@wp A Δ).
    Proof.
      unfold Proper, pointwise_relation, respectful.
      intros c P Q PQ. induction c; cbn.
      - apply PQ.
      - reflexivity.
      - apply Morphisms_Prop.and_impl_morphism; intuition.
      - apply Morphisms_Prop.ex_impl_morphism.
        intros t. now apply H.
      - apply IHc. intros. now apply H.
    Qed.

    #[export] Instance proper_wp_iff {A Δ} :
      Proper (pointwise_relation (Constraint A Δ) (pointwise_relation (A Δ) iff ==> iff)) (@wp A Δ).
    Proof.
      unfold Proper, pointwise_relation, respectful. intros c P Q PQ.
      split; apply proper_wp_impl; intros a ?; now apply (PQ a).
    Qed.

    #[export] Instance proper_wlp_impl {A Δ} :
      Proper (pointwise_relation (Constraint A Δ) (pointwise_relation (A Δ) Basics.impl ==> Basics.impl)) (@wlp A Δ).
    Proof.
      unfold Proper, pointwise_relation, respectful.
      intros c P Q PQ. induction c; cbn; firstorder.
    Qed.

    #[export] Instance proper_wlp_iff {A Δ} :
      Proper (pointwise_relation (Constraint A Δ) (pointwise_relation (A Δ) iff ==> iff)) (@wlp A Δ).
    Proof.
      unfold Proper, pointwise_relation, respectful. intros c P Q PQ.
      split; apply proper_wlp_impl; intros a ?; now apply (PQ a).
    Qed.

    Lemma wp_impl_wlp {A Δ} (c : Constraint A Δ) (P : A Δ -> Prop) (Q : Prop) :
      (wp c P -> Q) <-> wlp c (fun a => P a -> Q).
    Proof.
      revert P Q.
      induction c; cbn.
      - intuition.
      - intuition.
      - firstorder.
      - firstorder.
        apply H. apply H0.
      - intros. rewrite IHc.
        apply proper_wlp_iff.
        intros b. apply H.
    Qed.

    Lemma wp_bind {A B Δ} (c : Constraint A Δ) (f : A Δ -> Constraint B Δ) (P : B Δ -> Prop) :
      wp (bind c f) P <-> wp c (fun a => wp (f a) P).
    Proof.
      induction c; cbn.
      - auto.
      - auto.
      - now apply Morphisms_Prop.and_iff_morphism.
      - now apply Morphisms_Prop.ex_iff_morphism.
      - now apply proper_wp_iff.
    Qed.

    Lemma wlp_bind {A B Δ} (c : Constraint A Δ) (f : A Δ -> Constraint B Δ) (P : B Δ -> Prop) :
      wlp (bind c f) P <-> wlp c (fun a => wlp (f a) P).
    Proof.
      induction c; cbn.
      - auto.
      - auto.
      - now apply Morphisms_Prop.iff_iff_iff_impl_morphism.
      - now apply Morphisms_Prop.all_iff_morphism.
      - now apply proper_wlp_iff.
    Qed.

    (* Notation "C1 ∧ C2" := (And C1 C2). *)
    (* Notation "t1 ≡ t2" := (Eq t1 t2) (at level 80). *)
    Notation "∃ x , C" := (Ex (fun x => C)) (at level 80, x binder, right associativity, format "∃ x ,  C").
    (* Notation "∀ x , C" := (All (fun x => C)) (at level 80, x binder, right associativity, format "∀ x ,  C"). *)

    Fixpoint existentials {A Δ0} Δ : (Sub Δ Δ0 -> Constraint A Δ0) -> Constraint A Δ0 :=
      match Δ with
      | ctx.nil      => fun k => k env.nil
      | ctx.snoc w b => fun k => existentials (fun θ => ∃t, k (env.snoc θ b t))
      end.
    #[global] Arguments existentials {A Δ0} Δ _.

    Lemma wp_existentials {A} (Δ0 Δ : TVarCtx) (k : Sub Δ Δ0 -> Constraint A Δ0) (P : A Δ0 -> Prop) :
      wp (@existentials A Δ0 Δ k) P <-> exists θ : Sub Δ Δ0, wp (k θ) P.
    Proof.
      induction Δ; cbn.
      - split; intros H.
        + exists env.nil. apply H.
        + destruct H as [θ H]. now destruct (env.view θ).
      - rewrite IHΔ. clear IHΔ. cbn. firstorder.
        destruct (env.view x). firstorder.
    Qed.

    Lemma wlp_existentials {A} (Δ0 Δ : TVarCtx) (k : Sub Δ Δ0 -> Constraint A Δ0) (P : A Δ0 -> Prop) :
      wlp (@existentials A Δ0 Δ k) P <-> forall θ : Sub Δ Δ0, wlp (k θ) P.
    Proof.
      induction Δ; cbn.
      - split; intros H.
        + intros θ. now destruct (env.view θ).
        + now apply H.
      - rewrite IHΔ. clear IHΔ. cbn. firstorder.
        destruct (env.view θ). firstorder.
    Qed.

    Definition Unit (Δ : TVarCtx) : Type := unit.

    Definition gen_is_instance {Δ} (σ : Poly Δ) (t : Mono Δ) : Constraint Unit Δ :=
       existentials (ty.vars σ) (fun θ => Eq (ty.to σ)[env.cat refl θ] t (Ret tt)).

    Fixpoint check {Δ} (G : Env Δ) (e : Exp Δ) (t : Mono Δ) : Constraint Unit Δ :=
      match e with
      | exp.var _ x =>
          match resolve x G with
          | Some σ => gen_is_instance σ t
          | None   => Fls
          end
      | exp.true _  => Eq ty.bool t (Ret tt)
      | exp.false _ => Eq ty.bool t (Ret tt)
      | exp.ifte e1 e2 e3 =>
          bind (check G e1 ty.bool) (fun _ =>
          bind (check G e2 t) (fun _ =>
          bind (check G e3 t) (fun _ =>
          Ret tt)))
      | exp.absu x e =>
          ∃t1, ∃t2,
            Eq (ty.func t1 t2) t
              (check (cons (x, ty.of t1)G) e t2)
      | exp.abst x t1 e =>
          ∃t2,
            Eq (ty.func t1 t2) t
              (check (cons (x, ty.of t1)G) e t2)
      | exp.app e1 e2 =>
          ∃t1,
            bind (check G e1 (ty.func t1 t)) (fun _ =>
            check G e2 t1)
      | exp.letp x σ e1 e2 =>
          And (ty.vars σ)
            (check G[injl] e1 (ty.to σ))
            (fun _ => check (cons (x,σ) G) e2 t)
      end.

    Lemma complete_check Δ G e t :
      @algo Δ G e t -> wp (check G e t) (fun _ => True).
    Proof.
      intros T; induction T; cbn.
      - rewrite H. clear H. destruct H0 as [θ].
        unfold gen_is_instance in *.
        rewrite wp_existentials. cbn.
        now exists θ.
      - auto.
      - auto.
      - rewrite wp_bind. revert IHT1. apply proper_wp_impl. intros _ _.
        rewrite wp_bind. revert IHT2. apply proper_wp_impl. intros _ _.
        rewrite wp_bind. apply IHT3.
      - exists t1, t2. split. reflexivity. apply IHT.
      - exists t2. split. reflexivity. apply IHT.
      - exists t1.
        rewrite wp_bind. revert IHT1. apply proper_wp_impl. intros _ _.
        apply IHT2.
      - revert IHT1. apply proper_wp_impl. intros _ _. apply IHT2.
    Qed.

    Lemma sound_check Δ G e t :
      wp (check G e t) (fun _ => True) -> @algo Δ G e t.
    Proof.
      apply wp_impl_wlp. revert G t.
      induction e; cbn; intros *; intros; subst.
      - destruct (resolve x G) as [σ|] eqn:?.
        + unfold gen_is_instance.
          apply wp_impl_wlp. rewrite wp_existentials. cbn.
          intros (θ & Hwp & _). subst. econstructor. apply Heqo.
          exists θ. reflexivity.
        + constructor.
      - constructor.
      - constructor.
      - rewrite wlp_bind. generalize (IHe1 G ty.bool). clear IHe1.
        apply proper_wlp_impl. intros _ H1.
        rewrite wlp_bind. generalize (IHe2 G t). clear IHe2.
        apply proper_wlp_impl. intros _ H2.
        rewrite wlp_bind. generalize (IHe3 G t). clear IHe3.
        apply proper_wlp_impl. intros _ H3.
        cbn. intros _. constructor; auto.
      - generalize (IHe (cons (x,ty.of t0) G) t1). clear IHe.
        apply proper_wlp_impl. intros _ H1.
        cbn. intros _. constructor; auto.
      - generalize (IHe (cons (x,ty.of t) G) t1). clear IHe.
        apply proper_wlp_impl. intros _ H1.
        cbn. intros _. constructor; auto.
      - rewrite wlp_bind. generalize (IHe1 G (ty.func t0 t)). clear IHe1.
        apply proper_wlp_impl. intros _ H1.
        generalize (IHe2 G t0). clear IHe2.
        apply proper_wlp_impl. intros _ H2.
        cbn. intros _. econstructor; auto.
      - generalize (IHe1 G[injl] (ty.to σ)). clear IHe1.
        apply proper_wlp_impl. intros _ H1.
        generalize (IHe2 (cons (x,σ) G) t). clear IHe2.
        apply proper_wlp_impl. intros _ H2.
        cbn. intros _. econstructor; auto.
    Qed.

    Definition assert_sub {Δ} (σ1 σ2 : Poly Δ) : Constraint Unit Δ :=
      And (B := Unit) (ty.vars σ2)
        (existentials (ty.vars σ1)
           (fun θ => Eq (ty.to σ1)[env.cat injl θ] (ty.to σ2) (Ret tt)))
        (fun x : unit => Ret x).

    Definition assert_sub' {Δ} (σ1 σ2 : Poly Δ) : Constraint Unit Δ :=
      universals (A := Unit) (ty.vars σ2)
        (existentials (ty.vars σ1)
           (fun θ => Eq (ty.to σ1)[env.cat injl θ] (ty.to σ2) (Ret tt))).

    Definition choose_instance {Δ} (σ : Poly Δ) : Constraint Mono Δ :=
      existentials (ty.vars σ) (fun θ => Ret (ty.to σ)[env.cat refl θ]).

    Fixpoint synth {Δ} (G : Env Δ) (e : Exp Δ) : Constraint Mono Δ :=
      match e with
      | exp.var _ x =>
          match resolve x G with
          | Some σ => choose_instance σ
          | None   => Fls
          end
      | exp.true _  => Ret ty.bool
      | exp.false _ => Ret ty.bool
      | exp.ifte e1 e2 e3 =>
          bind (synth G e1) (fun t1 =>
          bind (synth G e2) (fun t2 =>
          bind (synth G e3) (fun t3 =>
          Eq t1 ty.bool (Eq t2 t3 (Ret t2)))))
      | exp.absu x e =>
          ∃t1,
            bind (synth (cons (x, ty.of t1) G) e) (fun t2 =>
            Ret (ty.func t1 t2))
      | exp.abst x t1 e =>
          bind (synth (cons (x, ty.of t1) G) e) (fun t2 =>
          Ret (ty.func t1 t2))
      | exp.app e1 e2 =>
          bind (synth G e1) (fun tf =>
          bind (synth G e2) (fun t1 =>
          ∃t2, Eq (ty.func t1 t2) tf (Ret t2)))
      | exp.letp x σ e1 e2 =>
          And (ty.vars σ)
            (bind (synth G[injl] e1) (fun t1 =>
             Eq t1 (ty.to σ) (Ret (A := Unit) tt)))
            (fun _ => synth (cons (x,σ) G) e2)
      end.

    Lemma complete_synth Δ G e t :
      @algo Δ G e t -> wp (synth G e) (fun t' => t' = t).
    Proof.
      intros T; induction T; cbn.
      - rewrite H. unfold choose_instance.
        rewrite wp_existentials. cbn. exact H0.
      - auto.
      - auto.
      - rewrite wp_bind. revert IHT1. apply proper_wp_impl. intros t1 Heq1.
        rewrite wp_bind. revert IHT2. apply proper_wp_impl. intros t2 Heq2.
        rewrite wp_bind. revert IHT3. apply proper_wp_impl. intros t3 Heq3.
        cbn. subst. auto.
      - exists t1. rewrite wp_bind. revert IHT. apply proper_wp_impl.
        intros t2' Heq. subst t2'. cbn. reflexivity.
      - rewrite wp_bind. revert IHT. apply proper_wp_impl.
        intros t2' Heq. subst t2'. cbn. reflexivity.
      - rewrite wp_bind. revert IHT1. apply proper_wp_impl. intros tf Heq1.
        rewrite wp_bind. revert IHT2. apply proper_wp_impl. intros t1' Heq2.
        subst t1'. cbn. exists t2. auto.
      - rewrite wp_bind. revert IHT1. apply proper_wp_impl. intros t1 Heq1. cbn.
        split. auto. apply IHT2.
    Qed.

    Lemma sound_synth Δ G e :
      wlp (synth G e) (fun t => Δ ∣ G ⊢ᴬ e ∷ t).
    Proof.
      induction e; cbn; intros *; intros; subst.
      - destruct (resolve x G) as [σ|] eqn:?.
        + unfold choose_instance.
          rewrite wlp_existentials.
          intros θ. cbn. econstructor; eauto.
          now exists θ.
        + constructor.
      - constructor.
      - constructor.
      - rewrite wlp_bind. generalize (IHe1 G). clear IHe1.
        apply proper_wlp_impl. intros t1 IH1.
        rewrite wlp_bind. generalize (IHe2 G). clear IHe2.
        apply proper_wlp_impl. intros t2 IH2.
        rewrite wlp_bind. generalize (IHe3 G). clear IHe3.
        apply proper_wlp_impl. intros t3 IH3.
        cbn. intros Heq1 Heq2. subst. constructor; auto.
      - rewrite wlp_bind. generalize (IHe (cons (x,ty.of t) G)).
        apply proper_wlp_impl. intros t2 H1. cbn.
        constructor; auto.
      - rewrite wlp_bind. generalize (IHe (cons (x,ty.of t) G)).
        apply proper_wlp_impl. intros t2 H1. cbn.
        constructor; auto.
      - rewrite wlp_bind.
        generalize (IHe1 G). clear IHe1.
        apply proper_wlp_impl. intros tf H1.
        rewrite wlp_bind.
        generalize (IHe2 G). clear IHe2.
        apply proper_wlp_impl. intros t1 H2.
        cbn. intros t2 Heq. subst. econstructor; eauto.
      - rewrite wlp_bind.
        generalize (IHe1 G[injl]).
        apply proper_wlp_impl. intros t1 H1 Heq. cbn.
        generalize (IHe2 (cons (x,σ) G)).
        apply proper_wlp_impl. intros t2 H2.
        subst. econstructor; eauto.
    Qed.

  End ShallowConstraintsStuff.

End JustTyping.


Module Elaboration.

(*   Reserved Notation "G ⊢ᵗ E ∷ T ↝ E'" (at level 90). *)

(*   Inductive tpb (G : Env) : Exp -> Ty -> Exp -> Prop := *)
(*   | tpb_var x σ t : *)
(*     resolve x G = Some σ -> *)
(*     denote σ t -> *)
(*     G ⊢ᵗ exp.var x ∷ t ↝ exp.var x *)
(*   | tpb_true : *)
(*     G ⊢ᵗ exp.true ∷ ty.bool ↝ exp.true *)
(*   | tpb_false : *)
(*     G ⊢ᵗ exp.false ∷ ty.bool ↝ exp.false *)
(*   | tpb_ifte t e1 e1' e2 e2' e3 e3' : *)
(*     G ⊢ᵗ e1 ∷ ty.bool ↝ e1' -> *)
(*     G ⊢ᵗ e2 ∷ t ↝ e2' -> *)
(*     G ⊢ᵗ e3 ∷ t ↝ e3' -> *)
(*     G ⊢ᵗ exp.ifte e1 e2 e3 ∷ t ↝ exp.ifte e1' e2' e3' *)
(*   | tpb_absu x t1 t2 e e' : *)
(*     cons (x,mono2poly t1) G ⊢ᵗ e ∷ t2 ↝ e' -> *)
(*     G ⊢ᵗ exp.absu x e ∷ ty.func t1 t2 ↝ exp.abst x t1 e' *)
(*   | tpb_abst x t1 t2 e e' : *)
(*     cons (x,mono2poly t1) G ⊢ᵗ e ∷ t2 ↝ e' -> *)
(*     G ⊢ᵗ exp.abst x t1 e ∷ ty.func t1 t2 ↝ exp.abst x t1 e' *)
(*   | tpb_app t1 t2 e1 e1' e2 e2' : *)
(*     G ⊢ᵗ e1 ∷ ty.func t1 t2 ↝ e1' -> *)
(*     G ⊢ᵗ e2 ∷ t1 ↝ e2' -> *)
(*     G ⊢ᵗ exp.app e1 e2 ∷ t2 ↝ exp.app e1' e2' *)
(*   | tpb_letp x σ1 t2 e1 e1' e2 e2' : *)
(*     (forall ι : Assignment (vars σ1), G ⊢ᵗ e1 ∷ mono σ1 ι ↝ e1') -> *)
(*     cons (x,σ1) G ⊢ᵗ e2 ∷ t2 ↝ e2' -> *)
(*     G ⊢ᵗ exp.letp x σ1 e1 e2 ∷ t2 ↝ exp.letp x σ1 e1' e2' *)

(*   where "G ⊢ᵗ e ∷ t ↝ e'" := (tpb G e t e'). *)

End Elaboration.

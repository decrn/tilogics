(******************************************************************************)
(* Copyright (c) 2020 Steven Keuchel, Dominique Devriese                      *)
(* All rights reserved.                                                       *)
(*                                                                            *)
(* Redistribution and use in source and binary forms, with or without         *)
(* modification, are permitted provided that the following conditions are     *)
(* met:                                                                       *)
(*                                                                            *)
(* 1. Redistributions of source code must retain the above copyright notice,  *)
(*    this list of conditions and the following disclaimer.                   *)
(*                                                                            *)
(* 2. Redistributions in binary form must reproduce the above copyright       *)
(*    notice, this list of conditions and the following disclaimer in the     *)
(*    documentation and/or other materials provided with the distribution.    *)
(*                                                                            *)
(* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS        *)
(* "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED  *)
(* TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR *)
(* PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR          *)
(* CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,      *)
(* EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,        *)
(* PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR         *)
(* PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF     *)
(* LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING       *)
(* NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS         *)
(* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.               *)
(******************************************************************************)

From Coq Require Export
     Numbers.BinNums.
From Coq Require Import
     Bool.Bool
     Lists.List
     Strings.String
     ZArith.BinInt.

From Equations Require Import
     Equations.

From stdpp Require base.

#[local] Set Implicit Arguments.
#[local] Set Transparent Obligations.

(* Equality *)

Definition f_equal_dec {A B : Type} (f : A -> B) {x y : A} (inj : f x = f y -> x = y)
           (hyp : dec_eq x y) : dec_eq (f x) (f y) :=
  match hyp with
  | left p => left (f_equal f p)
  | right p => right (fun e : f x = f y => p (inj e))
  end.

Definition f_equal2_dec {A1 A2 B : Type} (f : A1 -> A2 -> B) {x1 y1 : A1} {x2 y2 : A2}
           (inj : f x1 x2 = f y1 y2 -> @sigmaI _ _ x1 x2 = @sigmaI _ _ y1 y2)
           (hyp1 : dec_eq x1 y1) (hyp2 : dec_eq x2 y2) :
  dec_eq (f x1 x2) (f y1 y2) :=
  match hyp1 , hyp2 with
  | left  p , left q  => left (eq_trans
                                 (f_equal (f x1) q)
                                 (f_equal (fun x => f x y2) p))
  | left  p , right q =>
    right (fun e => q (f_equal (@pr2 _ (fun _ => _)) (inj e)))
  | right p , _       =>
    right (fun e => p (f_equal (@pr1 _ (fun _ => _)) (inj e)))
  end.

#[global] Instance Z_eqdec : EqDec Z := Z.eq_dec.
#[global] Instance string_eqdec : EqDec string := string_dec.
#[global] Instance option_eqdec {A} {eqdA : EqDec A} : EqDec (option A).
Proof. eqdec_proof. Defined.

Definition eq_dec_het {I} {A : I -> Type} `{eqdec : EqDec (sigT A)}
  {i1 i2} (x1 : A i1) (x2 : A i2) : dec_eq (existT i1 x1) (existT i2 x2) :=
  eq_dec (existT i1 x1) (existT i2 x2).
Derive NoConfusion EqDec for Empty_set.

Definition IsSome {A : Type} (m : option A) : Type :=
  match m with
  | Some _ => unit
  | None   => Empty_set
  end.

Definition fromSome {A : Type} (m : option A) : IsSome m -> A :=
  match m return IsSome m -> A with
  | Some a => fun _ => a
  | None   => fun p => match p with end
  end.

Module option.

  Definition isSome {A} (m : option A) : bool :=
    match m with Some _ => true | None => false end.
  Definition isNone {A} (m : option A) : bool :=
    match m with Some _ => false | None => true end.

  Definition IsSome {A} (m : option A) : Prop :=
    Is_true (isSome m).

  Definition fromSome {A} (m : option A) : IsSome m -> A :=
    match m with Some a => fun _ => a | None => fun p => match p with end end.

  Definition map {A B} (f : A -> B) (o : option A) : option B :=
    match o with Some a => Some (f a) | None => None end.
  Definition bind {A B} (a : option A) (f : A -> option B) : option B :=
    match a with Some x => f x | None => None end.
  Definition comp {A B C : Type} (f : A -> option B) (g : B -> option C) :=
    fun a => bind (f a) g.

  Arguments map {A B} f !o.
  Arguments bind {A B} !a f.

  (* Easy eq patterns *)
  Lemma map_eq_some {A B} (f : A -> B) (o : option A) (a : A) :
    o = Some a ->
    map f o = Some (f a).
  Proof. now intros ->. Qed.

  Lemma bind_eq_some {A B} (f : A -> option B) (o : option A) (b : B) :
    (exists a, o = Some a /\ f a = Some b) <->
    bind o f = Some b.
  Proof.
    split.
    - now intros (a & -> & <-).
    - destruct o as [a|]; [ now exists a | discriminate ].
  Qed.

  Lemma map_bind {A B C} (f : B -> C) (g : A -> option B) (o : option A) :
    map f (bind o g) = bind o (fun a => map f (g a)).
  Proof. now destruct o. Qed.

  (* Not lazy in (a : option A). Avoid! *)
  Definition ap {A B} (f : option (A -> B)) (a : option A) : option B :=
    match f with
    | Some f => map f a
    | None => None
    end.

  Local Notation aplazy f a :=
    (match f with
     | Some g => map g a
     | None   => None
     end).

  (* Variant of Bool.reflect and BoolSpec for options, i.e.
     a weakest pre without effect observation. *)
  Inductive spec {A} (S : A -> Prop) (N : Prop) : option A -> Prop :=
  | specSome {a : A} : S a -> spec S N (Some a)
  | specNone         : N -> spec S N None.

  (* Total correctness weakest pre for option. Arguments are inversed. *)
  Inductive wp {A} (S : A -> Prop) : option A -> Prop :=
  | wpSome {a : A} : S a -> wp S (Some a).

  (* Partial correctness weakest pre for option. Arguments are inversed. *)
  Inductive wlp {A} (S : A -> Prop) : option A -> Prop :=
  | wlpSome {a : A} : S a -> wlp S (Some a)
  | wlpNone         : wlp S None.

  (* We define equivalent formulations using pattern matches and
     logical connectives plus constructors. *)
  Lemma spec_match {A S N} (o : option A) :
    spec S N o <-> match o with
                   | Some a => S a
                   | None   => N
                   end.
  Proof.
    split.
    - intros []; auto.
    - destruct o; now constructor.
  Qed.

  Lemma wp_match {A S} (o : option A) :
    wp S o <-> match o with
               | Some a => S a
               | None   => False
               end.
  Proof.
    split.
    - intros []; auto.
    - destruct o; [apply wpSome|contradiction].
  Qed.

  Lemma wp_exists {A} (Q : A -> Prop) (o : option A) :
    wp Q o <-> exists a, o = Some a /\ Q a.
  Proof.
    rewrite wp_match. split.
    - destruct o; eauto; contradiction.
    - now intros [a [-> HQ]].
  Qed.

  Lemma wlp_match {A S} (o : option A) :
    wlp S o <-> match o with
               | Some a => S a
               | None   => True
               end.
  Proof.
    split.
    - intros []; auto.
    - destruct o; auto using wlpSome, wlpNone.
  Qed.

  Lemma wlp_forall {A} (Q : A -> Prop) (o : option A) :
    wlp Q o <-> forall a, o = Some a -> Q a.
  Proof.
    rewrite wlp_match. split.
    - intros; subst; auto.
    - destruct o; auto.
  Qed.

  Section Bind.

    Context {A B} {S : B -> Prop} {N : Prop} (f : A -> option B) (o : option A).

    Local Ltac proof :=
      destruct o; now rewrite ?spec_match, ?wp_match, ?wlp_match.

    Lemma spec_bind : spec S N (bind o f) <-> spec (fun a => spec S N (f a)) N o.
    Proof. proof. Qed.
    Definition spec_bind_elim := proj1 spec_bind.
    Definition spec_bind_intro := proj2 spec_bind.

    Lemma wp_bind : wp S (bind o f) <-> wp (fun a => wp S (f a)) o.
    Proof. proof. Qed.
    Definition wp_bind_elim := proj1 wp_bind.
    Definition wp_bind_intro := proj2 wp_bind.

    Lemma wlp_bind : wlp S (bind o f) <-> wlp (fun a => wlp S (f a)) o.
    Proof. proof. Qed.

    Definition wlp_bind_elim := proj1 wlp_bind.
    Definition wlp_bind_intro := proj2 wlp_bind.

  End Bind.

  Lemma spec_map {A B S N} (f : A -> B) (o : option A) :
    spec S N (map f o) <-> spec (fun a => S (f a)) N o.
  Proof. do 2 rewrite spec_match; now destruct o. Qed.

  Lemma spec_ap {A B S N} (f : option (A -> B)) (o : option A) :
    spec S N (ap f o) <->
    spec (fun f => spec (fun a => S (f a)) N o) N f.
  Proof.
    do 2 rewrite spec_match. destruct f; try easy.
    rewrite spec_match; now destruct o.
  Qed.

  Lemma spec_aplazy {A B S N} (f : option (A -> B)) (o : option A) :
    spec S N (aplazy f o) <->
    spec (fun f => spec (fun a => S (f a)) N o) N f.
  Proof. apply spec_ap. Qed.

  Lemma spec_monotonic {A} (S1 S2 : A -> Prop) (N1 N2 : Prop)
    (fS : forall a, S1 a -> S2 a) (fN: N1 -> N2) :
    forall (o : option A),
      spec S1 N1 o -> spec S2 N2 o.
  Proof. intros ? []; constructor; auto. Qed.

  Lemma spec_proper {A} (S1 S2 : A -> Prop) (N1 N2 : Prop)
    (fS : forall a, S1 a <-> S2 a) (fN: N1 <-> N2) :
    forall (o : option A),
      spec S1 N1 o <-> spec S2 N2 o.
  Proof. split; apply spec_monotonic; firstorder. Qed.

  Lemma wp_map {A B S} (f : A -> B) (o : option A) :
    wp S (map f o) <-> wp (fun a => S (f a)) o.
  Proof. do 2 rewrite wp_match; now destruct o. Qed.

  Lemma wp_ap {A B S} (f : option (A -> B)) (o : option A) :
    wp S (ap f o) <->
    wp (fun f => wp (fun a => S (f a)) o) f.
  Proof.
    do 2 rewrite wp_match. destruct f; try easy.
    rewrite wp_match; now destruct o.
  Qed.

  Lemma wp_aplazy {A B S} (f : option (A -> B)) (o : option A) :
    wp S (aplazy f o) <->
    wp (fun f => wp (fun a => S (f a)) o) f.
  Proof. apply wp_ap. Qed.

  Lemma wp_monotonic {A} (S1 S2 : A -> Prop) (fS : forall a, S1 a -> S2 a)  :
    forall (o : option A), wp S1 o -> wp S2 o.
  Proof. intros ? []; constructor; auto. Qed.

  Lemma wp_proper {A} (S1 S2 : A -> Prop) (fS : forall a, S1 a <-> S2 a)  :
    forall (o : option A), wp S1 o <-> wp S2 o.
  Proof. split; apply wp_monotonic; firstorder. Qed.

  Lemma wlp_map {A B S} (f : A -> B) (o : option A) :
    wlp S (map f o) <-> wlp (fun a => S (f a)) o.
  Proof. do 2 rewrite wlp_match; now destruct o. Qed.

  Lemma wlp_ap {A B S} (f : option (A -> B)) (o : option A) :
    wlp S (ap f o) <->
    wlp (fun f => wlp (fun a => S (f a)) o) f.
  Proof.
    do 2 rewrite wlp_match. destruct f; try easy.
    rewrite wlp_match; now destruct o.
  Qed.

  Lemma wlp_aplazy {A B S} (f : option (A -> B)) (o : option A) :
    wlp S (aplazy f o) <->
    wlp (fun f => wlp (fun a => S (f a)) o) f.
  Proof. apply wlp_ap. Qed.

  Lemma wlp_monotonic {A} (S1 S2 : A -> Prop) (fS : forall a, S1 a -> S2 a)  :
    forall (o : option A), wlp S1 o -> wlp S2 o.
  Proof. intros ? []; constructor; auto. Qed.

  Lemma wlp_proper {A} (S1 S2 : A -> Prop) (fS : forall a, S1 a <-> S2 a)  :
    forall (o : option A), wlp S1 o <-> wlp S2 o.
  Proof. split; apply wlp_monotonic; firstorder. Qed.

  Module Import notations.

    Notation "' x <- ma ;; mb" :=
      (bind ma (fun x => mb))
        (at level 80, x pattern, ma at next level, mb at level 200, right associativity,
          format "' x  <-  ma  ;;  mb").
    Notation "x <- ma ;; mb" :=
      (bind ma (fun x => mb))
        (at level 80, ma at next level, mb at level 200, right associativity).
    Notation "f <$> a" := (map f a) (at level 61, left associativity).
    Notation "f <*> a" := (aplazy f a) (at level 61, left associativity).

  End notations.

  Module tactics.

    Ltac mixin :=
      lazymatch goal with
      | |- wp _ (Some _) => constructor
      | |- wp _ (map _ _) => apply wp_map
      | |- wp _ (bind _ _) => apply wp_bind_intro
      | |- wlp _ (Some _) => constructor
      | |- wlp _ (map _ _) => apply wlp_map
      | |- wlp _ (bind _ _) => apply wlp_bind_intro
      | |- spec _ _ (match _ with _ => _ end) => apply spec_aplazy
      | |- spec _ _ (map _ _) => apply spec_map
      | H: wp _ ?x |- wp _ ?x => revert H; apply wp_monotonic; intros
      | H: wlp _ ?x |- wlp _ ?x => revert H; apply wlp_monotonic; intros
      | H: spec _ _ ?x |- spec _ _ ?x => revert H; apply spec_monotonic; intros
      | |- wp _ ?x <-> wp _ ?x => apply wp_proper
      | |- wlp _ ?x <-> wlp _ ?x => apply wlp_proper
      | |- spec _ _ ?x <-> spec _ _ ?x => apply spec_proper
      | |- context[wp ?S (Some ?x)] => rewrite (@wp_match _ S (Some x))
      | |- context[wlp ?S (Some ?x)] => rewrite (@wlp_match _ S (Some x))
      | |- context[spec ?S ?N (Some ?x)] => rewrite (@spec_match _ S N (Some x))
      | |- context[wp ?S None] => rewrite (@wp_match _ S None)
      | |- context[wlp ?S None] => rewrite (@wlp_match _ S None)
      end.

  End tactics.

End option.

Lemma and_iff_compat_r' (A B C : Prop) :
  (B /\ A <-> C /\ A) <-> (A -> B <-> C).
Proof. intuition. Qed.

Lemma and_iff_compat_l' (A B C : Prop) :
  (A /\ B <-> A /\ C) <-> (A -> B <-> C).
Proof. intuition. Qed.

Lemma imp_iff_compat_l' (A B C : Prop) :
  ((A -> B) <-> (A -> C)) <-> (A -> B <-> C).
Proof. intuition. Qed.

Lemma rightid_and_true (A : Prop) :
  A /\ True <-> A.
Proof. intuition. Qed.

Lemma leftid_true_and (A : Prop) :
  True /\ A <-> A.
Proof. intuition. Qed.

Lemma exists_or_compat {A} (P Q : A -> Prop):
  (exists a, P a \/ Q a) <-> (exists a, P a) \/ (exists a, Q a).
Proof. firstorder. Qed.

Lemma forall_and_compat {A} (P Q : A -> Prop):
  (forall a, P a /\ Q a) <-> (forall a, P a) /\ (forall a, Q a).
Proof. firstorder. Qed.

(* Really short summary on notations in Coq:
   - Coq uses precedence levels from 0 to 100.
   - Lower levels bound tighter than higher levels.
   - A /\ B is at level 80, right assoc
   - A \/ B is at level 85, right assoc
   - x = y is at level 70
 *)

Reserved Infix "▻"                 (at level 61, left associativity).
Reserved Infix "▻▻"                (at level 61, left associativity).
(* stdpp defines this at level 70 *)
Reserved Infix "∈"                 (at level 70).

Reserved Notation "[ ]" (format "[ ]").
Reserved Notation "[ x ]".
Reserved Notation "[ x ; y ; .. ; z ]".

(* We use the character ↦ as an infix notation for points-to predicates in the
   case-studies. This should bind tighter than ∗ which is at level 80. Hence
   x in this notation has to bind at least tighter than that. Also it should
   allow for x being a typed binding (y ∷ t) which is at level 49, so looser
   than that. *)
Reserved Notation "δ ► ( x ↦ v )"  (at level 50, x at level 50, left associativity,
 format "δ  ►  ( x  ↦  v )").
Reserved Notation "δ1 ►► δ2"       (at level 50, left associativity).
Reserved Notation "δ ⟪ x ↦ v ⟫"    (at level 90, x at level 0, v at level 0, left associativity).
Reserved Notation "δ ‼ x"          (at level 56, no associativity).

Reserved Notation "⟨ γ1 , μ1 , δ1 , s1 ⟩ ---> ⟨ γ2 , μ2 , δ2 , s2 ⟩" (at level 75, no associativity).
Reserved Notation "⟨ γ1 , μ1 , δ1 , s1 ⟩ --->* ⟨ γ2 , μ2 , δ2 , s2 ⟩" (at level 75, no associativity).
(* Notation "( x , y , .. , z )" := *)
(*   (tuplepat_snoc .. (tuplepat_snoc (tuplepat_snoc tuplepat_nil x) y) .. z). *)

Reserved Notation "s1 ;; s2" (at level 100, s2 at level 200, right associativity,
  format "'[v' s1 ;; '/' s2 ']'").

Reserved Notation "⦃ P ⦄ s ; δ ⦃ Q ⦄" (at level 75, no associativity).

(* Logic notations. These were chosen to be compatible with Coq.Unicode.Utf8, stdpp and iris. *)
Reserved Notation "P ⊢ Q" (at level 99, Q at level 200, right associativity).
Reserved Notation "P '⊢@{' L } Q" (at level 99, Q at level 200, right associativity).
Reserved Notation "P ⊢f f" (at level 99, f at level 200, no associativity).
Reserved Notation "P ⊣⊢ Q" (at level 95, no associativity).
Reserved Notation "P '⊣⊢@{' L } Q" (at level 95, no associativity).
Reserved Infix "∧" (at level 80, right associativity).
Reserved Infix "∨" (at level 85, right associativity).
Reserved Notation "x → y" (at level 99, y at level 200, right associativity).
Reserved Notation "'!!' e" (at level 25).
Reserved Notation "P ∗ Q" (at level 80, right associativity).
Reserved Notation "P -∗ Q"
  (at level 99, Q at level 200, right associativity,
   format "'[' P  '/' -∗  Q ']'").

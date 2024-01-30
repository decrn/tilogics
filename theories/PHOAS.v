(******************************************************************************)
(* Copyright (c) 2023 Denis Carnier, Steven Keuchel                           *)
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

From Coq Require Import
  Strings.String.
From stdpp Require Import
  base gmap.
From Em Require Import
  Spec.

#[local] Set Implicit Arguments.

Declare Scope phoas_scope.
Delimit Scope phoas_scope with P.
Declare Scope foas_scope.
Delimit Scope foas_scope with F.

Definition exp1 : Exp :=
  exp.app
    (exp.absu "x" (exp.var "x"))
    (exp.absu "y" (exp.var "y")).

Class Pure (F : Type -> Type) : Type :=
  pure : ∀ {A}, A -> F A.
Class Apply (F : Type -> Type) : Type :=
  ap : ∀ {A B}, F (A -> B) -> F A -> F B.

#[local] Typeclasses Transparent compose.
Definition fmap `{Pure F, Apply F} [A B] (f : A -> B) : F A -> F B :=
  ap (pure f).

Notation "f <$> a" := (@fmap _ _ _ _ _ f a) (at level 61, left associativity).
Notation "f <*> a" := (@ap _ _ _ _ f a) (at level 61, left associativity).

#[export] Instance pure_comp `{Pure F, Pure G} : Pure (F ∘ G) :=
  fun A a => pure (pure (F := G) a).

#[export] Instance apply_comp `{Pure F, Apply F, Apply G} : Apply (F ∘ G) :=
  fun A B f => ap (ap (F := G) <$> f).

Module Import PHOAS.

  Inductive PCStr (V : Type) : Type :=
  | ptru
  | pfls
  | peq (t1 t2 : V)
  | pand (C1 C2 : PCStr V)
  | pex (f : V -> PCStr V).
  #[global] Arguments ptru {V}.
  #[global] Arguments pfls {V}.

  Bind Scope phoas_scope with PCStr.
  Notation "∃ x .. y , P" :=
    (pex (fun x => .. (pex (fun y => P%P)) ..)) : phoas_scope.
  Notation "P ∧ Q" := (pand P Q) : phoas_scope.
  Notation "σ = τ" := (peq σ τ) : phoas_scope.
  Notation "⊤" := (ptru) : phoas_scope.
  Notation "⊥" := (pfls) : phoas_scope.

  Fixpoint shallow (C : PCStr Ty) : Prop :=
    match C with
    | ptru => True
    | pfls => False
    | peq t1 t2 => t1 = t2
    | pand C1 C2 => shallow C1 ∧ shallow C2
    | pex f => ∃ t : Ty, shallow (f t)
  end.

  Section Generate.
    Context {OTy : Type} (obool : OTy) (ofunc : OTy -> OTy -> OTy).

    Fixpoint open (τ : Ty) : OTy :=
      match τ with
      | ty.bool       => obool
      | ty.func τ1 τ2 => ofunc (open τ1) (open τ2)
      end.
    Notation "⌈ τ ⌉" := (open τ).

    Fixpoint gen (Γ : gmap string OTy) (e : Exp) (τ : OTy) {struct e} : PCStr OTy :=
      match e with
      | exp.var x         => match Γ !! x with
                             | Some σ => σ = τ
                             | None => ⊥
                             end
      | exp.false         => obool = τ
      | exp.true          => obool = τ
      | exp.ifte e1 e2 e3 => gen Γ e1 obool ∧ gen Γ e2 τ ∧ gen Γ e3 τ
      | exp.absu x e0     => ∃ τ1 τ2, τ = ofunc τ1 τ2 ∧ gen (Γ ,, x∷τ1) e0 τ2
      | exp.abst x τ1 e0  => ∃ τ2, τ = ofunc ⌈τ1⌉ τ2 ∧ gen (Γ ,, x∷⌈τ1⌉) e0 τ2
      | exp.app e1 e2     => ∃ σ, gen Γ e1 (ofunc σ τ) ∧ gen Γ e2 σ
      end.

    Definition infer_phoas (e : Exp) : PCStr OTy :=
      pex (gen empty e).
    Eval vm_compute in infer_phoas exp1.

  End Generate.

End PHOAS.

Module FOAS.

  Import Strings.Ascii Strings.String.
  #[local] Open Scope string_scope.

  Definition World := list string.
  Definition Var := string.

  Section Fresh.

    Definition incr_char (a:ascii) : bool * ascii :=
      match a with
      |"a" => (false,"b")|"b" => (false,"c")|"c" => (false,"d")
      |"d" => (false,"e")|"e" => (false,"f")|"f" => (false,"g")
      |"g" => (false,"h")|"h" => (false,"i")|"i" => (false,"j")
      |"j" => (false,"k")|"k" => (false,"l")|"l" => (false,"m")
      |"m" => (false,"n")|"n" => (false,"o")|"o" => (false,"p")
      |"p" => (false,"q")|"q" => (false,"r")|"r" => (false,"s")
      |"s" => (false,"t")|"t" => (false,"u")|"u" => (false,"v")
      |"v" => (false,"w")|"w" => (false,"x")|"x" => (false,"y")
      |"y" => (false,"z")| _   => (true,"a")
      end%char.

    Fixpoint incr (s : string) : bool * string :=
      match s with
      | ""          => (false, "a")
      | String a "" => let (b, a') := incr_char a in
                       (b, String a' "")
      | String a s  => let (b, s') := incr s in
                       if b
                       then let (b', a') := incr_char a in
                            (b', String a' s')
                       else (false , String a s')
      end.

    Fixpoint max (α : Var) (w : World) : Var :=
      match w with
      | nil      => α
      | cons β w => if String.ltb α β then max β w else max α w
      end.

    Definition fresh (w : World) : Var :=
      let (b, s') := incr (max "" w) in
      if b then String "a" s' else s'.

    Example fresh_nil : fresh nil = "a" := eq_refl.
    Example fresh_1   : fresh ["1"] = "aa" := eq_refl.
    Example fresh_a   : fresh ["a"] = "b"  := eq_refl.
    Example fresh_z   : fresh ["z"] = "aa" := eq_refl.
    Example fresh_tld : fresh ["~"] = "aa" := eq_refl.

  End Fresh.

  Section FOAS.

    Context {T : Type}.
    Inductive FOAS : Type :=
    | ftru
    | ffls
    | feq (t1 t2 : T)
    | fand (C1 C2 : FOAS)
    | fex (α : Var) (C : FOAS).

    Context (var : Var -> T).

    Fixpoint convert (x : PCStr (World -> T)) (w : World) : FOAS :=
      match x with
      | ptru => ftru
      | pfls => ffls
      | peq t1 t2 => feq (t1 w) (t2 w)
      | pand C1 C2 => fand (convert C1 w) (convert C2 w)
      | pex f =>
          let α := fresh w in
          fex α (convert (f (fun w => var α)) (cons α w))
      end.

  End FOAS.

  Bind Scope foas_scope with FOAS.
  Open Scope foas_scope.

  Notation "∃∃ x .. y , P" :=
    (fex x .. (fex y P%F) ..)
      (at level 200, right associativity,
        format "'[  ' '[  ' ∃∃  x  ..  y ']' ,  '/' P ']'") : foas_scope.
  Notation "P ∧ Q" := (fand P Q) : foas_scope.
  Notation "σ = τ" := (feq σ τ) : foas_scope.
  Notation "⊤" := (ftru) : foas_scope.
  Notation "⊥" := (ffls) : foas_scope.

  Inductive OTy : Type :=
  | ovar (α : Var)
  | obool
  | ofunc (σ τ : OTy).

  Coercion ovar : Var >-> OTy.
  Definition infer_foas (e : Exp) : FOAS :=
    convert
      ovar
      (infer_phoas
         (fun w => obool)
         (fun o1 o2 w => ofunc (o1 w) (o2 w))
         e)
      nil.
  Eval vm_compute in infer_foas exp1.

End FOAS.

Module FreePHOAS.

  Inductive Free (V A : Type) : Type :=
  | Ret (a : A)
  | Fail
  | Equalsk (t1 t2 : V) (k : Free V A)
  | Pickk (f : V -> Free V A).
  #[global] Arguments Ret {V A} a.
  #[global] Arguments Fail {V A}.

  #[export] Instance pure_free {V} : Pure (Free V) := @Ret V.
  Definition bind {V A B} (f : A -> Free V B) :=
    fix bind (m : Free V A) : Free V B :=
      match m with
      | Ret a           => f a
      | Fail            => Fail
      | Equalsk t1 t2 k => Equalsk t1 t2 (bind k)
      | Pickk g         => Pickk (fun t => bind (g t))
      end.
  Notation "' x <- ma ;; mb" :=
    (bind (fun x => mb) ma)
      (at level 80, x pattern, ma at next level, mb at level 200, right associativity,
        format "' x  <-  ma  ;;  mb").
  Notation "x <- ma ;; mb" :=
    (bind (fun x => mb) ma)
      (at level 80, ma at next level, mb at level 200, right associativity).

  #[export] Instance apply_free {V} : Apply (Free V) :=
    fun A B f m => f' <- f ;; m' <- m ;; pure (f' m').

  Definition equals {V} (τ1 τ2 : V) : Free V unit :=
    Equalsk τ1 τ2 (Ret tt).
  Definition pick {V} : Free V V :=
    Pickk Ret.

  Section Generate.

    Context {OTy} (obool : OTy) (ofunc : OTy -> OTy -> OTy).

    Fixpoint open (τ : Ty) : OTy :=
      match τ with
      | ty.bool       => obool
      | ty.func τ1 τ2 => ofunc (open τ1) (open τ2)
      end.
    Notation "⌈ τ ⌉" := (open τ).

    Fixpoint synth (Γ : gmap string OTy) (e : Exp) {struct e} : Free OTy OTy :=
      match e with
      | exp.var x         => match Γ !! x with
                             | Some σ => pure σ
                             | None => Fail
                             end
      | exp.false         => pure obool
      | exp.true          => pure obool
      | exp.ifte e1 e2 e3 => τ1 <- synth Γ e1 ;;
                             τ2 <- synth Γ e2 ;;
                             τ3 <- synth Γ e3 ;;
                             _  <- equals τ1 obool ;;
                             _  <- equals τ2 τ3 ;;
                             pure τ2
      | exp.absu x e0     => τ1 <- pick ;;
                             τ2 <- synth (Γ ,, x∷τ1) e0 ;;
                             pure (ofunc τ1 τ2)
      | exp.abst x t1 e0  => τ2 <- synth (Γ ,, x∷⌈t1⌉) e0 ;;
                             pure (ofunc ⌈t1⌉ τ2)
      | exp.app e1 e2     => τf <- synth Γ e1 ;;
                             τa <- synth Γ e2 ;;
                             τr <- pick ;;
                             _  <- equals τf (ofunc τa τr) ;;
                             pure τr
      end.

    Context {Open : Type -> Type} {opure : Pure Open} {oap : Apply Open}
      (close : OTy -> Open Ty).

    Fixpoint elabsynth (Γ : gmap string OTy) (e : Exp) {struct e} :
      Free OTy (OTy * Open Exp) :=
      match e with
      | exp.var x         => match Γ !! x with
                             | Some σ => pure (σ,opure (exp.var x))
                             | None => Fail
                             end
      | exp.false         => pure (obool, pure exp.false)
      | exp.true          => pure (obool, pure exp.true)
      | exp.ifte e1 e2 e3 => '(τ1,e1') <- elabsynth Γ e1 ;;
                             '(τ2,e2') <- elabsynth Γ e2 ;;
                             '(τ3,e3') <- elabsynth Γ e3 ;;
                             _  <- equals τ1 obool ;;
                             _  <- equals τ2 τ3 ;;
                             pure (τ2, exp.ifte <$> e1' <*> e2' <*> e3')
      | exp.absu x e0     => τ1 <- pick ;;
                             '(τ2,e0') <- elabsynth (Γ ,, x∷τ1) e0 ;;
                             pure (ofunc τ1 τ2, exp.abst x <$> close τ1 <*> e0')
      | exp.abst x t1 e0  => '(τ2,e0') <- elabsynth (Γ ,, x∷⌈t1⌉) e0 ;;
                             pure (ofunc ⌈t1⌉ τ2, exp.abst x t1 <$> e0')
      | exp.app e1 e2     => '(τf,e1') <- elabsynth Γ e1 ;;
                             '(τa,e2') <- elabsynth Γ e2 ;;
                             τr <- pick ;;
                             _  <- equals τf (ofunc τa τr) ;;
                             pure (τr, exp.app <$> e1' <*> e2')
      end.

    Definition elabsynth' (Γ : gmap string OTy) (e : Exp) : Free OTy (Open (Ty * Exp)) :=
      '(τ,ee) <- elabsynth Γ e;;
      pure (pair <$> close τ <*> ee).

    Section ApplicativeInterface.

      Definition Co A := Free OTy (Open A).
      Definition cpure : Pure Co :=
        fun A a => pure (pure (F := Open) a).
      Definition capply : Apply Co :=
        fun A B f => ap (ap (F := Open) <$> f).
      Definition cfmap {A B} (f : A → B) : Co A → Co B :=
        capply (cpure f).
      Definition cexists {A} (f : OTy -> Co A) : Co A :=
        bind f pick.
      Definition cequals (τ1 τ2 : OTy) : Co unit :=
        bind (@cpure unit) (equals τ1 τ2).
      Definition cdecode (τ : OTy) : Co Ty :=
        pure (close τ).

      Declare Scope applicative_scope.
      Delimit Scope applicative_scope with A.
      Notation "∃ x .. y , m" :=
        (cexists (fun x => .. (cexists (fun y => m%A)) ..)) :
          applicative_scope.
      Bind Scope applicative_scope with Co.
      Open Scope applicative_scope.

      Notation "f <$> a" := (cfmap f a) (at level 61, left associativity).
      Notation "f <*> a" := (capply f a) (at level 61, left associativity).

      Definition mlpure [A B] (a : A) (mb : Co B) : Co A :=
        (fun b => a) <$> mb.
      Definition mrpure [A B] (ma : Co A) (b : B) : Co B :=
        (fun a => b) <$> ma.
      Definition mlap [A B] (ma : Co A) (mb : Co B) : Co A :=
        (fun a b => a) <$> ma <*> mb.
      Definition mrap [A B] (ma : Co A) (mb : Co B) : Co B :=
        (fun a b => b) <$> ma <*> mb.

      Notation "a <$ mb" :=
        (mlpure a mb)
          (at level 61, left associativity) : applicative_scope.
      Notation "ma $> b" :=
        (mrpure ma b)
          (at level 61, left associativity) : applicative_scope.
      Notation "ma <* mb" :=
        (mlap ma mb)
          (at level 61, left associativity) : applicative_scope.
      Notation "ma *> mb" :=
        (mrap ma mb)
          (at level 61, left associativity) : applicative_scope.

      Fixpoint elabcheck (Γ : gmap string OTy) (e : Exp) (τ : OTy) {struct e} :
        Co Exp :=
        match e with
        | exp.var x         => match Γ !! x with
                               | Some σ => exp.var x
                                             <$ cequals σ τ
                               | None   => Fail
                               end
        | exp.false         => exp.false
                                 <$ cequals obool τ
        | exp.true          => exp.true
                                 <$ cequals obool τ
        | exp.ifte e1 e2 e3 => exp.ifte
                                 <$> elabcheck Γ e1 obool
                                 <*> elabcheck Γ e2 τ
                                 <*> elabcheck Γ e3 τ
        | exp.absu x e0     => ∃ τ1 τ2,
                               exp.abst x
                                 <$  cequals τ (ofunc τ1 τ2)
                                 <*> cdecode τ1
                                 <*> elabcheck (Γ ,, x∷τ1) e0 τ2
        | exp.abst x τ1 e0  => ∃ τ2,
                               exp.abst x τ1
                                 <$> elabcheck (Γ ,, x∷open τ1) e0 τ2
        | exp.app e1 e2     => ∃ τa,
                               exp.app
                                 <$> elabcheck Γ e1 (ofunc τa τ)
                                 <*> elabcheck Γ e2 τa
        end.

    End ApplicativeInterface.

  End Generate.

End FreePHOAS.

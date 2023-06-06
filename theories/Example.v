From Coq Require Import
     Strings.String.
From Em Require Import
     Context.
Import ctx.notations.

Inductive ty : Type :=
  | ty_nat
  | ty_bool.

Module WellScoped.

  Inductive expr (Γ : Ctx string) : Type :=
    (* values *)
    | v_true  : expr Γ
    | v_false : expr Γ
    | v_O     : expr Γ
    | v_S     : expr Γ -> expr Γ
    (* compound expressions *)
    | e_if    : expr Γ -> expr Γ -> expr Γ -> expr Γ
    | e_plus  : expr Γ -> expr Γ -> expr Γ
    | e_lte   : expr Γ -> expr Γ -> expr Γ
    | e_and   : expr Γ -> expr Γ -> expr Γ
    | e_let   : forall (x : string), expr Γ -> expr (Γ ▻ x) -> expr Γ
    | e_tlet  : forall (x : string), ty -> expr Γ -> expr (Γ ▻ x) -> expr Γ
    | e_var   : forall (x : string), x ∈ Γ -> expr Γ.

End WellScoped.

Module WellTyped.

  Inductive expr (Γ : Ctx (string*ty)) : ty -> Type :=
    (* values *)
    | v_true    : expr Γ ty_bool
    | v_false   : expr Γ ty_bool
    | v_O       : expr Γ ty_nat
    | v_S       : expr Γ ty_nat -> expr Γ ty_nat
    (* compound expressions *)
    | e_if {σ}  : expr Γ ty_bool -> expr Γ σ -> expr Γ σ -> expr Γ σ
    | e_plus    : expr Γ ty_nat -> expr Γ ty_nat -> expr Γ ty_nat
    | e_lte     : expr Γ ty_nat -> expr Γ ty_nat -> expr Γ ty_bool
    | e_and     : expr Γ ty_bool -> expr Γ ty_bool -> expr Γ ty_bool
    | e_let {τ} : forall (x : string) (σ : ty), expr Γ σ -> expr (Γ ▻ (x,σ)) τ -> expr Γ τ
    | e_var     : forall (x : string) (σ : ty), (x,σ) ∈ Γ -> expr Γ σ.

End WellTyped.

From Metaconfigurations Require Import 
  Map Syntax.Term Syntax.Value Object.
From stdpp Require Import base stringmap decidable.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Global Declare Scope dynamics_scope.

Definition states (Π Ω : Type) `{Object Π Ω} := Map.dependent Ω (Σ ∘ type).

Variant eval_binop : Term.bop → Value.t → Value.t → Value.t → Type :=
  | eval_add (n₁ n₂ : Z) : eval_binop Term.Add n₁ n₂ (n₁ + n₂)%Z
  | eval_sub (n₁ n₂ : Z) : eval_binop Term.Sub n₁ n₂ (n₁ - n₂)%Z
  | eval_mul (n₁ n₂ : Z) : eval_binop Term.Mul n₁ n₂ (n₁ * n₂)%Z
  | eval_or (b₁ b₂ : bool) : eval_binop Term.Or b₁ b₂ (b₁ || b₂)
  | eval_and (b₁ b₂ : bool) : eval_binop Term.And b₁ b₂ (b₁ && b₂).

Variant eval_unop : Term.uop → Value.t → Value.t → Type :=
  | eval_not (b : bool) : eval_unop Term.Not b (negb b).  

    (* match bop, v₁, v₂ with
    | Add, Value.Int n₁, Value.Int n₂ => (n₁ + n₂)%Z
    | Sub, Value.Int n₁, Value.Int n₂ => (n₁ - n₂)%Z
    | Mul, Value.Int n₁, Value.Int n₂ => (n₁ * n₂)%Z
    | 
    end. *)

(* (ω : Ω) (op : (type ω).(OP)) (arg : (type ω).(ARG Π) *)

Variant eval_inv {Π Ω} `{Object Π Ω} π ϵ ω op arg σ res :=
  | eval_inv_intro :
    (type ω).(δ) (Map.lookup ω ϵ) π op arg σ res →
    eval_inv π ϵ ω op arg σ res.

Reserved Notation "⟨ π , arg , Ψ , ϵ , e ⟩ ⇓ₑ ⟨ ϵ' , v ⟩" (at level 80, no associativity).

Inductive eval {Π Ω} `{Object Π Ω} (π : Π) (arg : Value.t) (ψ : stringmap Value.t) (ϵ : states Π Ω) : Term.t Π Ω → states Π Ω → Value.t → Prop := 
  | eval_var x v :
    ψ !! x = Some v →
    ⟨ π , arg , ψ , ϵ , Var x ⟩ ⇓ₑ ⟨ ϵ , v ⟩
  | eval_arg :
    ⟨ π , arg , ψ , ϵ , Arg ⟩ ⇓ₑ ⟨ ϵ , arg ⟩
  | eval_invoke ω op e v res ϵ' σ :
    ⟨ π , arg , ψ , ϵ , e ⟩ ⇓ₑ ⟨ ϵ' , v ⟩ →
    eval_inv π ϵ ω op v σ res →
    ⟨ π , arg , ψ , ϵ , Invoke ω op e ⟩ ⇓ₑ ⟨ rebind ω σ ϵ' , res ⟩
  | eval_bop bop e₁ e₂ v₁ v₂ v ϵ₁ ϵ₂ : 
    ⟨ π , arg , ψ , ϵ , e₁ ⟩ ⇓ₑ ⟨ ϵ₁ , v₁ ⟩ →
    ⟨ π , arg , ψ , ϵ₁ , e₂ ⟩ ⇓ₑ ⟨ ϵ₂ , v₂ ⟩ →
    eval_binop bop v₁ v₂ v →
    ⟨ π , arg , ψ , ϵ , Bop bop e₁ e₂ ⟩ ⇓ₑ ⟨ ϵ₂ , v ⟩
  | eval_uop e uop ϵ' v v' :
    ⟨ π , arg , ψ , ϵ , e ⟩ ⇓ₑ ⟨ ϵ' , v ⟩ →
    eval_unop uop v v' → 
    ⟨ π , arg , ψ , ϵ , Uop uop e ⟩ ⇓ₑ ⟨ ϵ' , v' ⟩
  | eval_pair e₁ e₂ v₁ v₂ ϵ₁ ϵ₂ :
    ⟨ π , arg , ψ , ϵ , e₁ ⟩ ⇓ₑ ⟨ ϵ₁ , v₁ ⟩ →
    ⟨ π , arg , ψ , ϵ₁ , e₂ ⟩ ⇓ₑ ⟨ ϵ₂ , v₂ ⟩ →
    ⟨ π , arg , ψ , ϵ , Term.Pair e₁ e₂ ⟩ ⇓ₑ ⟨ ϵ₂ , Pair v₁ v₂ ⟩
  | eval_projl e v₁ v₂ ϵ' :
    ⟨ π , arg , ψ , ϵ , e ⟩ ⇓ₑ ⟨ ϵ' , Pair v₁ v₂ ⟩ →
    ⟨ π , arg , ψ , ϵ , ProjL e ⟩ ⇓ₑ ⟨ ϵ' , v₁ ⟩
  | eval_projr e v₁ v₂ ϵ' :
    ⟨ π , arg , ψ , ϵ , e ⟩ ⇓ₑ ⟨ ϵ' , Pair v₁ v₂ ⟩ →
    ⟨ π , arg , ψ , ϵ , ProjR e ⟩ ⇓ₑ ⟨ ϵ' , v₂ ⟩
  | eval_int n :
    ⟨ π , arg , ψ , ϵ , Term.Int n ⟩ ⇓ₑ ⟨ ϵ , n ⟩
  | eval_bool b :
    ⟨ π , arg , ψ , ϵ , Term.Bool b ⟩ ⇓ₑ ⟨ ϵ , b ⟩
  | eval_unit :
    ⟨ π , arg , ψ , ϵ , ⊤ₑ ⟩ ⇓ₑ ⟨ ϵ , ⊤ᵥ ⟩
where "⟨ π , arg , ψ , ϵ , e ⟩ ⇓ₑ ⟨ ϵ' , v ⟩" := (eval π arg ψ ϵ e ϵ' v) : dynamics_scope.
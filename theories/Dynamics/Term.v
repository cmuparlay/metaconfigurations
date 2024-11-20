From Metaconfigurations Require Import 
  Map Syntax.Term Syntax.Ty Syntax.Value Statics.Value Object Process.
From stdpp Require Import base.
Require Import Coq.ZArith.BinInt.

Section Eval.

  Variable Π : Type.

  Context `{H : Process Π}.

  Variable Ω : Type.

  Context `{Object Π Ω}.

  Variable π : Π.

  Definition states := Map.dependent Ω (Σ Π ∘ type).

  Reserved Notation "⟨ Ψ , ϵ , e ⟩ ⇓ₑ ⟨ ϵ' , v ⟩" (at level 80, no associativity).

  Variant eval_binop : Term.bop → Value.t → Value.t → Value.t → Set :=
    | eval_add (n₁ n₂ : Z) : eval_binop Term.Add n₁ n₂ (n₁ + n₂)%Z
    | eval_sub (n₁ n₂ : Z) : eval_binop Term.Sub n₁ n₂ (n₁ - n₂)%Z
    | eval_mul (n₁ n₂ : Z) : eval_binop Term.Mul n₁ n₂ (n₁ * n₂)%Z
    | eval_or (b₁ b₂ : bool) : eval_binop Term.Or b₁ b₂ (b₁ || b₂)
    | eval_and (b₁ b₂ : bool) : eval_binop Term.And b₁ b₂ (b₁ && b₂).

  Variant eval_unop : Term.uop → Value.t → Value.t → Set :=
    | eval_not (b : bool) : eval_unop Term.Not b (negb b).  

    (* match bop, v₁, v₂ with
    | Add, Value.Int n₁, Value.Int n₂ => (n₁ + n₂)%Z
    | Sub, Value.Int n₁, Value.Int n₂ => (n₁ - n₂)%Z
    | Mul, Value.Int n₁, Value.Int n₂ => (n₁ * n₂)%Z
    | 
    end. *)

  Inductive eval (ψ : Map.t (register_names π) Value.t) (ϵ : states) : Term.t Π Ω π → states → Value.t → Prop := 
    | eval_var (x : register_names π) : ⟨ ψ , ϵ , Var x ⟩ ⇓ₑ ⟨ ϵ , @Map.lookup _ _ (eq_dec π) x ψ ⟩
    | eval_invoke ω op arg argᵥ res ϵ' σ :
      ⟨ ψ , ϵ , arg ⟩ ⇓ₑ ⟨ ϵ' , argᵥ ⟩ →
      ∀ H : ⊢ᵥ argᵥ `: (type ω).(ARG Π) op,
      (type ω).(δ Π) (Map.lookup ω ϵ) π op (exist _ argᵥ H) = (σ, res) →
      ⟨ ψ , ϵ , Invoke ω op arg ⟩ ⇓ₑ ⟨ rebind ω σ ϵ' , proj1_sig res ⟩
    | eval_bop bop e₁ e₂ v₁ v₂ v ϵ₁ ϵ₂ : 
      ⟨ ψ , ϵ , e₁ ⟩ ⇓ₑ ⟨ ϵ₁ , v₁ ⟩ →
      ⟨ ψ , ϵ₁ , e₂ ⟩ ⇓ₑ ⟨ ϵ₂ , v₂ ⟩ →
      eval_binop bop v₁ v₂ v →
      ⟨ ψ , ϵ , Bop bop e₁ e₂ ⟩ ⇓ₑ ⟨ ϵ₂ , v ⟩
    | eval_uop e uop ϵ' v v' :
      ⟨ ψ , ϵ , e ⟩ ⇓ₑ ⟨ ϵ' , v ⟩ →
      eval_unop uop v v' → 
      ⟨ ψ , ϵ , Uop uop e ⟩ ⇓ₑ ⟨ ϵ' , v' ⟩
    | eval_pair e₁ e₂ v₁ v₂ ϵ₁ ϵ₂ :
      ⟨ ψ , ϵ , e₁ ⟩ ⇓ₑ ⟨ ϵ₁ , v₁ ⟩ →
      ⟨ ψ , ϵ₁ , e₂ ⟩ ⇓ₑ ⟨ ϵ₂ , v₂ ⟩ →
      ⟨ ψ , ϵ , Term.Pair e₁ e₂ ⟩ ⇓ₑ ⟨ ϵ₂ , Pair v₁ v₂ ⟩
    | eval_projl e v₁ v₂ ϵ' :
      ⟨ ψ , ϵ , e ⟩ ⇓ₑ ⟨ ϵ' , Pair v₁ v₂ ⟩ →
      ⟨ ψ , ϵ , ProjL e ⟩ ⇓ₑ ⟨ ϵ' , v₁ ⟩
    | eval_projr e v₁ v₂ ϵ' :
      ⟨ ψ , ϵ , e ⟩ ⇓ₑ ⟨ ϵ' , Pair v₁ v₂ ⟩ →
      ⟨ ψ , ϵ , ProjR e ⟩ ⇓ₑ ⟨ ϵ' , v₂ ⟩
    | eval_int n :
      ⟨ ψ , ϵ , Term.Int n ⟩ ⇓ₑ ⟨ ϵ , n ⟩
    | eval_bool b :
      ⟨ ψ , ϵ , Term.Bool b ⟩ ⇓ₑ ⟨ ϵ , b ⟩
    | eval_unit :
      ⟨ ψ , ϵ , ⊤ₑ ⟩ ⇓ₑ ⟨ ϵ , ⊤ᵥ ⟩
  where "⟨ ψ , ϵ , e ⟩ ⇓ₑ ⟨ ϵ' , v ⟩" := (eval ψ ϵ e ϵ' v).
End Eval.
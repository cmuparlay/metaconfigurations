From Metaconfigurations Require Import 
  Map Syntax.Term Syntax.Stmt
  Syntax.Value Dynamics.Term Object.
From stdpp Require Import base stringmap.

Variant signal :=
  | Continue
  | Goto (l : nat)
  | Return (v : Value.t).

Reserved Notation "⟨ π , arg , ψ , ϵ , s ⟩ ⇓ₛ ⟨ Ψ' , ϵ' , sig ⟩" (at level 80, no associativity).

Inductive eval {Π Ω} `{Object Π Ω} (π : Π) (arg : Value.t) (ψ : stringmap Value.t) (ϵ : states Π Ω) : Stmt.t Π Ω → stringmap Value.t → states Π Ω → signal → Prop :=
  | eval_skip : ⟨ π , arg , ψ , ϵ , Skip ⟩ ⇓ₛ ⟨ ψ , ϵ , Continue ⟩
  | eval_seq_return s₁ s₂ ψ₁ ϵ₁ v : 
    ⟨ π , arg , ψ , ϵ , s₁ ⟩ ⇓ₛ ⟨ ψ₁ , ϵ₁ , Return v ⟩ →
    ⟨ π , arg , ψ , ϵ , Seq s₁ s₂ ⟩ ⇓ₛ ⟨ ψ₁ , ϵ₁ , Return v ⟩
  | eval_seq_goto s₁ s₂ ψ₁ ϵ₁ n : 
    ⟨ π , arg , ψ , ϵ , s₁ ⟩ ⇓ₛ ⟨ ψ₁ , ϵ₁ , Goto n ⟩ →
    ⟨ π , arg , ψ , ϵ , Seq s₁ s₂ ⟩ ⇓ₛ ⟨ ψ₁ , ϵ₁ , Goto n ⟩
  | eval_seq_cont s₁ s₂ ϵ₁ ψ₁ ϵ₂ ψ₂ sig :
    ⟨ π , arg , ψ , ϵ , s₁ ⟩ ⇓ₛ ⟨ ψ₁ , ϵ₁ , Continue ⟩ →
    ⟨ π , arg , ψ₁ , ϵ₁ , s₂ ⟩ ⇓ₛ ⟨ ψ₂ , ϵ₂ , sig ⟩ →
    ⟨ π , arg , ψ , ϵ , Seq s₁ s₂ ⟩ ⇓ₛ ⟨ ψ₂ , ϵ₂ , sig ⟩
  | eval_if_true e s₁ s₂ ϵ' ϵ₁ ψ₁ sig :
    ⟨ π , arg , ψ , ϵ , e ⟩ ⇓ₑ ⟨ ϵ' , true ⟩ →
    ⟨ π , arg , ψ , ϵ' , s₁ ⟩ ⇓ₛ ⟨ ψ₁ , ϵ₁ , sig ⟩ →
    ⟨ π , arg , ψ , ϵ , If e s₁ s₂ ⟩ ⇓ₛ ⟨ ψ₁ , ϵ₁ , sig ⟩
  | eval_if_false e s₁ s₂ ϵ' ϵ₂ ψ₂ sig :
    ⟨ π , arg , ψ , ϵ , e ⟩ ⇓ₑ ⟨ ϵ' , false ⟩ →
    ⟨ π , arg , ψ , ϵ' , s₂ ⟩ ⇓ₛ ⟨ ψ₂ , ϵ₂ , sig ⟩ →
    ⟨ π , arg , ψ , ϵ , If e s₁ s₂ ⟩ ⇓ₛ ⟨ ψ₂ , ϵ₂ , sig ⟩
  | eval_assign x e ϵ' v :
    ⟨ π , arg , ψ , ϵ , e ⟩ ⇓ₑ ⟨ ϵ' , v ⟩ →
    ⟨ π , arg , ψ , ϵ , Assign x e ⟩ ⇓ₛ ⟨ <[x:=v]>ψ , ϵ , Continue ⟩
  | eval_goto n :
    ⟨ π , arg , ψ , ϵ , Syntax.Stmt.Goto n ⟩ ⇓ₛ ⟨ ψ , ϵ , Goto n ⟩
  | eval_invoke ω op e ϵ' v :
    ⟨ π , arg , ψ , ϵ , Term.Invoke ω op e ⟩ ⇓ₑ ⟨ ϵ' , v ⟩ →
    ⟨ π , arg , ψ , ϵ , Invoke (Invocation ω op e) ⟩ ⇓ₛ ⟨ ψ , ϵ' , Continue ⟩
  | eval_return e ϵ' v :
    ⟨ π , arg , ψ , ϵ , e ⟩ ⇓ₑ ⟨ ϵ' , v ⟩ →
    ⟨ π , arg , ψ , ϵ , Syntax.Stmt.Return e ⟩ ⇓ₛ ⟨ ψ , ϵ' , Return v ⟩
where "⟨ π , arg , ψ , ϵ , s ⟩ ⇓ₛ ⟨ ψ' , ϵ' , sig ⟩" := (eval π arg ψ ϵ s ψ' ϵ' sig) : dynamics_scope.

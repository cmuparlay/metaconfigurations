From Metaconfigurations Require Import 
  Map Syntax.Term Syntax.Stmt Syntax.Ty 
  Syntax.Value Statics.Value 
  Dynamics.Term Object Process.
From stdpp Require Import base.
Require Import Coq.ZArith.BinInt.

Section Eval.

  Variable Π : Type.

  Context `{H : Process Π}.

  Variable Ω : Type.

  Context `{Object Π Ω}.

  Variable π : Π.

  Definition states := Dynamics.Term.states Π Ω.

  Variant signal :=
    | Continue
    | Goto (l : nat).

  Reserved Notation "⟨ Ψ , ϵ , s ⟩ ⇓ₛ ⟨ Ψ' , ϵ' , sig ⟩" (at level 80, no associativity).

  Definition register_file := 

  Inductive eval (ψ : Map.t (register_names π) Value.t) (ϵ : states) : Stmt.t Π Ω π → states → signal → Prop := 
    | eval_seq_goto s₁ s₂ ψ₁ ϵ₁ n : 
      ⟨ ψ , ϵ , s₁ ⟩ ⇓ₛ ⟨ ψ₁ , ϵ₁ , Goto n ⟩ →
      ⟨ ψ , ϵ , Seq s₁ s₂ ⟩ ⇓ₛ ⟨ ψ₁ , ϵ₁ , Goto n ⟩
    | eval_seq_cont s₁ s₂ ϵ₁ ψ₁ ϵ₂ ψ₂ sig : 
      ⟨ ψ , ϵ , s₁ ⟩ ⇓ₛ ⟨ ψ₁ , ϵ₁ , Continue ⟩ →
      ⟨ ψ₁ , ϵ₁ , s₂ ⟩ ⇓ₛ ⟨ ψ₂ , ϵ₂ , sig ⟩ →
      ⟨ ψ , ϵ , Seq s₁ s₂ ⟩ ⇓ₛ ⟨ ψ₂ , ϵ₂ , sig ⟩
    | eval_if_true e s₁ s₂ ϵ' ϵ₁ ψ₁ sig :
      Term.eval Π Ω π ψ ϵ e ϵ' true →
      ⟨ ψ , ϵ' , s₁ ⟩ ⇓ₛ ⟨ ψ₁ , ϵ₁ , sig ⟩ →
      ⟨ ψ , ϵ , If e s₁ s₂ ⟩ ⇓ₛ ⟨ ψ₁ , ϵ₁ , sig ⟩
    | eval_if_false e s₁ s₂ ϵ' ϵ₂ sig :
      Term.eval Π Ω π ψ ϵ e ϵ' false →
      ⟨ ψ , ϵ' , s₂ ⟩ ⇓ₛ ⟨ ψ₂ , ϵ₂ , sig ⟩ →
      ⟨ ψ , ϵ , If e s₁ s₂ ⟩ ⇓ₛ ⟨ ψ₂ , ϵ₂ , sig ⟩
  where "⟨ ψ , ϵ , s ⟩ ⇓ₛ ⟨ ψ' , ϵ' , sig ⟩" := (eval ψ ϵ s ψ' ϵ' sig).
End Eval.
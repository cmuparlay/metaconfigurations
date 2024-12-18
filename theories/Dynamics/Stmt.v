From Metaconfigurations Require Import 
  Map Syntax.Term Syntax.Stmt
  Syntax.Value Dynamics.Term Object.
From stdpp Require Import base stringmap.
Require Import Coq.ZArith.BinInt.

Section Eval.

  Context {Π Ω : Type}.

  Context `{Object Π Ω}.

  Variable π : Π.

  Variant signal :=
    | Continue
    | Goto (l : nat)
    | Return (v : Value.t).

  Reserved Notation "⧼ π , ψ , ϵ , s ⧽ ⇓ₛ ⧼ Ψ' , ϵ' , sig ⧽" (at level 80, no associativity).

  Declare Scope dynamics_scope.

  Inductive eval (π : Π) (ψ : stringmap Value.t) (ϵ : states Π Ω) : Stmt.t Π Ω → stringmap Value.t → states Π Ω → signal → Prop :=
    | eval_skip : ⧼ π , ψ , ϵ , Skip ⧽ ⇓ₛ ⧼ ψ , ϵ , Continue ⧽
    | eval_seq_return s₁ s₂ ψ₁ ϵ₁ v : 
      ⧼ π , ψ , ϵ , s₁ ⧽ ⇓ₛ ⧼ ψ₁ , ϵ₁ , Return v ⧽ →
      ⧼ π , ψ , ϵ , Seq s₁ s₂ ⧽ ⇓ₛ ⧼ ψ₁ , ϵ₁ , Return v ⧽
    | eval_seq_goto s₁ s₂ ψ₁ ϵ₁ n : 
      ⧼ π , ψ , ϵ , s₁ ⧽ ⇓ₛ ⧼ ψ₁ , ϵ₁ , Goto n ⧽ →
      ⧼ π , ψ , ϵ , Seq s₁ s₂ ⧽ ⇓ₛ ⧼ ψ₁ , ϵ₁ , Goto n ⧽
    | eval_seq_cont s₁ s₂ ϵ₁ ψ₁ ϵ₂ ψ₂ sig :
      ⧼ π , ψ , ϵ , s₁ ⧽ ⇓ₛ ⧼ ψ₁ , ϵ₁ , Continue ⧽ →
      ⧼ π , ψ₁ , ϵ₁ , s₂ ⧽ ⇓ₛ ⧼ ψ₂ , ϵ₂ , sig ⧽ →
      ⧼ π , ψ , ϵ , Seq s₁ s₂ ⧽ ⇓ₛ ⧼ ψ₂ , ϵ₂ , sig ⧽
    | eval_if_true e s₁ s₂ ϵ' ϵ₁ ψ₁ sig :
      Term.eval π ψ ϵ e ϵ' true →
      ⧼ π , ψ , ϵ' , s₁ ⧽ ⇓ₛ ⧼ ψ₁ , ϵ₁ , sig ⧽ →
      ⧼ π , ψ , ϵ , If e s₁ s₂ ⧽ ⇓ₛ ⧼ ψ₁ , ϵ₁ , sig ⧽
    | eval_if_false e s₁ s₂ ϵ' ϵ₂ ψ₂ sig :
      Term.eval π ψ ϵ e ϵ' false →
      ⧼ π , ψ , ϵ' , s₂ ⧽ ⇓ₛ ⧼ ψ₂ , ϵ₂ , sig ⧽ →
      ⧼ π , ψ , ϵ , If e s₁ s₂ ⧽ ⇓ₛ ⧼ ψ₂ , ϵ₂ , sig ⧽
    | eval_assign x e ϵ' v :
      Term.eval π ψ ϵ e ϵ' v →
      ⧼ π , ψ , ϵ , Assign x e ⧽ ⇓ₛ ⧼ <[x:=v]>ψ , ϵ , Continue ⧽
    | eval_goto n :
      ⧼ π , ψ , ϵ , Stmt.Goto n ⧽ ⇓ₛ ⧼ ψ , ϵ , Goto n ⧽
    | eval_invoke ω op arg ϵ' v :
      Term.eval π ψ ϵ (Term.Invoke ω op arg) ϵ' v →
      ⧼ π , ψ , ϵ , Invoke (Invocation ω op arg) ⧽ ⇓ₛ ⧼ ψ , ϵ' , Continue ⧽
    | eval_return e ϵ' v :
      Term.eval π ψ ϵ e ϵ' v →
      ⧼ π , ψ , ϵ , Stmt.Return e ⧽ ⇓ₛ ⧼ ψ , ϵ' , Return v ⧽
  where "⧼ π , ψ , ϵ , s ⧽ ⇓ₛ ⧼ ψ' , ϵ' , sig ⧽" := (eval π ψ ϵ s ψ' ϵ' sig) : dynamics_scope.
End Eval.

Require Import Metaconfigurations.Syntax.

(** Machine configurations are represented as tuples [⟨ σ , ϵ , e ⟩] where [σ] 
    binds thread-local variables to their values, [δ] binds object names to object states,
    ϵ binds object names to object types, and [e] is a term *)
Reserved Notation "⟨ σ , δ , ϵ , e ⟩ ⇓ v"
         (at level 80, no associativity).

Module Expr.
  (* configuration should include store bindings from thread-local variables to values *)
  Inductive Step : Type :=
    | Step
End Expr.
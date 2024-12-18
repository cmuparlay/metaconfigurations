From stdpp Require Import base gmap.
From Metaconfigurations Require Import Syntax.Term Object.
Require Import Coq.Strings.String.

Section Stmt.

  Variables Π Ω : Type.

  Context `{Object Π Ω}.

  Inductive t : Type :=
    | Seq (s₁ : t) (s₂ : t)
    | Assign (x : string) (e : Term.t Π Ω)
    | If (e : Term.t Π Ω) (s₁ : t) (s₂ : t)
    | Goto (l : nat)
    | Return (e : Term.t Π Ω)
    | Invoke (inv : invocation Π Ω)
    | Skip.

  Notation "s₁ `; s₂" := (Seq s₁ s₂) (at level 80).
  Notation "x ← e" := (Assign x e) (at level 80).

End Stmt.

Arguments Seq {_ _ _ _}.
Arguments Assign {_ _ _ _}.
Arguments If {_ _ _ _}.
Arguments Goto {_ _ _ _}.
Arguments Return {_ _ _ _}.
Arguments Invoke {_ _ _ _}.
Arguments Skip {_ _ _ _}.

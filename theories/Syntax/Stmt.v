From Metaconfigurations Require Import Syntax.Term Object.
Require Import Coq.Strings.String.
From stdpp Require Import base gmap.

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

(** [free x s] is provable iff variable [x] is free in statement [s] *)
Inductive free {Π Ω} `{Object Π Ω} : string → t Π Ω → Prop :=
  | free_seq_l x s₁ s₂ : free x s₁ → free x (Seq s₁ s₂)
  | free_seq_r x s₁ s₂ : free x s₂ → free x (Seq s₁ s₂)
  | free_assign x e y : x ≠ y → Term.free y e → free y (Assign x e)
  | free_if_guard x e s₁ s₂ : Term.free x e → free x (If e s₁ s₂)
  | free_if_l x e s₁ s₂ : free x s₁ → free x (If e s₁ s₂)
  | free_if_r x e s₁ s₂ : free x s₂ → free x (If e s₁ s₂)
  | free_return x e : Term.free x e → free x (Return e).

Instance subst_stmt {Π Ω} `{Object Π Ω} : Subst (t Π Ω) :=
  fix subst_stmt eₓ x s :=
    match s with
    | Seq s₁ s₂ => Seq (subst_stmt eₓ x s₁) (subst_stmt eₓ x s₂)
    | Assign x e => Assign x (subst eₓ x e)
    | If e s₁ s₂ => If (subst eₓ x e) (subst_stmt eₓ x s₁) (subst_stmt eₓ x s₁)
    | Return e => Return (subst eₓ x e)
    | Invoke (Invocation ω op e) => Invoke (Invocation ω op (subst eₓ x e))
    | Goto _ | Skip => s
    end.

From stdpp Require Import base gmap.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
From Metaconfigurations Require Import Object.

Variant bop : Set :=
  | Add
  | Sub
  | Mul
  | And
  | Or.

Variant uop : Set := Not.

Declare Scope term_scope.

Section Term.

  Variables Π Ω : Type.

  Context `{Object Π Ω}.

  Inductive t : Type :=
    | Var (x : string)
    | Invoke (ω : Ω) (op : (type ω).(OP Π)) (arg : t)
    | Bop (op : bop) (e₁ : t) (e₂ : t)
    | Uop (op : uop) (e : t)
    | Pair (e₁ : t) (e₂ : t)
    | ProjL (e : t)
    | ProjR (e : t)
    | Int (n : Z)
    | Bool (b : bool)
    | Unit.

  Variant invocation : Type := Invocation (ω : Ω) (op : (type ω).(OP Π)) (arg : t).

End Term.

Arguments Var {Π Ω _ _}.
Arguments Invoke {Π Ω _ _}.
Arguments Bop {Π Ω _ _}.
Arguments Uop {Π Ω _ _}.
Arguments Pair {Π Ω _ _}.
Arguments ProjL {Π Ω _ _}.
Arguments ProjR {Π Ω _ _}.
Arguments Int {Π Ω _ _}.
Arguments Bool {Π Ω _ _}.
Arguments Unit {Π Ω _ _}.
Arguments Invocation {_ _ _ _}.

Notation "'⊤ₑ'" := Unit.

Notation "⟨ e₁ , e₂ ⟩ₑ" := (Pair e₁ e₂) : term_scope.

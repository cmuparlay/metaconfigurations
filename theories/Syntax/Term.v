From stdpp Require Import base gmap.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
From Metaconfigurations Require Import Object Process.

Variant bop : Set :=
  | Add
  | Sub
  | Mul
  | And
  | Or.

Variant uop : Set := Not.

Inductive t (Π Ω : Type) (π : Π) `{Process Π} `{Object Π Ω} : Type :=
  | Var (x : register_names π)
  | Invoke (ω : Ω) (op : (type ω).(OP Π)) (arg : t Π Ω π)
  | Bop (op : bop) (e₁ : t Π Ω π) (e₂ : t Π Ω π)
  | Uop (op : uop) (e : t Π Ω π)
  | Pair (e₁ : t Π Ω π) (e₂ : t Π Ω π)
  | ProjL (e : t Π Ω π)
  | ProjR (e : t Π Ω π)
  | Int (n : Z)
  | Bool (b : bool)
  | Unit.

Arguments Var {Π Ω π _ _ _}.
Arguments Invoke {Π Ω π _ _ _}.
Arguments Bop {Π Ω π _ _ _}.
Arguments Uop {Π Ω π _ _ _}.
Arguments Pair {Π Ω π _ _ _}.
Arguments ProjL {Π Ω π _ _ _}.
Arguments ProjR {Π Ω π _ _ _}.
Arguments Int {Π Ω π _ _ _}.
Arguments Bool {Π Ω π _ _ _}.
Arguments Unit {Π Ω π _ _ _}.

Notation "'⊤ₑ'" := Unit.

Notation "⟨ e₁ , e₂ ⟩ₑ" := (Pair e₁ e₂).

From stdpp Require Import base gmap.
Require Import Coq.Classes.SetoidDec.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Decidable.

Inductive t :=
  | Int (n : Z)
  | Bool (b : bool)
  | Unit
  | Pair (σ : t) (τ : t).

Coercion Int : Z >-> t.
Coercion Bool : bool >-> t.

Notation "'⊤ᵥ'" := Unit.

Declare Scope value_scope.

Notation "⟨ v₁ , v₂ ⟩ᵥ" := (Pair v₁ v₂) : value_scope.


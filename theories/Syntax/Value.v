From stdpp Require Import base gmap.
Require Import Coq.Classes.SetoidDec.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Decidable.

Inductive t :=
  | Int (n : Z)
  | Bool (b : bool)
  | Unit
  | Pair (σ : t) (τ : t).

Coercion Int : Z >-> t.
Coercion Bool : bool >-> t.

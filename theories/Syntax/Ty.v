From stdpp Require Import base gmap.
Require Import Coq.Lists.List.

Inductive t : Type := 
  | Int 
  | Bool 
  | Unit
  | Prod (σ : t) (τ : t).

Notation "τ₁ × τ₂" := (Prod τ₁ τ₂) (at level 80).
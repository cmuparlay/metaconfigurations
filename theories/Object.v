From stdpp Require Import base gmap.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Strings.String.
From Metaconfigurations.Syntax Require Import Value Ty.
From Metaconfigurations.Statics Require Import Value.

Record object_type := {
  Σ : Type;
  OP : Type;
  ARG : OP → Ty.t;
  RES : OP → Ty.t;
  δ : Σ → ∀ op, V⟦ ARG op ⟧ → V⟦ RES op ⟧;
}.

Class Object (Ω : Type) := {
  type : Ω → object_type;
}.

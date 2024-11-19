From stdpp Require Import base gmap.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Strings.String.
From Metaconfigurations.Syntax Require Import Value Ty.
From Metaconfigurations.Statics Require Import Value.

Record object_type (Π : Type) := {
  Σ : Type;
  OP : Type;
  ARG : OP → Ty.t;
  RES : OP → Ty.t;
  δ : Σ → Π → ∀ op, V⟦ ARG op ⟧ → V⟦ RES op ⟧;
}.

Class Object (Π : Type) (Ω : Type) := {
  type : Ω → object_type Π;
  (* state : ∀ (ω : Ω), (type ω).(Σ Π) *)
}.
From stdpp Require Import base gmap.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Strings.String.
From Metaconfigurations.Syntax Require Import Value.

Record object_type (Π : Type) := {
  Σ : Type;
  OP : Type;
  δ : Σ → Π → OP → Value.t → Σ → Value.t → Prop;
}.

Arguments Σ {_}.
Arguments OP {_}.
Arguments δ {_}.

Class Object (Π : Type) (Ω : Type) `{EqDecision Ω} := type : Ω → object_type Π.

Instance augmentation_Object (Ω Ω' Π : Type) `{Object Π Ω, Object Π Ω'} : Object Π (Ω + Ω') :=
  λ obj,
    match obj with
    | inl ω => type ω
    | inr ω => type ω
    end.

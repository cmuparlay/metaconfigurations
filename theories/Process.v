From stdpp Require Import base decidable.
From Metaconfigurations.Syntax Require Import Value.

Class Process (Π : Type) := {
  register_names : Π → Type;
  eq_dec π : EqDecision (register_names π);
}.

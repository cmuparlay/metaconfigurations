From stdpp Require Import base.

Class Process (Π : Type) := {
  register_names : Π → Type;
}.

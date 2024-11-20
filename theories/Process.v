From stdpp Require Import base decidable gmap.
From Metaconfigurations Require Import Syntax.Value Map.

Class Process (Π : Type) := {
  register_names : Π → Type;
  eq_dec π : EqDecision (register_names π);
  countable π : Countable (register_names π);
}.

Module RegisterFile.
  Definition t {Π} `{Process Π} (π : Π) := @gmap (register_names π) (eq_dec π) (countable π) Value.t.
End RegisterFile.

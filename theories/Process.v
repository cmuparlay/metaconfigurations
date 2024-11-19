From stdpp Require Import base.
From Metaconfigurations.Syntax Require Import Value.

Class Process (Π : Type) := {
  register_names : Π → Type;
  eq_dec_register_names π (r r' : register_names π) : {r = r'} + {r ≠ r'};
}.

Module RegisterFile.
  Section RF.

    Context {Π : Type} `{Process Π}.

    Variable (π : Π).

    Definition t := register_names π → Value.t.

    Definition rebind : register_names π → Value.t → t → t.
    Proof.
      intros r v m r'. destruct (eq_dec_register_names π r r').
      - exact v.
      - exact (m r').
    Defined.

    Definition lookup (r : register_names π) (m : t) : Value.t := m r.

    Definition init : t := λ _, ⊤ᵥ.

    Theorem lookup_rebind_same k v m : lookup k (rebind k v m) = v.
    Proof.
      unfold lookup, rebind. now destruct (eq_dec_register_names π k k).
    Qed.

    Theorem lookup_rebind_diff k k' v m : k ≠ k' → lookup k' (rebind k v m) = lookup k' m.
    Proof.
      intros. unfold lookup, rebind. now destruct (eq_dec_register_names π k k').
    Qed.
  End RF.

End RegisterFile.

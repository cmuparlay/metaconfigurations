From stdpp Require Import base decidable.

Section Map.

  Variable K V : Type.

  Context `{EqDecision K}.

  Definition t := K → V.

  Definition rebind : K → V → t → t.
  Proof.
    intros k v m k'. unfold EqDecision in *. destruct (decide (k = k')).
    - exact v.
    - exact (m k').
  Defined.

  Definition lookup (k : K) (m : t) : V := m k.

  Definition with_default (d : V) : t := λ _, d.

  Theorem lookup_rebind_same k v m : lookup k (rebind k v m) = v.
  Proof.
    unfold lookup, rebind. now destruct (decide (k = k)).
  Qed.

  Theorem lookup_rebind_diff k k' v m : k ≠ k' → lookup k' (rebind k v m) = lookup k' m.
  Proof.
    intros. unfold lookup, rebind. now destruct (decide (k = k')).
  Qed.

End Map.

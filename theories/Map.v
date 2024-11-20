From stdpp Require Import base decidable.
Require Import Program.

Definition dependent (K : Type) (V : K → Type) := ∀ k : K, V k.

Definition rebind {K : Type} {V : K → Type} `{EqDecision K} : 
  ∀ k : K, V k → dependent K V → dependent K V.
Proof.
  intros k v m k'. unfold EqDecision in *. destruct (decide (k = k')).
  - destruct e. exact v.
  - exact (m k').
Defined.

Definition lookup {K : Type} {V : K → Type} `{EqDecision K} (k : K) (m : dependent K V) : V k := m k.

Theorem lookup_rebind_same {K : Type} {V : K → Type} `{EqDecision K} (k : K) (v : V k) (m : dependent K V) : 
  lookup k (rebind k v m) = v.
Proof.
  destruct (decide (k = k)); cbv; 
  destruct (EqDecision0 k k); intuition.
  dependent destruction e0. reflexivity.
Qed.

Theorem lookup_rebind_diff {K : Type} {V : K → Type} `{EqDecision K} (k k' : K) (v : V k) (m : dependent K V) 
  : k ≠ k' → lookup k' (rebind k v m) = lookup k' m.
Proof.
  intros. unfold lookup, rebind. now destruct (decide (k = k')).
Qed.

Definition t (K V : Type) := dependent K (λ _, V).

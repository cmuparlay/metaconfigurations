From stdpp Require Import base decidable.
Require Import Program.

Definition dependent (K : Type) (V : K → Type) : Type := ∀ k : K, V k.

Definition insert {K : Type} {V : K → Type} `{EqDecision K} : 
  ∀ k : K, V k → dependent K V → dependent K V.
Proof.
  intros k v m k'. unfold EqDecision in *. destruct (decide (k = k')).
  - destruct e. exact v.
  - exact (m k').
Defined.

Definition lookup {K : Type} {V : K → Type} `{EqDecision K} (k : K) (m : dependent K V) : V k := m k.

Module Dep.

Theorem lookup_insert {K : Type} {V : K → Type} `{EqDecision K} (k : K) (v : V k) (m : dependent K V) : 
  lookup k (insert k v m) = v.
Proof.
  destruct (decide (k = k)); cbv; 
  destruct (EqDecision0 k k); intuition.
  dependent destruction e0. reflexivity.
Qed.

Theorem lookup_insert_ne {K : Type} {V : K → Type} `{EqDecision K} (k k' : K) (v : V k) (m : dependent K V) 
  : k ≠ k' → lookup k' (insert k v m) = lookup k' m.
Proof.
  intros. unfold lookup, insert. now destruct (decide (k = k')).
Qed.

Lemma insert_insert `{EqDecision K} {V : K → Type} (k : K) (v : V k) (m : dependent K V) :
  insert k (lookup k m) (insert k v m) = m.
Proof.
  extensionality k'. destruct (decide (k = k')).
  - subst. fold (lookup k' (insert k' (lookup k' m) (insert k' v m))).
    now rewrite lookup_insert.
  - fold (lookup k' (insert k (lookup k m) (insert k v m))).
    rewrite lookup_insert_ne by assumption.
    now rewrite lookup_insert_ne.
Qed.

Lemma η `{EqDecision K} {V : K → Type} (k : K) (m : dependent K V) :
  insert k (lookup k m) m = m.
Proof.
  extensionality k'. destruct (decide (k = k')).
  - subst. fold (lookup k' (insert k' (lookup k' m) m)).
    now rewrite lookup_insert.
  - fold (lookup k' (insert k (lookup k m) m)).
    now rewrite lookup_insert_ne by assumption.
Qed.

End Dep.

Definition t (K V : Type) := dependent K (λ _, V).

Instance map_insert K `{EqDecision K} V : Insert K V (t K V) := insert.

Instance map_lookup_total K `{EqDecision K} V : LookupTotal K V (t K V) := lookup.

Definition with_default {K V : Type} (d : V) : t K V := λ _, d.

Lemma η `{EqDecision K} {V} (k : K) (m : t K V) :
  <[k := m !!! k]> m = m.
Proof.
  apply Dep.η.
Qed.

Lemma lookup_insert `{EqDecision K} {V} (k : K) (v : V) (m : t K V) : 
  <[k := v]> m !!! k = v.
Proof.
  destruct (decide (k = k)); cbv; 
  destruct (EqDecision0 k k); intuition.
  dependent destruction e0. reflexivity.
Qed.

Lemma lookup_insert_ne `{EqDecision K} {V} (k k' : K) (v : V) (m : t K V) : 
  k ≠ k' → <[k := v]> m !!! k' = m !!! k'.
Proof.
  intros. unfold base.insert, map_insert, "!!!", map_lookup_total, lookup, insert. now destruct (decide (k = k')).
Qed.

Lemma insert_insert `{EqDecision K} {V} (k : K) (v : V) (m : t K V) : <[k := m !!! k]> (<[k := v]> m) = m.
Proof.
  unfold base.insert, Map.map_insert, "!!!", Map.map_lookup_total. apply Dep.insert_insert.
Qed.


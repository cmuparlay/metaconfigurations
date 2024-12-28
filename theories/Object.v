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

Instance dsig_Object (Ω Π : Type) (P : Ω → Prop) `{∀ x, Decision (P x), Object Π Ω} : Object Π (dsig P).
Proof.
  unfold Object. intros [ω _]. exact (type ω).
Defined.

Variant sing {Ω} (ω : Ω) := Sing.

Instance sing_eq_dec {Ω} (ω : Ω) : EqDecision (sing ω).
Proof. solve_decision. Defined.

Instance sing_object `{Object Π Ω} (ω : Ω) : Object Π (sing ω).
Proof.
  unfold Object. intros obj. destruct obj. exact (type ω).
Defined.

Definition singleton {A : Type} (x : A) : sig (eq x) := exist (eq x) x (eq_refl x).

Instance singleton_object {Ω} Π (ω : Ω) `{Object Π Ω} : Object Π (sig (eq ω)).
Proof.
  unfold Object. intros [? ?]. exact (type ω).
Defined.
From stdpp Require Import base.
From stdpp Require Import base gmap.
Require Import Metaconfigurations.Syntax.Ty.
Require Import Coq.Classes.SetoidDec.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Decidable.
From Metaconfigurations.Syntax Require Import Value Ty.

Reserved Notation "⊢ᵥ v `: τ" (at level 80, no associativity).

Inductive type : Value.t → Ty.t → Prop :=
  | type_int (n : Z) : ⊢ᵥ n `: Ty.Int
  | type_bool (b : bool) : ⊢ᵥ b `: Ty.Bool
  | type_unit : (⊢ᵥ ⊤ᵥ `: Ty.Unit)
  | type_tuple v₁ v₂ τ₁ τ₂ : ⊢ᵥ v₁ `: τ₁ → ⊢ᵥ v₂ `: τ₂ → ⊢ᵥ ⟨ v₁, v₂ ⟩ᵥ `: (τ₁ × τ₂)
where "⊢ᵥ v `: τ" := (type v τ).

Definition with_type τ := { v | ⊢ᵥ v `: τ }.

Notation "V⟦ τ ⟧" := (with_type τ).

Theorem value_well_typed v : ∃ τ, ⊢ᵥ v `: τ.
Proof.
   induction v.
   - econstructor. econstructor.
   - econstructor. econstructor.
   - econstructor. econstructor.
   - inversion IHv1. inversion IHv2. eexists. econstructor; eauto.
Qed.

Theorem type_deterministic v σ τ : ⊢ᵥ v `: σ → ⊢ᵥ v `: τ → σ = τ.
Proof.
   intros Hσ. generalize dependent σ. generalize dependent τ. 
   induction v; intros; inv H; inv Hσ; try f_equal; auto.
Qed.

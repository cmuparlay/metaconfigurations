From stdpp Require Import base.
From stdpp Require Import base gmap.
Require Import Metaconfigurations.Syntax.Ty.
Require Import Coq.Classes.SetoidDec.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Decidable.
From Metaconfigurations.Syntax Require Import Value Ty.

Reserved Notation "v :ᵥ τ" (at level 80, no associativity).

Inductive type : Value.t → Ty.t → Prop :=
  | type_int (n : Z) : n :ᵥ Ty.Int
  | type_bool (b : bool) : b :ᵥ Ty.Bool
  | type_unit : Value.Unit :ᵥ Ty.Unit
  | type_tuple v₁ v₂ τ₁ τ₂ : v₁ :ᵥ τ₁ → v₂ :ᵥ τ₂ → ⟨ v₁, v₂ ⟩ᵥ :ᵥ (τ₁ × τ₂)
where "v :ᵥ τ" := (type v τ).

Definition with_type τ := { v | type v τ }.

Notation "V⟦ τ ⟧" := (with_type τ).

Theorem value_well_typed v : ∃ τ, v :ᵥ τ.
Proof.
   induction v.
   - econstructor. econstructor.
   - econstructor. econstructor.
   - econstructor. econstructor.
   - inversion IHv1. inversion IHv2. eexists. econstructor; eauto.
Qed.

Theorem type_deterministic v σ τ : v :ᵥ σ → v :ᵥ τ → σ = τ.
Proof.
   intros Hσ. generalize dependent σ. generalize dependent τ. 
   induction v; intros; inv H; inv Hσ; try f_equal; auto.
Qed.

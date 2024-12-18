From Metaconfigurations Require Import 
  Map Syntax.Term Syntax.Value Object.
From stdpp Require Import base stringmap decidable.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Global Declare Scope dynamics_scope.

Definition states (Π Ω : Type) `{Object Π Ω} := Map.dependent Ω (Σ Π ∘ type).

Section DisjointUnion.

  Context {Π Ω Ω' : Type}.

  Context `{EqDecision Ω, Object Π Ω, EqDecision Ω', Object Π Ω'}.

  Definition disjoint_union (ϵ : states Π Ω) (ϵ' : states Π Ω') : states Π (Ω + Ω') :=
    λ ω,
      match ω with
      | inl ω => ϵ ω
      | inr ω => ϵ' ω
      end.

  Notation "ϵ ⊎ ϵ'" := (disjoint_union ϵ ϵ').

  Lemma rebind_union_distr ω σ ϵ ϵ' : rebind ω σ ϵ ⊎ ϵ' = rebind (inl ω) σ (ϵ ⊎ ϵ').
  Proof.
    extensionality ω'. destruct ω'.
    - simpl. unfold rebind, disjoint_union. case_decide.
      + destruct H1. case_decide.
        * dependent destruction H1. reflexivity.
        * contradiction.
      + case_decide. 
        * dependent destruction H2. contradiction.
        * reflexivity.
    - simpl. unfold rebind, disjoint_union. case_decide.
      + dependent destruction H1.
      + reflexivity.
  Qed.

  Lemma lookup_union_distr ω ϵ ϵ' : Map.lookup ω ϵ = Map.lookup (inl ω) (ϵ ⊎ ϵ').
  Proof. reflexivity. Qed.

  Lemma union_inj ϵ₁ ϵ₁' ϵ₂ ϵ₂' : ϵ₁ ⊎ ϵ₁' = ϵ₂ ⊎ ϵ₂' → ϵ₁ = ϵ₂ ∧ ϵ₁' = ϵ₂'.
  Proof.
    intros. split; extensionality ω.
    - eapply equal_f_dep with (x := inl ω) in H1. auto. 
    - eapply equal_f_dep with (x := inr ω) in H1. auto.
  Qed.

  Definition πₗ (ϵ : states Π (Ω + Ω')) : states Π Ω := λ ω, ϵ (inl ω).

  Definition πᵣ (ϵ : states Π (Ω + Ω')) : states Π Ω' := λ ω, ϵ (inr ω).

  Lemma πₗ_union ϵ₁ ϵ₂ : πₗ (ϵ₁ ⊎ ϵ₂) = ϵ₁.
  Proof.
    extensionality ω. reflexivity.
  Qed.

  Lemma πᵣ_union ϵ₁ ϵ₂ : πᵣ (ϵ₁ ⊎ ϵ₂) = ϵ₂.
  Proof.
    extensionality ω. reflexivity.
  Qed.

  Lemma union_project ϵ : πₗ ϵ ⊎ πᵣ ϵ = ϵ.
  Proof. extensionality ω. intuition. Qed.

  Lemma πₗ_rebind_comm ω σ ϵ : πₗ (rebind (inl ω) σ ϵ) = rebind ω σ (πₗ ϵ).
  Proof.
    intros. extensionality ω'. unfold rebind. case_decide.
    - subst. cbv. destruct (EqDecision1 ω' ω').
      + dependent destruction e. reflexivity.
      + contradiction.
    - cbv. destruct (EqDecision1 ω ω').
      + contradiction.
      + reflexivity.
  Qed.

  Lemma lookup_πₗ ω ϵ : Map.lookup ω (πₗ ϵ) = Map.lookup (inl ω) ϵ.
  Proof. reflexivity. Qed.

  Lemma rebind_l_πᵣ ω ϵ σ : πᵣ ϵ = πᵣ (rebind (inl ω) σ ϵ).
  Proof. extensionality ω'. reflexivity. Qed.

End DisjointUnion.

Section Eval.

  Context {Π : Type}.

  Context {Ω : Type} `{Object Π Ω}.

  Reserved Notation "⟨ π , Ψ , ϵ , e ⟩ ⇓ₑ ⟨ ϵ' , v ⟩" (at level 80, no associativity).

  Variant eval_binop : Term.bop → Value.t → Value.t → Value.t → Set :=
    | eval_add (n₁ n₂ : Z) : eval_binop Term.Add n₁ n₂ (n₁ + n₂)%Z
    | eval_sub (n₁ n₂ : Z) : eval_binop Term.Sub n₁ n₂ (n₁ - n₂)%Z
    | eval_mul (n₁ n₂ : Z) : eval_binop Term.Mul n₁ n₂ (n₁ * n₂)%Z
    | eval_or (b₁ b₂ : bool) : eval_binop Term.Or b₁ b₂ (b₁ || b₂)
    | eval_and (b₁ b₂ : bool) : eval_binop Term.And b₁ b₂ (b₁ && b₂).

  Variant eval_unop : Term.uop → Value.t → Value.t → Set :=
    | eval_not (b : bool) : eval_unop Term.Not b (negb b).  

    (* match bop, v₁, v₂ with
    | Add, Value.Int n₁, Value.Int n₂ => (n₁ + n₂)%Z
    | Sub, Value.Int n₁, Value.Int n₂ => (n₁ - n₂)%Z
    | Mul, Value.Int n₁, Value.Int n₂ => (n₁ * n₂)%Z
    | 
    end. *)

(* (ω : Ω) (op : (type ω).(OP Π)) (arg : (type ω).(ARG Π) *)

  Variant eval_inv π ϵ ω op arg σ res :=
    | eval_inv_intro :
      (type ω).(δ Π) (Map.lookup ω ϵ) π op arg σ res →
      eval_inv π ϵ ω op arg σ res.

  Inductive eval (π : Π) (ψ : stringmap Value.t) (ϵ : states Π Ω) : Term.t Π Ω → states Π Ω → Value.t → Prop := 
    | eval_var x v :
      ψ !! x = Some v →
      ⟨ π , ψ , ϵ , Var x ⟩ ⇓ₑ ⟨ ϵ , v ⟩
    | eval_invoke ω op arg argᵥ res ϵ' σ :
      ⟨ π , ψ , ϵ , arg ⟩ ⇓ₑ ⟨ ϵ' , argᵥ ⟩ →
      eval_inv π ϵ ω op argᵥ σ res →
      ⟨ π , ψ , ϵ , Invoke ω op arg ⟩ ⇓ₑ ⟨ rebind ω σ ϵ' , res ⟩
    | eval_bop bop e₁ e₂ v₁ v₂ v ϵ₁ ϵ₂ : 
      ⟨ π , ψ , ϵ , e₁ ⟩ ⇓ₑ ⟨ ϵ₁ , v₁ ⟩ →
      ⟨ π , ψ , ϵ₁ , e₂ ⟩ ⇓ₑ ⟨ ϵ₂ , v₂ ⟩ →
      eval_binop bop v₁ v₂ v →
      ⟨ π , ψ , ϵ , Bop bop e₁ e₂ ⟩ ⇓ₑ ⟨ ϵ₂ , v ⟩
    | eval_uop e uop ϵ' v v' :
      ⟨ π , ψ , ϵ , e ⟩ ⇓ₑ ⟨ ϵ' , v ⟩ →
      eval_unop uop v v' → 
      ⟨ π , ψ , ϵ , Uop uop e ⟩ ⇓ₑ ⟨ ϵ' , v' ⟩
    | eval_pair e₁ e₂ v₁ v₂ ϵ₁ ϵ₂ :
      ⟨ π , ψ , ϵ , e₁ ⟩ ⇓ₑ ⟨ ϵ₁ , v₁ ⟩ →
      ⟨ π , ψ , ϵ₁ , e₂ ⟩ ⇓ₑ ⟨ ϵ₂ , v₂ ⟩ →
      ⟨ π , ψ , ϵ , Term.Pair e₁ e₂ ⟩ ⇓ₑ ⟨ ϵ₂ , Pair v₁ v₂ ⟩
    | eval_projl e v₁ v₂ ϵ' :
      ⟨ π , ψ , ϵ , e ⟩ ⇓ₑ ⟨ ϵ' , Pair v₁ v₂ ⟩ →
      ⟨ π , ψ , ϵ , ProjL e ⟩ ⇓ₑ ⟨ ϵ' , v₁ ⟩
    | eval_projr e v₁ v₂ ϵ' :
      ⟨ π , ψ , ϵ , e ⟩ ⇓ₑ ⟨ ϵ' , Pair v₁ v₂ ⟩ →
      ⟨ π , ψ , ϵ , ProjR e ⟩ ⇓ₑ ⟨ ϵ' , v₂ ⟩
    | eval_int n :
      ⟨ π , ψ , ϵ , Term.Int n ⟩ ⇓ₑ ⟨ ϵ , n ⟩
    | eval_bool b :
      ⟨ π , ψ , ϵ , Term.Bool b ⟩ ⇓ₑ ⟨ ϵ , b ⟩
    | eval_unit :
      ⟨ π , ψ , ϵ , ⊤ₑ ⟩ ⇓ₑ ⟨ ϵ , ⊤ᵥ ⟩
  where "⟨ π , ψ , ϵ , e ⟩ ⇓ₑ ⟨ ϵ' , v ⟩" := (eval π ψ ϵ e ϵ' v) : dynamics_scope.
End Eval.
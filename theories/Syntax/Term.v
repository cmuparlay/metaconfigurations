From stdpp Require Import base gmap.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
From Metaconfigurations Require Import Object.

Variant bop : Type :=
  | Add
  | Sub
  | Mul
  | And
  | Or.

Variant uop : Type := Not.

Declare Scope term_scope.

Section Term.

  Variables Π Ω : Type.

  Context `{Object Π Ω}.

  Inductive t : Type :=
    | Var (x : string)
    | Invoke (ω : Ω) (op : (type ω).(OP)) (arg : t)
    | Bop (op : bop) (e₁ : t) (e₂ : t)
    | Uop (op : uop) (e : t)
    | Pair (e₁ : t) (e₂ : t)
    | ProjL (e : t)
    | ProjR (e : t)
    | Int (n : Z)
    | Bool (b : bool)
    | Unit.
    
  Variant invocation : Type := Invocation (ω : Ω) (op : (type ω).(OP)) (arg : t).

End Term.

Arguments Var {Π Ω _ _}.
Arguments Invoke {Π Ω _ _}.
Arguments Bop {Π Ω _ _}.
Arguments Uop {Π Ω _ _}.
Arguments Pair {Π Ω _ _}.
Arguments ProjL {Π Ω _ _}.
Arguments ProjR {Π Ω _ _}.
Arguments Int {Π Ω _ _}.
Arguments Bool {Π Ω _ _}.
Arguments Unit {Π Ω _ _}.
Arguments Invocation {_ _ _ _}.

Inductive free {Π Ω : Type} `{Object Π Ω} : string → t Π Ω → Prop :=
  | free_var x : free x (Var x)
  | free_invoke x ω op arg : free x arg → free x (Invoke ω op arg)
  | free_bop_l x op e₁ e₂ : free x e₁ → free x (Bop op e₁ e₂)
  | free_bop_r x op e₁ e₂ : free x e₂ → free x (Bop op e₁ e₂)
  | free_uop x op e : free x e → free x (Uop op e)
  | free_pair_l x e₁ e₂ : free x e₁ → free x (Pair e₁ e₂)
  | free_pair_r x e₁ e₂ : free x e₂ → free x (Pair e₁ e₂)
  | free_proj_l x e : free x e → free x (ProjL e)
  | free_proj_r x e : free x e → free x (ProjR e).

Fixpoint subst {Π Ω} `{Object Π Ω} (eₓ : t Π Ω) (x : string) (e : t Π Ω) := 
  match e with
  | Var x => eₓ
  | Invoke ω op arg => Invoke ω op (subst eₓ x arg)
  | Bop op e₁ e₂ => Bop op (subst eₓ x e₁) (subst eₓ x e₂)
  | Uop op e => Uop op (subst eₓ x e)
  | Pair e₁ e₂ => Pair (subst eₓ x e₁) (subst eₓ x e₂)
  | ProjL e => ProjL (subst eₓ x e)
  | ProjR e => ProjR (subst eₓ x e)
  | Int _ | Bool _ | Unit => e
  end.

Notation "'⊤ₑ'" := Unit.

Notation "⟨ e₁ , e₂ ⟩ₑ" := (Pair e₁ e₂) : term_scope.

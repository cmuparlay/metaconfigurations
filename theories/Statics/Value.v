From stdpp Require Import base.
Require Import Metaconfigurations.Syntax.Value.

Inductive type : t → Ty.t → Prop :=
  | type_int n : type (Int n) Ty.Int
  | type_bool b : type (Bool b) Ty.Bool
  | type_unit : type Unit Ty.Unit
  | type_tuple vs τs : Forall2 type vs τs → type (Tuple vs) (Ty.Tuple τs).

Definition with_type τ := { v | type v τ }.

Notation "V⟦ τ ⟧" := (with_type τ).

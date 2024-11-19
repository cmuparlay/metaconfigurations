From stdpp Require Import base gmap.
Require Import Coq.Lists.List.

Inductive t : Type := 
  | Int 
  | Bool 
  | Unit
  | Tuple (τs : list t).

Section custom_ind.
  Variable P : t → Prop.

  Hypothesis HInt : P Int.
  Hypothesis HBool : P Bool.
  Hypothesis HUnit : P Unit.
  Hypothesis HTuple : ∀ τs, Forall P τs → P (Tuple τs).

  Definition custom_ind : ∀ τ, P τ :=
    fix f τ : P τ :=
      match τ with
      | Int => HInt
      | Bool => HBool
      | Unit => HUnit
      | Tuple τs =>
        HTuple τs
          (list_ind
              (Forall P) (Forall_nil P)
              (fun τ l H => Forall_cons P τ l (f τ) H) τs)
      end.
End custom_ind.

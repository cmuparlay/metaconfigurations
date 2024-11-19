From stdpp Require Import base gmap.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
From Metaconfigurations Require Import Object Process.

Variant bop : Set :=
  | Add
  | Sub
  | Mul
  | And
  | Or.

Variant uop : Set := Not.

Section Term.

  Variable Π : Type.

  Context `{Process Π}.

  Variable Ω : Type.

  Context `{Object Π Ω}.

  Variable π : Π.

  Inductive t : Type :=
    | Var (x : register_names π)
    | Invoke (ω : Ω) (op : (type ω).(OP Π)) (arg : t)
    | Bop (op : bop) (e₁ : t) (e₂ : t)
    | Uop (op : uop) (e : t)
    | Pair (e₁ : t) (e₂ : t)
    | ProjL (e : t)
    | ProjR (e : t)
    | Int (n : Z)
    | Bool (b : bool)
    | Unit.

End Term.


(* Module Stmt.
  Inductive t : Type :=
    | Seq (s₁ : t) (s₂ : t)
    | Assign (x : string) (e : Expr.t)
    | If (e : Expr.t) (s₁ : t) (s₂ : t)
    (* | While (e : Expr.t) (s : t) *)
    | Goto (l : nat)
    | Return (e : Expr.t)
    | Call (obj : string) (op : string) (es : list t).
End Stmt. *)



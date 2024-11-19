From stdpp Require Import base gmap.
From Metaconfigurations Require Import Syntax.Term Object Process.
Require Import Coq.Strings.String.

Section Stmt.

  Variable Π : Type.

  Context `{Process Π}.

  Variables Ω : Type.

  Context `{Object Π Ω}.

  Variable π : Π.

  Inductive t : Type :=
    | Seq (s₁ : t) (s₂ : t)
    | Assign (x : register_names π) (e : Term.t Π Ω)
    | If (e : Term.t Π Ω) (s₁ : t) (s₂ : t)
    (* | While (e : Expr.t) (s : t) *)
    | Goto (l : nat)
    | Return (e : Term.t Π Ω)
    | Invoke (obj : string) (op : string) (es : list (Term.t Π Ω)).

End Stmt.
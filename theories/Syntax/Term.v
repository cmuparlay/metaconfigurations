From stdpp Require Import base gmap.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Metaconfigurations.Object.

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

  Inductive t : Type :=
    | Var (x : string)
    | Invoke (ω : Ω) (op : (type ω).(OP Π)) (arg : t)
    | Bop (op : bop) (e₁ : t) (e₂ : t)
    | Uop (op : uop) (e : t)
    | Tuple (es : list t)
    | Proj (e : t) (index : nat)
    | Int (n : Z)
    | Bool (b : bool)
    | Unit.

  Section custom_ind.
    Variable P : t → Prop.
    Hypothesis HVar : ∀ x, P (Var x).
    Hypothesis HCall : ∀ ω op e, P e → P (Invoke ω op e).
    Hypothesis HBop : ∀ op e₁ e₂, P e₁ → P e₂ → P (Bop op e₁ e₂).
    Hypothesis HUop : ∀ op e, P e → P (Uop op e).
    Hypothesis HTuple : ∀ es, Forall P es → P (Tuple es).
    Hypothesis HProj : ∀ e n, P e → P (Proj e n).
    Hypothesis HInt : ∀ n, P (Int n).
    Hypothesis HBool : ∀ b, P (Bool b).
    Hypothesis HUnit : P Unit.

    Definition custom_ind : ∀ e, P e :=
      fix f e : P e :=
        let flist (es : list t) : Forall P es :=
          list_ind
            (Forall P) (Forall_nil P)
            (fun e l H => Forall_cons P e l (f e) H) es
        in      
        match e with
        | Var x => HVar x
        | Invoke ω op e => HCall ω op e (f e)
        | Bop op e₁ e₂ => HBop op e₁ e₂ (f e₁) (f e₂)
        | Uop op e => HUop op e (f e)
        | Tuple es => HTuple es (flist es)
        | Proj e n => HProj e n (f e)
        | Int n => HInt n
        | Bool b => HBool b
        | Unit => HUnit
        end.
  End custom_ind.

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



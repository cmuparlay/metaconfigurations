From stdpp Require Import base gmap.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Module Expr.

  Parameter Ω : Type.

  Variant bop : Set :=
    | Add
    | Sub
    | Mul
    | And
    | Or.

  Variant uop : Set := Not.

  Inductive t : Type :=
    | Var (x : string)
    | Call (obj : string) (op : string) (es : list t)
    | Bop (op : bop) (e₁ : t) (e₂ : t)
    | Uop (op : uop) (e : t)
    | Tuple (es : list t)
    | Int (n : Z)
    | Bool (b : bool)
    | Unit.

  Section custom_ind.
    Variable P : t → Prop.
    Hypothesis HVar : ∀ x, P (Var x).
    Hypothesis HCall : ∀ obj op es, Forall P es → P (Call obj op es).
    Hypothesis HBop : ∀ op e₁ e₂, P e₁ → P e₂ → P (Bop op e₁ e₂).
    Hypothesis HUop : ∀ op e, P e → P (Uop op e).
    Hypothesis HTuple : ∀ es, Forall P es → P (Tuple es).
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
        | Call obj op es => HCall obj op es (flist es)
        | Bop op e₁ e₂ => HBop op e₁ e₂ (f e₁) (f e₂)
        | Uop op e => HUop op e (f e)
        | Tuple es => HTuple es (flist es)
        | Int n => HInt n
        | Bool b => HBool b
        | Unit => HUnit
        end.
  End custom_ind.

  Inductive Value : t → Prop :=
    | ValueInt n : Value (Int n)
    | ValueBool b : Value (Bool b)
    | ValueUnit : Value Unit
    | ValueTuple es : Forall Value es → Value (Tuple es).

  Section custom_value_ind.
    Variable P : t → Prop.
    Hypothesis HInt : ∀ n, P (Int n).
    Hypothesis HBool : ∀ b, P (Bool b).
    Hypothesis HUnit : P Unit.
    Hypothesis HTuple : ∀ vs, Forall Value vs → Forall P vs → P (Tuple vs).

    Definition custom_value_ind : ∀ v, Value v → P v :=
      fix f v H :=
        match H with
        | ValueInt n => HInt n
        | ValueBool b => HBool b
        | ValueUnit => HUnit
        | ValueTuple vs Hvs =>
          HTuple vs Hvs
              (Forall_ind
                    (Forall P)
                    (Forall_nil P)
                    (fun (v : t) (l : list t) (Hv : Value v) Hvs Hl => @Forall_cons t P v l (f v Hv) Hl) Hvs)
        end.
  End custom_value_ind.

End Expr.

Module Stmt.
  Inductive t : Type :=
    | Seq (s₁ : t) (s₂ : t)
    | Assign (x : string) (e : Expr.t)
    | If (e : Expr.t) (s₁ : t) (s₂ : t)
    (* | While (e : Expr.t) (s : t) *)
    | Goto (l : nat)
    | Return (e : Expr.t)
    | Call (obj : string) (op : string) (es : list t).
End Stmt.



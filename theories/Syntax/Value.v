From stdpp Require Import base gmap.
Require Import Metaconfigurations.Syntax.Ty.

Inductive t :=
  | Int (n : Z)
  | Bool (b : bool)
  | Unit
  | Tuple (vs : list t).

Section custom_ind.
    Variable P : t → Prop.
    Hypothesis HInt : ∀ n, P (Int n).
    Hypothesis HBool : ∀ b, P (Bool b).
    Hypothesis HUnit : P Unit.
    Hypothesis HTuple : ∀ vs, Forall Value vs → Forall P vs → P (Tuple vs).

    Definition custom_ind : ∀ v, Value v → P v :=
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
  End custom_ind.
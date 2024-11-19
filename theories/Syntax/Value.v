From stdpp Require Import base gmap.
Require Import Metaconfigurations.Syntax.Ty.
Require Import Coq.Classes.SetoidDec.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Decidable.

Inductive t :=
  | Int (n : Z)
  | Bool (b : bool)
  | Unit
  | Tuple (vs : list t).

Section custom_ind.
  Variable P : t → Set.
  Hypothesis HInt : ∀ n, P (Int n).
  Hypothesis HBool : ∀ b, P (Bool b).
  Hypothesis HUnit : P Unit.
  Hypothesis HTuple : ∀ vs, Forall P vs → P (Tuple vs).

  Definition custom_ind : ∀ v, P v :=
    fix f v : P v :=
      let flist (vs : list t) : Forall P vs :=
        list_ind
          (Forall P) (Forall_nil P)
          (fun v l H => Forall_cons P v l (f v) H) vs
      in      
      match v with
      | Int n => HInt n
      | Bool b => HBool b
      | Unit => HUnit
      | Tuple vs => HTuple vs (flist vs)
      end.
End custom_ind.

Lemma eq_dec (v v' : t) : decidable (v = v').
Proof.
  generalize dependent v'. unfold decidable. 
  induction v using custom_ind;
  destruct v'; auto.
  - destruct (Z.eq_dec n n0).
    + left. congruence.
    + right. intuition. injection H. assumption.
  - destruct (bool_eq_dec b b0).
    + left. congruence.
    + right. intuition. injection H. assumption.
  - generalize dependent vs0. induction H.
    + destruct vs0; auto.
    + destruct vs0. auto. 
      destruct (H t0), (IHForall vs0).
      * left. congruence.
      * right. intuition. injection H3. intros. apply H2. congruence.
      * right. intuition. injection H3. auto.
      * right. intuition. injection H3. auto.
Defined.

Check

Lemma eq_dec_nst : forall n m : nat, {n = m} + {n <> m}.
Proof.
  intro n; induction n as [|n IHn]. intro m; destruct m as [|m].
  - now left.
  - now right.
  - now right.
  - destruct (IHn m); [left|right]; auto.
Defined.

Unset Printing Notations.

Program Instance t_eqdec : EqDec (eq_setoid t) := {
  equiv_dec :=
    fun v v' =>
      match eq_dec v v' with
      | or_introl P => left P
      | or_intror P => right P
      end
}.

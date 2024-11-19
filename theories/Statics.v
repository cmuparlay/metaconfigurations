(* Lays out statics of language *)

From stdpp Require Import base.

Declare Scope type_scope.

Require Import Metaconfigurations.Dynamics.
Require Import Metaconfigurations.Syntax.

Reserved Notation "e ⊢ 'v' '∈' 'τ'" (at level 80, no associativity).

Inductive type_value : Expr.t → Ty.t → Prop :=
   | type_int n : type_value (Expr.Int n) Ty.Int
   | type_bool b : type_value (Expr.Bool b) Ty.Bool
   | type_unit : type_value Expr.Unit Ty.Unit
   | type_tuple vs τs : 
      Forall2 type_value vs τs → type_value (Expr.Tuple vs) (Ty.Tuple τs).

Ltac inv H := inversion H; clear H; subst.

(* Check Forall2_ind. *)

Section TypeValueInd.
   Variable P : Expr.t → Ty.t → Prop.
   Hypothesis HInt : ∀ n, P (Expr.Int n) Ty.Int.
   Hypothesis HBool : ∀ b, P (Expr.Bool b) Ty.Bool.
   Hypothesis HUnit : P Expr.Unit Ty.Unit.
   Hypothesis HTuple : 
      ∀ vs τs, 
         Forall2 type_value vs τs → Forall2 P vs τs → P (Expr.Tuple vs) (Ty.Tuple τs).

   Definition custom_type_value_ind : ∀ e τ, type_value e τ → P e τ :=
    fix f e τ H :=
      match H with
      | type_int n => HInt n
      | type_bool b => HBool b
      | type_unit => HUnit
      | type_tuple vs τs Hvs =>
         HTuple vs τs Hvs
            (Forall2_ind
                  (Forall2 P)
                  (Forall2_nil _)
                  (fun _ _ _ _ het _ => Forall2_cons _ _ (f _ _ het)) Hvs)
      end.
End TypeValueInd.


Theorem value_well_typed v : Expr.Value v → ∃ τ, type_value v τ.
Proof.
   intros. induction H using Expr.custom_value_ind.
   - econstructor. econstructor.
   - econstructor. econstructor.
   - econstructor. econstructor.
   - induction vs.
      + repeat econstructor.
      + inv H. inv H0. inv H2. intuition. 
        inv H1. inv H0. eexists. econstructor.
        econstructor; eauto.
Qed.

Theorem type_deterministic v σ τ : type_value v σ → type_value v τ → σ = τ.
Proof.
   intros Hσ. generalize dependent τ. induction Hσ using custom_type_value_ind.
   - intros. inv H. reflexivity.
   - intros. inv H. reflexivity.
   - intros. inv H. reflexivity.
   - induction H.
     + intros. inv H. inv H0. inv H2. reflexivity.
     + intros. inversion H2. inv H0. inv H4. repeat f_equal; intuition.
       assert (type_value (Expr.Tuple l) (Ty.Tuple l'0)).
       { constructor. assumption. }
       apply H0 in H3. inv H3. reflexivity.
Qed.

        




From stdpp Require Import base list.
From Metaconfigurations.Syntax Require Import Value Term Stmt.

From Metaconfigurations Require Import 
  Map Syntax.Term Syntax.Stmt Syntax.Ty 
  Syntax.Value Statics.Value 
  Dynamics.Term Object Process.
From stdpp Require Import base.
Require Import Coq.ZArith.BinInt.

From Metaconfigurations.Dynamics Require Import Term Stmt.


Section Procedure.
  Variable Π : Type.

  Context `{Process Π}.

  (* Type of implemented object *)
  Variable Ω₀ : Type.

  (* The object being implemented *)
  Variable ω : Ω₀.

  Context `{Object Π Ω₀}.

  (* Set of base objects *)
  Variable Ω : Type.

  (* Context `{EqDecision Ω}. *)

  Context `{Object Π Ω}.

  Definition procedure (π : Π) := list (Stmt.t Ω π).

  Record Implementation := 
  {
    (* Initial states for every base object *)
    inital_states : states;
    (* Assignment from every process π and operation OP to a procedure *)
    procedures π op : V⟦ (type ω).(ARG Π) op ⟧ → procedure π;
  }.

  Variant control :=
    | Next (l : nat) 
    | Return (v : Value.t)

  Record frame π := {
    pc : nat;
    proc : procedure π;
  }.

  Record configuration := {
    outstanding π : option (frame π);
    ψ π : RegisterFile.t π;
    ϵ : states;
  }.

  Section Run.

    Variable impl : Implementation.

    Variant line (π : Π) :=
      | Invoke (op : (type ω).(OP Π)) (arg : Value.t)
      | Intermediate
      | Response (resp : Value.t).

    Local Open Scope stmt_scope.

    Inductive step : configuration → ∀ π : Π, line π → configuration → Prop :=
    | step_intermediate c π c' s ψ' ϵ' pc pc' (proc : procedure π) :
      (* If process [π] has an outstanding request for proecedure [proc], interrupted at line [pc] *)
      c.(outstanding) π = Some {| pc := pc; proc := proc |} →
      (* And [pc] points to line containing statement [s] in [proc] *)
      proc !! pc = Some s →
      (* And *)
      Stmt.eval (c.(ψ) π) c.(ϵ) s ψ' ϵ' (Goto pc') →
      step c π Intermediate {| outstanding |}
      (⟨ ψ , ϵ , s ⟩ ⇓ₛ ⟨ ψ' , ϵ' , sig ⟩)%stmt_scope →
      (⟨ (c.(ψ) π) , (c.(ϵ)) , s ⟩ ⇓ₛ ⟨ Ψ' , ϵ' , sig ⟩)%stmt_scope →
      step c π c'
      impl.(procedures) π !! c.(pc) π = Some l → step.
      
      Stmt.eval (c.(ψ) π) (c.(arg) pi c.(ϵ) l ψ ϵ → step .

  End Run.

  Inductive run :=
    | Initial (c : configuration)
    | Step (r : run) (π : Π) (c : configuration).

  Definition final r :=
    match r with
    | Initial c | Step _ _ c => c
    end.

  Inductive step : configuration → Π → configuration → Prop :=
    | step_intro c π c' :

      Stmt.eval (c.(registers) π) c.(arg) (c.(pc) π)
     

  Inductive run_wf : run → Prop :=
    | Initial_wf c : run_wf (Initial c)
    | Step_wf r π c : run_wf r →

  Reserved Notation "⟨ Ψ , ϵ , Φ , pc ⟩ ⇓ₛ ⟨ Ψ' , ϵ' , sig ⟩" (at level 80, no associativity).

End Procedure.
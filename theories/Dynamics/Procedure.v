From Metaconfigurations.Syntax Require Import Value Term Stmt.

From Metaconfigurations Require Import 
  Map Syntax.Term Syntax.Stmt
  Syntax.Value
  Dynamics.Term Object.

From Metaconfigurations.Dynamics Require Import Term Stmt.
From stdpp Require Import base decidable list stringmap gmap fin_maps.

Record frame Π {Ω} `{Object Π Ω} (ω : Ω) : Type := {
  op : (type ω).(OP);
  pc : nat;
  arg : Value.t;
  registers : stringmap Value.t;
}.

Arguments op {_ _ _ _ _}.
Arguments pc {_ _ _ _ _}.
Arguments arg {_ _ _ _ _}.
Arguments registers {_ _ _ _ _}.

Variant signal Π {Ω} `{Object Π Ω} ω :=
  | Next (f : frame Π ω) (* On next step, go to line [l] *)
  | Return (v : Value.t). (* Procedure has returned with value [v] *)

Arguments Next   {_ _ _ _ _}.
Arguments Return {_ _ _ _ _}.

Record Implementation (Π Ω : Type) {Ω₀} `{Object Π Ω₀, Object Π Ω} (ω : Ω₀) := {
  initial_state : (type ω).(Σ);
  (* Initial states for every base object *)
  initial_states : states Π Ω;
  (* Assignment from every process π and operation OP to a procedure *)
  procedures : (type ω).(OP) → list (Stmt.t Π Ω);
}.

Arguments initial_state : default implicits.
Arguments initial_states : default implicits.
Arguments procedures : default implicits.

Local Open Scope dynamics_scope.

Definition atomic_implementation {Π Ω} `{Object Π Ω} (ω : Ω) (ϵ₀ : (type ω).(Σ)) : Implementation Π (sing ω) ω.
Proof.
  split.
  - exact ϵ₀.
  - unfold states, dependent. intros. destruct k. simpl. exact ϵ₀.
  - intros op. 
    + (* body *) exact
      [
        Assign "r" (Term.Invoke (Sing ω) op (Var "arg"));
        Syntax.Stmt.Return (Var "r")
      ].
Defined.

Variant line Π {Ω} `{Object Π Ω} (ω : Ω) :=
  | Invoke (op : (type ω).(OP)) (arg : Value.t)
  | Intermediate
  | Response (resp : Value.t).

Arguments Invoke {_ _ _ _ _}.
Arguments Intermediate {_ _ _ _ _}.
Arguments Response {_ _ _ _ _}.

Variant status Π {Ω} `{Object Π Ω} (ω : Ω) :=
  | Idle
  | Pending (op : (type ω).(OP)) (arg : Value.t)
  | Linearized (res : Value.t).

Arguments Idle {_ _ _ _ _}.
Arguments Pending {_ _ _ _ _}.
Arguments Linearized {_ _ _ _ _}.

Instance idle_eq_dec Π {Ω} `{Object Π Ω} {ω : Ω} (x : status Π ω) : Decision (x = Idle).
Proof. destruct x; now constructor. Qed.

Definition refines A B : relation (A → B → Prop) := λ P Q, ∀ x y, P x y → Q x y.

Instance refines_Preorder A B : PreOrder (refines A B).
Proof.
  split; firstorder.
Qed.

(* Instance refines_Reflexive A B : Reflexive (refines A B).
Proof. firstorder. Defined.

Instance refines_Transitive A B : Transitive (refines A B).
Proof. firstorder. Defined. *)

Instance relation_SubsetEq A B : SubsetEq (A → B → Prop) := refines A B.

Instance relation_SqSubsetEq A B : SqSubsetEq (A → B → Prop) := refines A B.

Definition monotone `{SqSubsetEq A, SqSubsetEq B} (f : A → B) := ∀ x y : A, x ⊑ y → f x ⊑ f y.

(* Inductive list (A : Type) : Type :=
  | Nil
  | Snoc (h : list A) (t : A).

Arguments Nil {_}.
Arguments Snoc {_}.

Notation "[]" := Nil (format "[]") : list_scope.
Notation "⟨ x ⟩" := (Snoc Nil x) : list_scope.
Notation "⟨ x ; y ; .. ; z ⟩" := (Snoc .. (Snoc (Snoc Nil x) y) .. z) : list_scope. *)

Notation "l ,, x" := (x :: l) (at level 50, left associativity).

(* Lemma not_in_neq {A} (x y : A) (xs : list A) : y ∉ xs ,, x → y ≠ x ∧ y ∉ xs.
Proof.
  unfold not. intros H. split.
  + intros Heq. apply H. cbn. now right.
  + intros Hin. apply H. cbn. now left.
Qed.

Lemma snoc_in_iff_list_in {A} (x : A) (l : list A) : x ∈ l ↔ x ∈ list_of_list l.
Proof.
  revert x. induction l.
  - intros x. split.
    + intros Hmem. inv Hmem.
    + cbn. tauto.
  - cbn. intros x. split.
    + set_unfold. intros [Heq | Hmem].
      * now right.
      * left. now apply IHl.
    + intros [Hmem | Heq].
      * right. now apply IHl.
      * set_unfold. now left.
Qed. *)

Inductive δ_multi {Π Ω} `{EqDecision Π, Object Π Ω} {ω : Ω} : (type ω).(Σ) → (Π → status Π ω) → list Π → (type ω).(Σ) → (Π → status Π ω) → Prop :=
  | δ_multi_refl σ f : δ_multi σ f [] σ f
  | δ_multi_step f σ π πs op arg σ' res σ'' f' :
    δ_multi σ (f : Π → status Π ω) πs σ' (f' : Π → status Π ω) →
    (* if [π] has invoked [op(arg)], but not returned *)
    f' !!! π = Pending op arg →
    (* And (σ', res) ∈ δ(σ, π, op, arg) *)
    (type ω).(δ) σ' π op arg σ'' res →
    δ_multi σ f (πs ,, π) σ'' (<[π := Linearized res]>f').

Lemma δ_multi_mod `{EqDecision Π, Object Π Ω} {ω : Ω} (σ σ' : (type ω).(Σ)) (f f' : Π → status Π ω) (πs : list Π) (π : Π) (v : status Π ω) :
  π ∉ πs → δ_multi σ f πs σ' f' → δ_multi σ (<[π := v]>f) πs σ' (<[π := v]>f').
Proof.
  revert σ' f'. induction πs.
  - intros σ' f' Hnotin Hstep. inv Hstep. constructor.
  - intros σ' f' Hnotin Hstep. set_unfold in Hnotin. apply Decidable.not_or in Hnotin as [Hneq Hnotin].
    inv Hstep. rewrite Map.insert_comm at 1 by auto. econstructor; eauto.
    now rewrite Map.lookup_insert_ne at 1.
Qed.

Definition invoke `{EqDecision Π, Object Π Ω} {ω} (f : Π → status Π ω) (π : Π) (op : (type ω).(OP)) (arg : Value.t) : Π → status Π ω :=
  Map.insert π (Pending op arg) f.

Definition ret `{EqDecision Π, Object Π Ω} {ω} (f : Π → status Π ω) (π : Π) := Map.insert π Idle f.

(* A meta configuration relates states of the implemented object and the status of each process *)
Definition meta_configuration Π {Ω} `{Object Π Ω} (ω : Ω) := (type ω).(Σ) → (Π → status Π ω) → Prop.

Definition inhabited {A B} (R : A → B → Prop) : Prop := ∃ a b, R a b.

Definition singleton {A B} (R : A → B → Prop) (x : A) (y : B) : Prop :=
  R x y ∧ ∀ x' y', R x' y' → x = x' ∧ y = y'.

Variant map {A B C D} (f : A → B → (C * D)%type) (P : A → B → Prop) : C → D → Prop :=
  | map_intro a b c d :
    P a b →
    f a b = (c, d) →
    map f P c d.

Variant filter_map {A B C D} (f : A → B → option (C * D)%type) (P : A → B → Prop) : C → D → Prop :=
  | filter_map_intro a b c d :
    P a b →
    f a b = Some (c, d) →
    filter_map f P c d.

Variant evolve_inv `{EqDecision Π, Object Π Ω} {ω : Ω} (π : Π) op arg (C : meta_configuration Π ω) : meta_configuration Π ω :=
  | evolve_inv_intro σ f :
    C σ f →
    f !!! π = Idle →
    evolve_inv π op arg C σ (invoke f π op arg).

Variant evolve_ret `{EqDecision Π, Object Π Ω} {ω : Ω} (π : Π) v (C : meta_configuration Π ω) : meta_configuration Π ω :=
  | evolve_ret_intro σ f :
    C σ f →
    f !!! π = Linearized v →
    evolve_ret π v C σ (ret f π).

Variant linearize_pending `{EqDecision Π, Object Π Ω} {ω : Ω} (C : meta_configuration Π ω) : meta_configuration Π ω :=
  | linearize_pending_intro σ f πs σ' f' :
    C σ f →
    δ_multi σ f πs σ' f' →
    linearize_pending C σ' f'.

Definition evolve `{EqDecision Π, Object Π Ω} {ω : Ω} (π : Π) (l : line Π ω) (C : meta_configuration Π ω) : meta_configuration Π ω :=
  match l with
  | Invoke op arg =>
    linearize_pending (evolve_inv π op arg C)
  | Intermediate =>
    linearize_pending C
  | Response v => 
    linearize_pending (evolve_ret π v C)
  end.
(* 
Variant evolve `{EqDecision Π, Object Π Ω} {ω : Ω} (π : Π) : line Π ω → meta_configuration Π ω → meta_configuration Π ω :=
  | evolve_inv C op arg σ f πs σ' f' :
    (* If (σ, f) ∈ C *)
    C σ f →
    f !!! π = Idle →
    (* And atomic configuration (σ', f') results after linearizing every outstanding operation of [πs] *)
    δ_multi σ (invoke f π op arg) πs σ' f' →
    (* Then (σ', f') is in the resulting metaconfiguration *)
    evolve π (Invoke op arg) C σ' f'
  | evolve_intermediate C σ f πs σ' f' :
    (* If (σ, f) ∈ C *)
    C σ f →
    (* And atomic configuration (σ', f') results after linearizing every outstanding operation of [πs] *)
    δ_multi σ f πs σ' f' →
    (* Then (σ', f') is in the resulting metaconfiguration *)
    evolve π Intermediate C σ' f'
  | evolve_ret C res σ f πs σ' f' :
    f !!! π = Linearized res →
    (* If (σ, f) ∈ C *)
    C σ f →
    (* And atomic configuration (σ', f') results after linearizing every outstanding operation of [πs] *)
    δ_multi σ (ret f π) πs σ' f' →
    (* Then (σ', f') is in the resulting metaconfiguration *)
    evolve π (Response res) C σ' f'. *)

(* Variant evolve_intermediate Π `{EqDecision Π, Object Π Ω} (ω : Ω) (C : meta_configuration Π ω) : meta_configuration Π ω :=
  evolve_intermediate_intro σ f πs σ' f' :
    (* If (σ, f) ∈ C *)
    C σ f →
    (* And atomic configuration (σ', f') results after linearizing every outstanding operation of [πs] *)
    δ_multi σ f πs σ' f' →
    (* Then (σ', f') is in the resulting metaconfiguration *)
    evolve_intermediate Π ω C σ' f'. *)

Lemma evolve_monotone `{EqDecision Π, Object Π Ω} {ω : Ω} (π : Π) (l : line Π ω) : monotone (evolve π l).
Proof.
  unfold monotone. intros C C' Hrefines σ f Hevolve. destruct l; cbn in *.
  - inv Hevolve. inv H0. repeat (econstructor; eauto).
  - inv Hevolve. econstructor; eauto.
  - inv Hevolve. inv H0. repeat (econstructor; eauto).
Qed.

(* Variant evolve_ret `{EqDecision Π, Object Π Ω} (ω : Ω) (π : Π) (res : Value.t) (C : meta_configuration Π ω) : meta_configuration Π ω :=
  evolve_ret_intro σ f πs σ' f' :
    f !!! π = Linearized res →
    (* If (σ, f) ∈ C *)
    C σ f →
    (* And atomic configuration (σ', f') results after linearizing every outstanding operation of [πs] *)
    δ_multi σ (ret f π) πs σ' f' →
    (* Then (σ', f') is in the resulting metaconfiguration *)
    evolve_ret ω π res C σ' f'.

Lemma evolve_ret_monotone `{EqDecision Π, Object Π Ω} (ω : Ω) (π : Π) (res : Value.t) : monotone (evolve_ret ω π res).
Proof.
  unfold monotone. intros x y Hless.
  intros σ f Hevolve. inv Hevolve. econstructor; eauto.
Qed. *)

(* Definition atomic_run {Π Ω} `{Countable Π, Object Π Ω} (ϵ : states Π Ω) (ω : Ω) (l : line ω) : list (Π * line) :=
  Run (atomic_implementation ϵ ω). *)

Inductive run (C Π : Type) `{Object Π Ω} (ω : Ω) :=
  | Initial (c : C)
  | Step (r : run C Π ω) (π : Π) (l : line Π ω) (c : C).

Arguments Initial {_ _ _ _ _ _}.
Arguments Step {_ _ _ _ _ _}.

Inductive prefix (C Π : Type) `{Object Π Ω} (ω : Ω) : run C Π ω → run C Π ω → Prop :=
  | prefix_refl r : prefix C Π ω r r
  | prefix_trans r r' π l c : prefix C Π ω r r' → prefix C Π ω r (Step r' π l c).

Instance prefix_Preorder (C Π : Type) `{Object Π Ω} (ω : Ω) : PreOrder (prefix C Π ω).
Proof.
  split.
  - unfold Reflexive. constructor.
  - unfold Transitive. intros r₁ r₂ r₃ H₁ H₂. generalize dependent r₁.
    induction H₂.
    + tauto.
    + intros. econstructor. auto.
Qed.

Instance run_SubsetEq (C Π : Type) `{Object Π Ω} (ω : Ω) : SqSubsetEq (run C Π ω) := prefix C Π ω.

Fixpoint behavior {C Π : Type} `{Object Π Ω} {ω : Ω} (r : run C Π ω) : list (Π * line Π ω) :=
  match r with
  | Initial _ => []
  | Step r π l c =>
      match l with
      | Invoke _ _ | Response _ => behavior r ,, (π, l)
      | Intermediate => behavior r
      end
  end.

Inductive subsequence {A : Type} : list A → list A → Prop :=
  | subsequence_refl l : subsequence l l
  | subsequence_trans l h t : subsequence l h → subsequence l (h ,, t).

Definition final {C Π : Type} `{Countable Π, Object Π Ω} {ω : Ω} (r : run C Π ω) :=
  match r with
  | Initial c | Step _ _ _ c => c
  end.

Definition sem (C Π : Type) `{Countable Π, Object Π Ω} (ω : Ω) := C → Π → line Π ω → C → Prop.

Inductive Run {C Π : Type} `{Countable Π, Object Π Ω} {ω : Ω} (c₀ : C) (step : sem C Π ω) : run C Π ω → Prop :=
  | RunInitial : Run c₀ step (Initial c₀)
  | RunStep r π l c : Run c₀ step r → step (final r) π l c → Run c₀ step (Step r π l c).

(** [invariant P] is true iff [P] is true for the final configuration of every run *)
Definition invariant {C Π : Type} `{Countable Π, Object Π Ω} {ω : Ω} (c₀ : C) (step : sem C Π ω) (P : _ → Prop) : Prop := ∀ r, Run c₀ step r → P (final r).

Module Atomic.
  Definition configuration (Π : Type) `{Countable Π, Object Π Ω} (ω : Ω) := ((type ω).(Σ) * (Π → status Π ω))%type.

  Definition run (Π : Type) `{Countable Π, Object Π Ω} (ω : Ω) := run (configuration Π ω) Π ω.

  Inductive step `{Countable Π, Object Π Ω} {ω : Ω} : configuration Π ω → Π → line Π ω → configuration Π ω → Prop :=
    | step_invoke σ f π op arg :
      (* If [π] has no outstanding operations*)
      f !!! π = Idle →
      (* Then π can invoke an operation on the shared object *)
      step (σ, f) π (Invoke op arg) (σ, Map.insert π (Pending op arg) f)
    | step_linearize σ σ' f π op arg res :
      (* If [π] has invoked [op(arg)] but not yet responded *)
      f !!! π = Pending op arg →
      (* And (σ', res) ∈ δ(σ, π, op, arg) *)
      (type ω).(δ) σ π op arg σ' res →
      (* Then [op(arg)] can linearize with value [res] and state [σ'] *)
      step (σ, f) π Intermediate (σ', Map.insert π (Linearized res) f)
    | step_response σ f π v :
      f !!! π = Linearized v →
      step (σ, f) π (Response v) (σ, Map.insert π Idle f).

    Definition Run {Π : Type} `{Countable Π, Object Π Ω} {ω : Ω} (σ₀ : (type ω).(Σ)) : run Π ω → Prop := Run (σ₀, λ _, Idle) step.

End Atomic.

  (* | idle_initial c : idle π (Initial c)
  | idle_step_response r c v : idle π (Step r π (Response v) c)
  | idle_step_intermediate r π' c : idle π r → idle π (Step r π' Intermediate c)
  | idle_step_invoke : idle π r → π ≠ π' → idle π () *)

(* Inductive coupled `{Countable Π, Object Π Ω, Object Π Ω₀} {ω : Ω₀} : relation (run (aumented_configuration Π Ω ω) Π ω) :=
  | coupled_initial c : coupled (Initial c) (Initial c)
  | coupled_step r r' π l tracker tracker' outstanding ϵ :
    coupled r r' →
    coupled
      (Step r π l {| tracker := tracker; outstanding := outstanding; ϵ := ϵ |})
      (Step r' π l {| tracker := tracker'; outstanding := outstanding; ϵ := ϵ |}). *)

Module Implementation.

  Record configuration Π Ω {Ω₀} `{Countable Π, Object Π Ω, Object Π Ω₀} (ω : Ω₀) := {
    outstanding : gmap Π (frame Π ω);
    ϵ : states Π Ω;
  }.

  Arguments outstanding : default implicits.
  Arguments ϵ : default implicits.

  Definition run Π Ω {Ω₀} `{Countable Π, Object Π Ω, Object Π Ω₀} (ω : Ω₀) := run (configuration Π Ω ω) Π ω.

  Section Semantics.
    Context {Π Ω₀ Ω : Type} {ω : Ω₀}.

    Context `{Countable Π, Object Π Ω₀, Object Π Ω}.

    Variable impl : Implementation Π Ω ω.

    Definition initial_frame op arg :=
      let proc := procedures impl op in
      {|
        op := op;
        pc := 0;
        arg := arg;
        registers := ∅;
      |}.

  Variant step_procedure (π : Π) : states Π Ω → frame Π ω → states Π Ω → signal Π ω → Prop :=
    | step_continue pc arg s ψ ψ' (op : (type ω).(OP)) ϵ ϵ' :
      (* If [pc] points to line containing statement [s] in [proc] *)
      procedures impl op !! pc = Some s →
      ⟨ π , arg , ψ , ϵ , s ⟩ ⇓ₛ ⟨ ψ' , ϵ' , Continue ⟩ →
      step_procedure π ϵ {| pc := pc; registers := ψ; op := op; arg := arg |} ϵ' (Next {| pc := S pc; registers := ψ'; op := op; arg := arg |})
    | step_goto pc pc' arg s ψ ψ' op ϵ ϵ' :
      (* If [pc] points to line containing statement [s] in [proc] *)
      procedures impl op !! pc = Some s →
      ⟨ π , arg , ψ , ϵ , s ⟩ ⇓ₛ ⟨ ψ' , ϵ' , Goto pc' ⟩ →
      step_procedure π ϵ {| pc := pc; registers := ψ; op := op; arg := arg |} ϵ' (Next {| pc := pc'; registers := ψ'; op := op; arg := arg |})
    (* | step_implicit_return arg pc ψ op ϵ :
      (* Control has fallen off end of procedure *)
      procedures impl op !! pc = None →
      step_procedure π ϵ {| pc := pc; registers := ψ; op := op; arg := arg |} ϵ (Return ⊤ᵥ) *)
    | step_return arg pc s ψ op ϵ ϵ' v:
      procedures impl op !! pc = Some s →
      ⟨ π , arg , ψ , ϵ , s ⟩ ⇓ₛ ⟨ ψ , ϵ' , Stmt.Return v ⟩ →
      step_procedure π ϵ {| pc := pc; registers := ψ; op := op; arg := arg |} ϵ' (Return v).

    Variant step : gmap Π (frame Π ω) → states Π Ω → Π → line Π ω → gmap Π (frame Π ω) → states Π Ω → Prop :=
      | step_invoke outstanding π ϵ op arg :
        outstanding !! π = None → 
        step outstanding ϵ π (Invoke op arg) (<[π := initial_frame op arg]>outstanding) ϵ
      | step_intermediate outstanding π ϵ ϵ' f f' :
        (* If process [π] has an outstanding request for proecedure [proc], interrupted at line [pc] *)
        outstanding !! π = Some f →
        step_procedure π ϵ f ϵ' (Next f') →
        step outstanding ϵ π Intermediate (<[π := f']>outstanding) ϵ'
      | step_response outstanding π ϵ ϵ' f v :
        (* If process [π] has an outstanding request for procedure [proc], interrupted at line [pc] *)
        outstanding !! π = Some f →
        step_procedure π ϵ f ϵ' (Return v) →
        step outstanding ϵ π (Response v) (delete π outstanding) ϵ'.

    Definition initial_configuration : configuration Π Ω ω  := {| outstanding := ∅; ϵ := impl.(initial_states) |}.

    Definition step_configuration c π l c' := step c.(outstanding) c.(ϵ) π l c'.(outstanding) c'.(ϵ).

    Definition Run := Run initial_configuration step_configuration.

  End Semantics.
End Implementation.

Module FullTracker.

  Record configuration Π Ω {Ω₀} `{Countable Π, Object Π Ω, Object Π Ω₀} (ω : Ω₀) := {
    base_configuration : Implementation.configuration Π Ω ω;
    tracker : meta_configuration Π ω;
  }.

  Arguments base_configuration : default implicits.
  Arguments tracker : default implicits.

  Section Semantics.

    Context {Π Ω₀ Ω : Type} {ω : Ω₀}.

    Context `{Countable Π, Object Π Ω₀, Object Π Ω}.

    Variable impl : Implementation Π Ω ω.
      
    Variant initial_tracker : meta_configuration Π ω :=
      initial_tracker_intro f : (∀ π, f !!! π = Idle) → initial_tracker impl.(initial_state) f.

    Definition initial_configuration := {|
      base_configuration := Implementation.initial_configuration impl;
      tracker := initial_tracker;
    |}.

    Variant step_augmented (c : configuration Π Ω ω) (π : Π) (l : line Π ω) : configuration Π Ω ω → Prop :=
      | step_augmented_intro base :
          Implementation.step_configuration impl c.(base_configuration) π l base →
            step_augmented c π l {| tracker := evolve π l c.(tracker); base_configuration := base |}.

    Definition Run := Run initial_configuration step_augmented.

    Definition invariant := invariant initial_configuration step_augmented.

    Fixpoint project r : Implementation.run Π Ω ω :=
      match r with
      | Initial c => Initial c.(base_configuration)
      | Step r π l c => Step (project r) π l c.(base_configuration)
      end.

    Definition run := Procedure.run (configuration Π Ω ω) Π ω.

    Fixpoint embed (r : Implementation.run Π Ω ω) : run :=
      match r with
      | Initial c => Initial {| base_configuration := c; tracker := initial_tracker |}
      | Step r π l c =>
        let r := embed r in
        Step r π l ({| base_configuration := c; tracker := evolve π l (tracker (final r)) |})
      end.

  Inductive coupled : Implementation.run Π Ω ω → run → Prop :=
    | coupled_initial c tracker : coupled (Initial c) (Initial {| tracker := tracker; base_configuration := c|})
    | coupled_step r r' π l tracker base :
      coupled r r' →
      coupled
        (Step r π l base)
        (Step r' π l {| tracker := tracker; base_configuration := base |}).

    Lemma project_embed_id r : project (embed r) = r.
    Proof.
      induction r.
      - reflexivity.
      - cbn. congruence.
    Qed.

    Lemma embed_project_id r : Run r → embed (project r) = r.
    Proof.
      induction r.
      - intros Hrun. now inv Hrun.
      - intros Hrun. inv Hrun. inv H7. cbn. f_equal.
        + auto.
        + f_equal. now rewrite IHr by auto.
    Qed.

    Lemma project_coupled r : Run r → coupled (project r) r.
    Proof.
      induction r.
      - intros Hrun. inv Hrun. constructor.
      - intros Hrun. inv Hrun. inv H7. cbn. constructor. auto.
    Qed.

    Lemma project_wf r : Run r → Implementation.Run impl (project r).
    Proof.
      induction r.
      - intros Hrun. inv Hrun. constructor.
      - intros Hrun. inv Hrun. inv H7. cbn. constructor.
        + now apply IHr.
        + now destruct r.
    Qed.

    Lemma embed_wf r : Implementation.Run impl r → Run (embed r).
    Proof.
      induction r.
      - intros Hrun. inv Hrun. constructor.
      - intros Hrun. inv Hrun. cbn. constructor.
        + now apply IHr.
        + constructor. now destruct r.
    Qed.

    Lemma embed_behavior r : behavior (embed r) = behavior r.
    Proof.
      induction r.
      - reflexivity.
      - destruct l.
        + cbn. now f_equal.
        + auto.
        + cbn. now f_equal.
    Qed.

    Lemma project_behavior r : behavior (project r) = behavior r.
    Proof.
      induction r.
      - reflexivity.
      - destruct l.
        + cbn. f_equal. auto.
        + auto.
        + cbn. f_equal. auto.
    Qed.

    Variant linearizable_run (r : run) σ f : Prop :=
      linearizable_intro (atomic : Atomic.run Π ω) :
        Atomic.Run impl.(initial_state) atomic →
          behavior r = behavior atomic →
            final atomic = (σ, f) →
              linearizable_run r σ f.

    (* Lemma project_sound r : Run r → Implementation.Run impl (project r).
    Proof.
      induction r; intros.
      - destruct c. simpl in *. econstructor. *)
    Definition tracker_sound (r : run) :=
      ∀ σ f, tracker (final r) σ f → linearizable_run r σ f.

    Lemma sound_linearizations r atomic σ σ' πs f f' :
      Run r →
        Atomic.Run impl.(initial_state) atomic →
          behavior atomic = behavior r →
            tracker (final r) σ f →
              final atomic = (σ, f) →
                δ_multi σ f πs σ' f' →
                  ∃ atomic',
                    Atomic.Run impl.(initial_state) atomic' ∧
                      behavior atomic' = behavior r ∧
                        final atomic' = (σ', f').
    Proof.
      intros. induction H7.
      - intros. exists atomic. split.
        + assumption.
        + now split.
      - intros. pose proof IHδ_multi H5 H6 as (atomic' & Hatomic & Hbehavior & Hfinal). clear IHδ_multi.
        eexists (Step atomic' _ Intermediate _).
        split.
        + econstructor; eauto. rewrite Hfinal. econstructor; eauto.
        + now split.
    Qed.

    Lemma sound_invoke r π op arg c :
      Run (Step r π (Invoke op arg) c) → tracker_sound r → tracker_sound (Step r π (Invoke op arg) c).
    Proof.
      intros HRunStep IH. inv HRunStep. inv H7. inv H2. unfold tracker_sound. simpl. intros.
      inv H2. inv H3. remember (invoke f1 π op arg) in H5. induction H5.
      - intros. unfold tracker_sound in *.
        apply IH in H2. inversion H2.
        eapply linearizable_intro with (atomic := Step atomic π (Invoke op arg) _).
        + econstructor.
          * assumption.
          * rewrite H7. now econstructor. 
        + simpl. now rewrite H5. 
        + simpl. now rewrite Heqs.
      - intros. unfold tracker_sound in *. simpl in *.
        apply IH in H2 as ?. inv H10. eapply IHδ_multi in H2. inv H2.
        eapply linearizable_intro with (atomic := Step atomic π0 Intermediate _).
        + econstructor.
          * assumption.
          * rewrite H14. simpl in *. econstructor; eauto.
        + assumption.
        + easy.
        + reflexivity.
    Qed.

    Lemma sound_intermediate r π c :
      Run (Step r π Intermediate c) → tracker_sound r → tracker_sound (Step r π Intermediate c).
    Proof.
      intros HRunStep IH. inv HRunStep. inv H7. inv H2. unfold tracker_sound. simpl. intros.
      inv H2. induction H7.
      - intros. unfold tracker_sound in *.
        apply IH in H6. inv H6.
        now eapply linearizable_intro with (atomic := atomic).
      - intros. unfold tracker_sound in *. simpl in *.
        apply IH in H6 as ?. inv H10. eapply IHδ_multi in H6. inv H6.
        eapply linearizable_intro with (atomic := Step atomic0 π0 Intermediate _).
        + econstructor.
          * assumption.
          * rewrite H15. simpl in *. econstructor; eauto.
        + assumption.
        + reflexivity.
    Qed.

    Lemma sound_response r π v c :
      Run (Step r π (Response v) c) → tracker_sound r → tracker_sound (Step r π (Response v) c).
    Proof.
      intros HRunStep IH. inv HRunStep. inv H7. inv H2. unfold tracker_sound. simpl. intros.
      inv H2. inv H3. remember (ret f2 π) in H6. induction H6.
      - intros. unfold tracker_sound in *.
        apply IH in H2. inversion H2.
        eapply linearizable_intro with (atomic := Step atomic π (Response v) _).
        + econstructor.
          * assumption.
          * rewrite H8. now econstructor. 
        + simpl. now rewrite H6. 
        + simpl. now rewrite Heqd.
      - intros. unfold tracker_sound in *. simpl in *.
        apply IH in H2 as ?. inv H11. eapply IHδ_multi in H2; auto. inv H2.
        eapply linearizable_intro with (atomic := Step atomic0 π0 Intermediate _).
        + econstructor.
          * assumption.
          * rewrite H16. simpl in *. econstructor; eauto.
        + assumption.
        + easy.
    Qed.

  Require Import Coq.Logic.FunctionalExtensionality.

  Lemma sound r : Run r → tracker_sound r.
  Proof.
    induction r.
    - simpl. intros. unfold tracker_sound. intros. econstructor.
      + econstructor.
      + constructor.
      + inv H2. inv H3. cbn. f_equal. apply functional_extensionality. intros π. now change (f π) with (f !!! π).
    - simpl. intros. inversion H2. destruct l.
      + apply sound_invoke; auto.
      + apply sound_intermediate; auto.
      + apply sound_response; auto.
  Qed.

  Definition tracker_complete r := 
    ∀ atomic σ f, 
      Atomic.Run impl.(initial_state) atomic →
        behavior r = behavior atomic →
          final atomic = (σ, f) →
            (final r).(tracker) σ f.

  Lemma linearization_invoke r π op arg c σ' f' atomic :
    Atomic.Run impl.(initial_state) atomic →
      behavior (Step r π (Invoke op arg) c) = behavior atomic →
        (* If [atomic] is a linearization of run [r, (π, Invoke op arg), c] with final configuration [(σ', f')] *)
        final atomic = (σ', f') →
          Run (Step r π (Invoke op arg) c) →
            ∃ atomic' σ f πs,
              Atomic.Run impl.(initial_state) atomic' ∧
                (* Then there exists some linearization [atomic'] of [r] *)
                behavior r = behavior atomic' ∧
                  (* With final configuration [(σ, f)] *)
                  final atomic' = (σ, f) ∧
                    (* Such that there exists some sequence of processes [πs] such 
                      that (σ', f') results from first invoking [op(arg)] and then linearizing each of [πs] *)
                    δ_multi σ (invoke f π op arg) πs σ' f' ∧
                      f !!! π = Idle.
    Proof.
      intros Hatomic.
      (* Need to generalize over the final configuration of the atomic run *)
      revert σ' f'. 
      (* Proceed by induction on the structure of the linearization *)
      induction atomic.
      - (* Case [atomic = Initial c']; impossible, as [atomic] is a linearization of [Step r π (Invoke op arg) c] *)
        discriminate.
      - (* Case [atomic = atomic, (π', l), c'] *)
        intros.
        (* Consider the last line [l] executed by the run *)
        destruct l.
        + (* [l] is an invocation *) 
          simpl in *. 
          (* Because the behavior of [atomic] is the same as [Step r π (Invoke op arg) c], this invocation must be [invoke π op arg] *)
          inv H2.
          (* We can take [atomic] as the linearization of [r] *)
          exists atomic.
          destruct (final atomic) as [σ f] eqn:Hfinal. exists σ. exists f.
          (* Because the last step of the linearization is an invocation, no pending processes linearize afterwards *)
          exists [].
          split.
          * (* Because [atomic, (π', l), c'] is an atomic run, so is [atomic] *)
            inv Hatomic. assumption.
          * split.
            -- assumption.
            -- split.
              ++ reflexivity.
              ++ inv Hatomic. inv H8. unfold invoke.
                  assert ((σ', f0) = (σ, f)) by now transitivity (final atomic).
                  inv H3. split.
                ** constructor.
                ** assumption.
        + (* [l] is an intermediate line, so [atomic, (π', l), c'] is also a linearization of [Step r π (Invoke op arg) c] *) 
          simpl in *.
          (* Because [atomic, (π', l), c'] is an atomic run, so is [atomic] *)
          inv Hatomic. subst.
          (* Let (σ, f) be the final configuration of [atomic ]
            Because ((σ, f), (π', Intermediate), (σ', f')) is a step,
            [f π' = Pending op' arg'], and [(σ', f')] results from linearizing [op(arg)] *)
          inv H10.
          apply IHatomic with (σ' := σ) (f' := f) in H7 as ?; eauto.
          (* We can apply the induction hypothesis to [atomic] *)
          destruct H5 as [atomic' [σ'' [f'' [πs [? [? [? [? ?]]]]]]]].
          exists atomic'. exists σ''. exists f''.
          exists (πs ,, π0).
          split.
          * assumption.
          * split.
            -- assumption.
            -- split.
              ** assumption.
              ** split.
                --- econstructor; eauto.
                --- assumption.
        + discriminate.
  Qed.

  Lemma linearization_response r π v c σ' f' atomic :
    Atomic.Run impl.(initial_state) atomic →
      behavior (Step r π (Response v) c) = behavior atomic →
        (* If [atomic] is a linearization of run [r, (π, Response v), c] with final configuration [(σ', f')] *)
        final atomic = (σ', f') →
          Run (Step r π (Response v) c) →
            ∃ atomic' σ f πs,
              Atomic.Run impl.(initial_state) atomic' ∧
                (* Then there exists some linearization [atomic'] of [r] *)
                behavior r = behavior atomic' ∧
                  (* With final configuration [(σ, f)] *)
                  final atomic' = (σ, f) ∧
                    (* Such that there exists some sequence of processes [πs] such 
                      that (σ', f') results from first invoking [op(arg)] and then linearizing each of [πs] *)
                    δ_multi σ (ret f π) πs σ' f' ∧
                      f !!! π = Linearized v.
    Proof.
      intros Hatomic.
      (* Need to generalize over the final configuration of the atomic run *)
      revert σ' f'. 
      (* Proceed by induction on the structure of the linearization *)
      induction atomic.
      - (* Case [atomic = Initial c']; impossible, as [atomic] is a linearization of [Step r π (Invoke op arg) c] *)
        discriminate.
      - (* Case [atomic = atomic, (π', l), c'] *)
        intros.
        (* Consider the last line [l] executed by the run *)
        destruct l.
        + discriminate.
        + (* [l] is an intermediate line, so [atomic, (π', l), c'] is also a linearization of [Step r π (Invoke op arg) c] *) 
          simpl in *.
          (* Because [atomic, (π', l), c'] is an atomic run, so is [atomic] *)
          inv Hatomic. subst.
          (* Let (σ, f) be the final configuration of [atomic ]
            Because ((σ, f), (π', Intermediate), (σ', f')) is a step,
            [f π' = Pending op' arg'], and [(σ', f')] results from linearizing [op(arg)] *)
          inv H10.
          apply IHatomic with (σ' := σ) (f' := f) in H7 as ?; eauto.
          (* We can apply the induction hypothesis to [atomic] *)
          destruct H5 as [atomic' [σ'' [f'' [πs [? [? [? [? ?]]]]]]]].
          exists atomic'. exists σ''. exists f''.
          exists (πs ,, π0).
          split.
          * assumption.
          * split.
            -- assumption.
            -- split.
              ** assumption.
              ** split.
                --- econstructor; eauto.
                --- assumption.
        + (* [l] is a response *) 
          simpl in *. 
          (* Because the behavior of [atomic] is the same as [Step r π (Response v) c], this response must be [Response v] *)
          inv H2.
          (* We can take [atomic] as the linearization of [r] *)
          exists atomic.
          destruct (final atomic) as [σ f] eqn:Hfinal. exists σ. exists f.
          (* Because the last step of the linearization is an invocation, no pending processes linearize afterwards *)
          exists [].
          split.
          * (* Because [atomic, (π', l), c'] is an atomic run, so is [atomic] *)
            inv Hatomic. assumption.
          * split.
            -- assumption.
            -- split.
              ++ reflexivity.
              ++ inv Hatomic. inv H9. unfold invoke.
                assert ((σ', f0) = (σ, f)) by now transitivity (final atomic).
                inv H3. split.
                ** constructor.
                ** assumption.
  Qed.

  (* Every linearization of an initial run is also initial *)
  Lemma linearization_empty c atomic :
    Run (Initial c) → Atomic.Run impl.(initial_state) atomic → behavior (Initial c) = behavior atomic → atomic = Initial (impl.(initial_state), λ _, Idle).
  Proof.
    simpl. intros Hrun. inv Hrun. induction atomic.
    - intros. inv H2. reflexivity.
    - intros. inv H2. destruct l; simpl in *.
      + discriminate.
      + apply IHatomic in H6; auto. inv H9. simpl in *. inv H2.
      + discriminate.
  Qed.

  Lemma complete r atomic σ f : Run r → Atomic.Run impl.(initial_state) atomic → behavior r = behavior atomic → final atomic = (σ, f) → (final r).(tracker) σ f.
  Proof.
    revert atomic σ f.
    induction r.
    - simpl. intros. eapply linearization_empty in H2 as ?; eauto. 
      subst. simpl in *. inv H5. inv H2. simpl. now econstructor.
    - destruct l.
      + intros. cbn. eapply linearization_invoke in H3 as (atomic' & σ' & f' & πs & Hatomicrun & Hbeh & Hfinal & Hmulti & Hidle); eauto.
        simpl in *. inv H2. inv H10. inv H2. simpl. econstructor.
        * econstructor; eauto.
        * eassumption.
      + simpl in *. intros. inv H2. inv H11. simpl. econstructor.
        * eapply IHr; eauto.
        * econstructor.
      + intros. eapply linearization_response in H3 as (atomic' & σ' & f' & πs & Hatomicrun & Hbeh & Hfinal & Hmulti & Hidle); eauto.
        simpl in *. inv H2. inv H10. simpl. econstructor.
        * econstructor; eauto. 
        * eauto.
  Qed.

  (** An implementation is linearizable iff there exists a linearization for each of its runs *)
  Definition linearizable :=
    ∀ r,
      Implementation.Run impl r →
        ∃ atomic, Atomic.Run impl.(initial_state) atomic ∧ behavior r = behavior atomic.

  Lemma soundness : invariant (λ c, ∃ σ f, tracker c σ f) → linearizable.
  Proof.
    unfold linearizable, invariant. intros Hinv r Hrun.
    pose proof Hinv (embed r) (embed_wf r Hrun) as (σ & f & Hmeta).
    pose proof sound (embed r) (embed_wf r Hrun).
    unfold tracker_sound in *.
    pose proof H2 _ _ Hmeta as [atomic Hatomic Hlinearization Hfinal].
    exists atomic. split.
    - assumption.
    - rewrite <- Hlinearization. now rewrite embed_behavior. 
  Qed.

  Lemma completeness : linearizable → invariant (λ c, ∃ σ f, tracker c σ f).
  Proof.
    unfold linearizable, invariant. intros Hlinearizable r Hrun.
    pose proof Hlinearizable (project r) (project_wf r Hrun) as (atomic & Hatomic & Hbehavior).
    destruct (final atomic) as [σ f] eqn:Hfinal.
    exists σ. exists f.
    eapply complete; eauto.
    rewrite <- Hbehavior. now rewrite project_behavior.
  Qed.

  (* An implementation is linearizable iff its tracker being non-empty is an invariant of the algorithm *)
  Theorem adequacy : linearizable ↔ invariant (λ c, ∃ σ f, tracker c σ f).
  Proof.
    split.
    - exact completeness.
    - exact soundness.
  Qed.

  End Semantics.
End FullTracker.

Module ReadWrite.

  Variant t : Set := Cell.

  Definition Σ := Value.t.

  Variant OP := Read | Write.

  Variant δ (Π : Type) : Σ → Π → OP → Value.t → Σ → Value.t → Prop :=
    | δ_read x π v : δ Π x π Read v x x
    | δ_write x y π : δ Π x π Write y y Value.Unit.

  Definition object_type Π := {|
    Object.Σ := Σ;
    Object.OP := OP;
    Object.δ := δ Π;
  |}.

  Instance eq_dec : EqDecision t.
  Proof. solve_decision. Defined.

  Instance object Π : Object Π t := const (object_type Π).

End ReadWrite.

Module ReadCAS.

  Variant t := Cell.

  Definition Σ := Value.t.

  Variant OP := Read | CAS.

  Variant δ (Π : Type) : Σ → Π → OP → Value.t → Σ → Value.t → Prop :=
    | δ_read x π v : δ Π x π Read v x x
    | δ_cas_succeed x y z π : 
      x = y →
        δ Π x π CAS (Value.Pair y z) z (Value.Bool true)
    | δ_cas_fail x y z π :
      x ≠ y →
        δ Π x π CAS (Value.Pair y z) x (Value.Bool false).

  Definition object_type Π := {|
    Object.Σ := Σ;
    Object.OP := OP;
    Object.δ := δ Π;
  |}.

  Instance eq_dec : EqDecision t.
  Proof. solve_decision. Qed.

  Instance object Π : Object Π t := const (object_type Π).

End ReadCAS.

Section RWCAS.

  Variable Π : Type.

  Context `{EqDecision Π, Countable Π}.

  Import ReadWrite ReadCAS.

  Definition impl : Implementation Π ReadCAS.t ReadWrite.Cell.
  Proof.
    split.
    - exact Value.Unit.
    - exact (λ _, Value.Unit).
    - intros op. destruct op eqn:?.
      exact [
        Assign "r" (Term.Invoke ReadCAS.Cell ReadCAS.Read Term.Unit);
        Syntax.Stmt.Return (Term.Var "r")
      ].
      + exact [
          Assign "x" (Term.Invoke ReadCAS.Cell ReadCAS.Read Term.Unit);
          Stmt.Invoke (Term.Invocation ReadCAS.Cell ReadCAS.CAS (Term.Pair (Term.Var "x") Term.Arg));
          Syntax.Stmt.Return Term.Unit
        ].
    Defined.

    (* Only auxiliary state is metaconfiguration *)
    Definition Aux := unit.

    Import Implementation.

    Variant tracker_inv (c : Implementation.configuration Π ReadCAS.t ReadWrite.Cell) (π : Π) : status Π ReadWrite.Cell → Type :=
      | tracker_inv_idle : c.(outstanding) !! π = None → tracker_inv c π Idle
      | tracker_inv_invoke f : 
        c.(outstanding) !! π = Some f →
        f.(pc) = 0 →
        tracker_inv c π (Pending f.(op) f.(arg))
      | tracker_inv_read_return f v :
        c.(outstanding) !! π = Some f →
        f.(op) = ReadWrite.Read →
        f.(pc) = 1 →
        f.(registers) !! "r" = Some v →
        tracker_inv c π (Linearized v)
      | tracker_inv_write_cas_pending f :
        c.(outstanding) !! π = Some f →
        f.(op) = ReadWrite.Write →
        f.(pc) = 1 →
        tracker_inv c π (@Pending Π ReadWrite.t _ _ _ ReadWrite.Write f.(arg))
      | tracker_inv_write_cas_linearized f v :
        c.(outstanding) !! π = Some f →
        f.(op) = ReadWrite.Write →
        f.(pc) = 1 →
        f.(registers) !! "x" = Some v →
        c.(ϵ) ReadCAS.Cell ≠ v →
        tracker_inv c π (Linearized Value.Unit)
      | tracker_inv_write_response f :
        c.(outstanding) !! π = Some f →
        f.(op) = ReadWrite.Write →
        f.(pc) = 2 →
        tracker_inv c π (Linearized Value.Unit).

      Lemma tracker_inv_step_diff π c c' status :
        c.(outstanding) !! π = c'.(outstanding) !! π →
        c.(ϵ) ReadCAS.Cell = c'.(ϵ) ReadCAS.Cell →
        tracker_inv c π status → tracker_inv c' π status.
      Proof.
        intros Hlocal Hglobal Hrel. inv Hrel.
        - constructor. now rewrite <- Hlocal.
        - constructor; auto. now rewrite <- Hlocal.
        - econstructor; eauto. now rewrite <- Hlocal.
        - econstructor; eauto. now rewrite <- Hlocal.
        - eapply tracker_inv_write_cas_linearized; eauto.
          + now rewrite <- Hlocal.
          + now rewrite <- Hglobal.
        - eapply tracker_inv_write_response; eauto.
          now rewrite <- Hlocal.
      Defined.

      Variant S (c : Implementation.configuration Π ReadCAS.t ReadWrite.Cell) : meta_configuration Π ReadWrite.Cell :=
        | S_intro f : (∀ π : Π, tracker_inv c π (f !!! π)) → S c (c.(ϵ) ReadCAS.Cell) f.

      Require Import Coq.Logic.FunctionalExtensionality.

      Lemma intermediate_pc_positive (r : FullTracker.run Π ReadCAS.t ReadWrite.Cell) (π : Π) c f :
        FullTracker.Run impl (Step r π Intermediate c) →
        c.(base_configuration).(outstanding) !! π = Some f →
        f.(pc) ≠ 0.
      Proof.
        intros Hrun Hf.
        unfold "≠". intros.
        inv Hrun. clear H3. inv H6. simpl in *. inv H1.
        inv H8; simpl in *.
        - destruct op0.
          + destruct pc0.
            * simpl in H5. inv H5. inv H10. rewrite <- H3 in Hf.
              rewrite lookup_insert in Hf. inv Hf.
            * destruct pc0. 
              -- simpl in H5. inv H5. inv H10.
              -- simpl in H5. inv H5.
          + destruct pc0.
            * simpl in H5. inv H5. inv H10. rewrite <- H3 in Hf.
              rewrite lookup_insert in Hf. inv Hf.
            * destruct pc0. 
              -- simpl in H5. inv H5. inv H10. rewrite <- H3 in Hf.
                rewrite lookup_insert in Hf. inv Hf.
              -- destruct pc0.
                ++ simpl in H5. inv H5. inv H10.
                ++ simpl in H5. inv H5.
        - destruct op0.
          + destruct pc0.
            * simpl in H5. inv H5. inv H10.
            * destruct pc0. 
              -- simpl in H5. inv H5. inv H10.
              -- simpl in H5. inv H5.
          + destruct pc0.
            * simpl in H5. inv H5. inv H10.
            * destruct pc0. 
              -- simpl in H5. inv H5. inv H10.
              -- destruct pc0.
                ++ simpl in H5. inv H5. inv H10.
                ++ simpl in H5. inv H5.
      Qed.


      Definition update {c} {g : Π → status Π ReadWrite.Cell} : (∀ π, tracker_inv c π (g π)) → Π → status Π ReadWrite.Cell.
      Proof.
        intros Hinv π.
        destruct (Hinv π).
        - exact (g π).
        - exact (g π).
        - exact (g π).
        - exact (g π).
        - exact (Pending f.(op) f.(arg)).
        - exact (g π). 
      Defined.

      Lemma tracker_inv_step_diff_update f π c c' (X : ∀ π, tracker_inv c π (f π))  :
        c.(outstanding) !! π = c'.(outstanding) !! π →
        tracker_inv c π (f π) → tracker_inv c' π (update X !!! π).
      Proof.
        intros Hframe Hinv. unfold update, "!!!", Map.map_lookup_total, Map.lookup. destruct (X π).
        - econstructor. now rewrite <- Hframe.
        - econstructor; eauto. now rewrite <- Hframe.
        - econstructor; eauto. now rewrite <- Hframe.
        - econstructor; eauto. now rewrite <- Hframe.
        - rewrite e0. eapply tracker_inv_write_cas_pending; eauto. now rewrite <- Hframe.
        - eapply tracker_inv_write_response; eauto. now rewrite <- Hframe.
      Qed.

      Lemma return_pc_read {π arg ψ ψ' ϵ ϵ' pc s v} : 
        procedures impl ReadWrite.Read !! pc = Some s →
            ⟨ π , arg , ψ , ϵ , s ⟩ ⇓ₛ ⟨ ψ' , ϵ' , Stmt.Return v ⟩ → pc = 1.
      Proof.
        cbn. intros Hstmt Hstep.
        - destruct pc.
          + inv Hstmt. inv Hstep.
          + destruct pc0.
            * reflexivity.
            * inv Hstmt. 
      Qed.

      Lemma return_pc_write {π arg ψ ψ' ϵ ϵ' pc s v} : 
        procedures impl ReadWrite.Write !! pc = Some s →
            ⟨ π , arg , ψ , ϵ , s ⟩ ⇓ₛ ⟨ ψ' , ϵ' , Stmt.Return v ⟩ → pc = 2.
      Proof.
        cbn. intros Hstmt Hstep.
        - destruct pc.
          + inv Hstmt. inv Hstep.
          + destruct pc0.
            * inv Hstmt. inv Hstep.
            * destruct pc0.
              -- reflexivity.
              -- inv Hstmt.
      Qed.

      Set Typeclasses Strict Resolution.

      Lemma return_state_constant {π arg ψ ψ' ϵ ϵ' op pc s v} : 
        procedures impl op !! pc = Some s →
          ⟨ π , arg , ψ , ϵ , s ⟩ ⇓ₛ ⟨ ψ' , ϵ' , Stmt.Return v ⟩ → ψ = ψ' ∧ ϵ = ϵ'.
      Proof.
        destruct op; cbn; intros Hstmt Hstep.
        - pose proof return_pc_read Hstmt Hstep. subst. inv Hstmt. inv Hstep. inv H4. tauto.
        - pose proof return_pc_write Hstmt Hstep. subst. inv Hstmt. inv Hstep. inv H4. tauto.
      Qed.

      Lemma no_goto {π arg ψ ψ' ϵ ϵ' op pc pc' s} :
        procedures impl op !! pc = Some s →
          ¬ (⟨ π , arg , ψ , ϵ , s ⟩ ⇓ₛ ⟨ ψ' , ϵ' , Goto pc' ⟩).
      Proof.
        destruct op.
        - destruct pc.
          + cbn. intros. inv H0. unfold not. intros. inv H0.
          + destruct pc0.
            * cbn. intros. inv H0. unfold not. intros. inv H0.
            * cbn. intros. inv H0.
        - destruct pc.
          + cbn. intros. inv H0. unfold not. intros. inv H0.
          + destruct pc0.
            * cbn. intros. inv H0. unfold not. intros. inv H0.
            * cbn. intros. destruct pc0.
              -- inv H0. intros. unfold not. intros. inv H0.
              -- inv H0.
      Qed.

      Require Import Coq.Program.Equality.

      Lemma update_not_idle c f (X : ∀ π, tracker_inv c π (f π)) π : update X !!! π ≠ Idle ↔ f π ≠ Idle.
      Proof.
        split; unfold update, "!!!", Map.map_lookup_total, Map.lookup in *.
        - intros Hinv. now destruct (X π).
        - intros Neq. now destruct (X π).
      Qed.

      Lemma outstanding_finite : FullTracker.invariant impl (λ c M, ∀ σ f, S c σ f → ∃ (l : gset Π), ∀ π : Π, π ∈ l ↔ f !!! π ≠ Idle).
      Proof.
        unfold FullTracker.invariant, invariant, Procedure.invariant. intros r. induction r; intros Hrun.
        - inv Hrun. cbn in *. intros σ f HS. exists ∅. intros. inv HS.
          pose proof X π as Hinv. inv Hinv. split.
          + intros. inv H2.
          + intros. contradiction.
        - inversion Hrun. subst. inv H5. inv H1. inv H0.
          + cbn in *. intros σ f HS.
            pose proof IHr H2 as IH. pose proof IH σ (<[π := Idle]>f) as IH.
            inv HS. pose proof X π as Hinv. inv Hinv;
            (rewrite <- H1 in H3; rewrite lookup_insert in H3; inv H3).
            cbn in *.
            assert (S (base_configuration (final r)) (ϵ base Cell) (<[π:=Idle]> f)) as HS.
            { rewrite <- H7. econstructor. intros π'.
              destruct (decide (π = π')).
              - subst. rewrite Map.lookup_insert at 1. now econstructor.
              - subst. rewrite Map.lookup_insert_ne at 1 by assumption.
                apply tracker_inv_step_diff with (c := base).
                + rewrite <- H1. now simpl_map.
                + now rewrite H7.
                + auto. }
            pose proof IH HS as [l Hfin].
            exists (l ∪ {[ π ]}).
            intros π'. split.
            * intros Hmem. apply elem_of_union in Hmem as [Hin | Heq].
              -- pose proof Hfin π' as [Hfwd _]. destruct (decide (π = π')).
                ++ subst. rewrite Map.lookup_insert in Hfwd at 1. exfalso.
                   pose proof Hfwd Hin. contradiction.
                ++ rewrite Map.lookup_insert_ne in Hfwd at 1 by assumption. auto.
              -- apply elem_of_singleton in Heq. subst. rewrite <- H0. intros. discriminate.
            * intros Hneq. destruct (decide (π = π')).
              -- subst. cbn. set_solver.
              -- set_unfold. left. pose proof Hfin π' as [_ Hrev].
                 rewrite Map.lookup_insert_ne in Hrev at 1 by assumption.
                 auto.
          + cbn in *. intros σ F HS. inv H8; [ idtac | exfalso; eapply no_goto; eauto ].
            inv HS. pose proof X π as Hinv. inv Hinv.
            * rewrite <- H1 in H5. now rewrite lookup_insert in H5.
            * now assert (pc f ≠ 0) by (eapply intermediate_pc_positive; eauto).
            * rewrite <- H1 in H5. rewrite lookup_insert in H5. inv H5. subst. cbn in *. subst. inv H7. inv H4. inv H9. inv H8.
              rewrite lookup_insert in H5. inv H5. inv H7. inv H6. inv H11. inv H4.
              remember ({| op := _; pc := 0; arg := arg0; registers := ψ |}).
              assert (∃ l : gset Π, ∀ π' : Π, π' ∈ l ↔ <[π := Pending f.(op) f.(arg)]>F !!! π' ≠ Idle) as [l Hl].
              { eapply IHr with (σ := ϵ base Cell); eauto.
                rewrite <- H10. econstructor.
                intros π'. destruct (decide (π = π')).
                -- subst. rewrite Map.lookup_insert at 1. now econstructor.
                -- rewrite Map.lookup_insert_ne at 1 by assumption.
                  ++ apply tracker_inv_step_diff with (c := base).
                    ** rewrite <- H1. now rewrite lookup_insert_ne by assumption.
                    ** symmetry. congruence.
                    ** auto. 
              }
              exists l. intros π'. pose proof Hl π' as [Hfwd Hrev]. clear Hl. split.
              -- intros Hin. destruct (decide (π = π')).
                 ++ subst. now rewrite <- H0.
                 ++ subst. cbn in *. pose proof Hfwd Hin as Hfwd. now rewrite Map.lookup_insert_ne in Hfwd at 1.
              -- intros. destruct (decide (π = π')).
                 ++ subst. apply Hrev. cbn. now rewrite Map.lookup_insert at 1.
                 ++ apply Hrev. now rewrite Map.lookup_insert_ne at 1.
            * rewrite <- H1 in H5. rewrite lookup_insert in H5. inv H5. subst. cbn in *. subst. inv H7. inv H4. inv H9. inv H7. inv H6. inv H11. inv H4.
              remember ({| op := _; pc := 0; arg := arg0; registers := ψ |}).
              assert (∃ l : gset Π, ∀ π' : Π, π' ∈ l ↔ <[π := Pending f.(op) f.(arg)]>F !!! π' ≠ Idle) as [l Hl].
              { eapply IHr with (σ := ϵ base Cell); eauto.
                rewrite <- H8. econstructor.
                intros π'. destruct (decide (π = π')).
                -- subst. rewrite Map.lookup_insert at 1. now econstructor.
                -- rewrite Map.lookup_insert_ne at 1 by assumption.
                  ++ apply tracker_inv_step_diff with (c := base).
                    ** rewrite <- H1. now rewrite lookup_insert_ne by assumption.
                    ** symmetry. congruence.
                    ** auto. 
              }
              exists l. intros π'. pose proof Hl π' as [Hfwd Hrev]. clear Hl. split.
              -- intros Hin. destruct (decide (π = π')).
                 ++ subst. now rewrite <- H0.
                 ++ subst. cbn in *. pose proof Hfwd Hin as Hfwd. now rewrite Map.lookup_insert_ne in Hfwd at 1.
              -- intros. destruct (decide (π = π')).
                 ++ subst. apply Hrev. cbn. now rewrite Map.lookup_insert at 1.
                 ++ apply Hrev. now rewrite Map.lookup_insert_ne at 1.
            * rewrite <- H1 in H5. rewrite lookup_insert in H5. inv H5. subst. cbn in *. subst. inv H7. inv H4. inv H9. inv H7. inv H6. inv H13. inv H4.
              rewrite lookup_insert in H8. inv H8. rewrite H11 in H10. destruct ω. now unfold Map.lookup in H10.
            * rewrite <- H1 in H5. rewrite lookup_insert in H5. inv H5. cbn in *. subst.
              inv H4. inv H6. inv H9. inv H8. inv H7. inv H8. inv H12. inv H10. destruct ω, ω0. cbn in *. inv H4.
              -- remember ({| op := _; pc := 1; arg := σ; registers := ψ' |}) as frame.
                 assert (∃ l : gset Π, ∀ π' : Π, π' ∈ l ↔ <[π := Pending frame.(op) frame.(arg)]>(update X) !!! π' ≠ Idle) as [l Hl].
                 { eapply IHr.
                   - auto.
                   - econstructor. intros π'.
                     destruct (decide (π = π')).
                     + destruct e. rewrite Map.lookup_insert at 1.
                       rewrite Heqframe at 1. cbn. eapply tracker_inv_write_cas_pending.
                       * eauto.
                       * now rewrite Heqframe.
                       * now rewrite Heqframe.
                     + rewrite Map.lookup_insert_ne at 1 by assumption.
                       apply tracker_inv_step_diff_update; auto.
                       rewrite <- H1. now rewrite lookup_insert_ne.
                 }
                 exists l. intros π'. pose proof Hl π' as [Hfwd Hrev]. clear Hl. split.
                 ++ intros Hin. destruct (decide (π = π')).
                     ** subst. now rewrite <- H0.
                     ** subst. cbn in *. pose proof Hfwd Hin as Hfwd.
                        rewrite Map.lookup_insert_ne in Hfwd at 1 by assumption.
                        eapply update_not_idle; eauto.
                 ++ intros. destruct (decide (π = π')).
                     ** subst. apply Hrev. cbn. now rewrite Map.lookup_insert at 1.
                     ** apply Hrev.
                        rewrite Map.lookup_insert_ne in Hfwd at 1 by assumption.
                        rewrite Map.lookup_insert_ne at 1 by assumption.
                        eapply update_not_idle; eauto.
              -- rewrite Map.Dep.η in H6.
                 assert (∃ l : gset Π, ∀ π' : Π, π' ∈ l ↔ <[π := Linearized Value.Unit]>F !!! π' ≠ Idle) as [l Hl].
                 { eapply IHr with (σ := ϵ base Cell); eauto.
                   rewrite <- H6. econstructor.
                   intros π'. destruct (decide (π = π')).
                   -- subst. rewrite Map.lookup_insert at 1. eapply tracker_inv_write_cas_linearized; eauto.
                   -- rewrite Map.lookup_insert_ne at 1 by assumption.
                     ++ apply tracker_inv_step_diff with (c := base).
                       ** rewrite <- H1. now rewrite lookup_insert_ne by assumption.
                       ** symmetry. congruence.
                       ** auto. 
                 }
                 exists l. intros π'. pose proof Hl π' as [Hfwd Hrev]. clear Hl. split.
                 ++ intros Hin. destruct (decide (π = π')).
                     ** subst. now rewrite <- H0.
                     ** subst. cbn in *. pose proof Hfwd Hin as Hfwd. now rewrite Map.lookup_insert_ne in Hfwd at 1.
                 ++ intros. destruct (decide (π = π')).
                     ** subst. apply Hrev. cbn. now rewrite Map.lookup_insert at 1.
                     ** apply Hrev. now rewrite Map.lookup_insert_ne at 1.
          + cbn in *. intros σ F HS. inv H8. destruct op0.
            * pose proof return_pc_read H4 H9 as pc_read. subst. inv H4. inv H9. inv H7.
              inv HS. pose proof X π as Hinv. inv Hinv; rewrite <- H1 in H6; rewrite lookup_delete in H6; try discriminate. clear H6.
              remember ({| op := _; pc := 1; arg := arg0; registers := ψ |}).
              assert (S (base_configuration (final r)) (ϵ base Cell) (<[π := Linearized v]>F)) as HS.
              { rewrite <- H4. econstructor. intros π'.
                destruct (decide (π = π')).
                - subst. rewrite Map.lookup_insert at 1. econstructor; eauto.
                - subst. rewrite Map.lookup_insert_ne at 1 by assumption.
                  apply tracker_inv_step_diff with (c := base).
                  + rewrite <- H1. now rewrite lookup_delete_ne by assumption.
                  + congruence.
                  + auto. }
              pose proof IHr H2 as IH. pose proof IH (ϵ base Cell) (<[π := Linearized v]>F) as IH.
              pose proof IH HS as [l Hfin].
              exists (difference l {[ π ]}).
              intros π'. pose proof Hfin π' as [Hfwd Hrev]. split.
              -- intros Hmem. apply elem_of_difference in Hmem as [Hmem Hneq]. rewrite elem_of_singleton in Hneq.
                 pose proof Hfwd Hmem as Hpending. now rewrite Map.lookup_insert_ne in Hpending at 1.
              -- intros Hpending. set_unfold. split.
                 ++ apply Hrev. destruct (decide (π = π')).
                    ** subst. now rewrite Map.lookup_insert at 1 by assumption.
                    ** now rewrite Map.lookup_insert_ne at 1 by assumption.
                 ++ destruct (decide (π = π')).
                    ** subst. rewrite H0 in Hpending. contradiction.
                    ** auto.
            * pose proof return_pc_write H4 H9 as pc_read. subst. inv H4. inv H9. inv H7.
              inv HS. pose proof X π as Hinv. inv Hinv; rewrite <- H1 in H5; rewrite lookup_delete in H5; try discriminate.
              assert (S (base_configuration (final r)) (ϵ base Cell) (<[π := Linearized Value.Unit]>F)) as HS.
              { rewrite <- H0. econstructor. intros π'.
                destruct (decide (π = π')).
                - subst. rewrite Map.lookup_insert at 1. eapply tracker_inv_write_response; eauto.
                - subst. rewrite Map.lookup_insert_ne at 1 by assumption.
                  apply tracker_inv_step_diff with (c := base).
                  + rewrite <- H1. now rewrite lookup_delete_ne by assumption.
                  + congruence.
                  + auto. }
              pose proof IHr H2 as IH. pose proof IH (ϵ base Cell) (<[π := Linearized Value.Unit]>F) as IH.
              pose proof IH HS as [l Hfin].
              exists (difference l {[ π ]}).
              intros π'. pose proof Hfin π' as [Hfwd Hrev]. split.
              -- intros Hmem. apply elem_of_difference in Hmem as [Hmem Hneq]. rewrite elem_of_singleton in Hneq.
                 pose proof Hfwd Hmem as Hpending. now rewrite Map.lookup_insert_ne in Hpending at 1.
              -- intros Hpending. set_unfold. split.
                 ++ apply Hrev. destruct (decide (π = π')).
                    ** subst. now rewrite Map.lookup_insert at 1 by assumption.
                    ** now rewrite Map.lookup_insert_ne at 1 by assumption.
                 ++ destruct (decide (π = π')).
                    ** subst. rewrite H4 in Hpending. contradiction.
                    ** auto.
      Qed.

      Lemma S_inhabited : FullTracker.invariant impl (λ c M, ∃ σ f, S c σ f).
      Proof.
        unfold FullTracker.invariant, invariant, Procedure.invariant. intros r. induction r; intros Hrun.
        - inv Hrun. cbn. eexists. exists (λ _, Idle).
          econstructor. intro. constructor. cbn. auto.
        - inversion Hrun. subst. inv H5. inv H1. pose proof IHr H2 as (σ & f & HS). inv HS. inv H0.
          + eexists. cbn in *. eexists (<[π := Pending (initial_frame impl op0 arg0).(op) (initial_frame impl op0 arg0).(arg)]>f).
            econstructor. intros π'. destruct (decide (π = π')).
            * subst. rewrite Map.lookup_insert at 1. eapply tracker_inv_invoke.
              ++ rewrite <- H1. now rewrite lookup_insert.
              ++ reflexivity.
            * subst. rewrite Map.lookup_insert_ne at 1 by assumption.
              apply tracker_inv_step_diff with (c := base_configuration (final r)).
              -- rewrite <- H1. now rewrite lookup_insert_ne by assumption.
              -- congruence.
              -- auto.
          + cbn. inv H8; [ idtac | exfalso; eapply no_goto; eauto ]. destruct op0.
            * destruct pc0.
              -- inv H4. inv H9. exists (ϵ base Cell). exists (<[π := Linearized v]>f). inv H6. inv H5. inv H10. inv H0.
                 rewrite H7. econstructor. intros π'. destruct (decide (π = π')).
                 ++ subst. rewrite Map.lookup_insert at 1. econstructor.
                    ** rewrite <- H1. now rewrite lookup_insert.
                    ** reflexivity.
                    ** reflexivity.
                    ** cbn. rewrite lookup_insert. now rewrite H7.
                 ++ rewrite Map.lookup_insert_ne at 1 by assumption.
                    apply tracker_inv_step_diff with (c := base_configuration (final r)).
                    ** rewrite <- H1. now rewrite lookup_insert_ne.
                    ** congruence.
                    ** auto.
              -- destruct pc0.
                 ++ inv H4. inv H9.
                 ++ inv H4.
            * destruct pc0.
              -- inv H4. inv H9. inv H6. inv H5. inv H10. inv H0.
                 remember ({| op := _; pc := 1; arg := arg0; registers := _ |}).
                 exists (ϵ base Cell). exists (<[π := Pending f0.(op) f0.(arg)]>f).
                 econstructor. intros π'. destruct (decide (π = π')).
                 ++ subst. rewrite Map.lookup_insert at 1. eapply tracker_inv_write_cas_pending.
                    ** rewrite <- H1. now rewrite lookup_insert.
                    ** reflexivity.
                    ** reflexivity.
                 ++ rewrite Map.lookup_insert_ne at 1 by assumption. 
                    apply tracker_inv_step_diff with (c := base_configuration (final r)).
                    ** rewrite <- H1. now rewrite lookup_insert_ne by assumption.
                    ** congruence.
                    ** auto.
              -- destruct pc0.
                 ++ inv H4. inv H9. inv H7. inv H6. inv H7. inv H11. destruct ω, ω0. inv H9. inv H0.
                    ** remember ({| op := _; pc := 2; arg := σ; registers := _ |}) as frame.
                       exists (ϵ base Cell). exists (<[π := Linearized Value.Unit]>(update X)).
                       econstructor. intros π'.
                       destruct (decide (π = π')).
                       --- subst. rewrite Map.lookup_insert at 1. eapply tracker_inv_write_response.
                           +++ rewrite <- H1. rewrite lookup_insert. reflexivity.
                           +++ reflexivity.
                           +++ reflexivity.
                       --- rewrite Map.lookup_insert_ne at 1 by assumption. eapply tracker_inv_step_diff_update.
                           +++ rewrite <- H1. now rewrite lookup_insert_ne.
                           +++ auto.
                    ** remember ({| op := _; pc := 2; arg := v₂; registers := _ |}) as frame.
                       exists (ϵ base Cell). exists (<[π := Linearized Value.Unit]>f).
                       econstructor. intros π'.
                       destruct (decide (π = π')).
                       --- subst. rewrite Map.lookup_insert at 1. eapply tracker_inv_write_response.
                           +++ rewrite <- H1. rewrite lookup_insert. reflexivity.
                           +++ reflexivity.
                           +++ reflexivity.
                       --- rewrite Map.lookup_insert_ne at 1 by assumption. apply tracker_inv_step_diff with (c := base_configuration (final r)).
                           +++ rewrite <- H1. now rewrite lookup_insert_ne.
                           +++ rewrite Map.Dep.η in H5. congruence.
                           +++ auto.
                  ++ destruct pc0.
                     ** inv H4. inv H9.
                     ** inv H4.
            + inv H8. pose proof return_state_constant H4 H9 as [_ Hϵ].
              exists (ϵ base Cell). exists (<[π := Idle]>f).
              cbn. econstructor. intros π'.
              destruct (decide (π = π')).
              * subst. rewrite Map.lookup_insert at 1. econstructor.
                rewrite <- H1. now rewrite lookup_delete.
              * rewrite Map.lookup_insert_ne at 1 by assumption.
                apply tracker_inv_step_diff with (c := base_configuration (final r)).
                -- rewrite <- H1. now rewrite lookup_delete_ne by assumption.
                -- congruence.
                -- auto.
      Qed.

      Definition linearized_writers {base : configuration Π t ReadWrite.Cell} {g : Π → status Π ReadWrite.Cell} :
        (∀ π : Π, tracker_inv base π (g !!! π)) →
          list Π →
            list Π.
      Proof.
        intros Hinv l. refine (List.filter _ l).
        intros π. destruct (Hinv π).
        - exact false.
        - exact false.
        - exact false.
        - exact false.
        - exact true.
        - exact false.
      Defined.

      Definition linearized_writer {base} {f : Π → status Π ReadWrite.Cell} (X : ∀ π : Π, tracker_inv base π (f !!! π)) (π : Π) :=
        match X π with
        | tracker_inv_write_cas_linearized _ _ _ _ _ _ _ _ _ => True
        | _ => False
        end.

      Lemma linearized_writers_correct {base f} (X : ∀ π : Π, tracker_inv base π (f !!! π)) (l : gset Π) :
        (∀ π : Π, π ∈ l ↔ f !!! π ≠ Idle) →
          ∀ π,
            π ∈ list_of_list (linearized_writers X (elements l)) ↔ linearized_writer X π.
      Proof.
        intros Hmem π. unfold linearized_writers. rewrite <- snoc_in_iff_list_in. rewrite elem_of_list_In.
        rewrite filter_In. split.
        - intros [Hin Hlin]. unfold linearized_writer. destruct (X π); now try discriminate.
        - unfold linearized_writer. intros. pose proof Hmem π as Hmem. destruct (X π); try contradiction. split.
          + apply elem_of_list_In. apply elem_of_elements. now apply Hmem.
          + reflexivity.
      Qed.

      Fixpoint linearize_many (πs : list Π) (f : Π → status Π ReadWrite.Cell) :=
        match πs with
        | [] => f
        | πs ,, π => <[π := Linearized Value.Unit]>(linearize_many πs f)
        end.

      (* Lemma linearized_many_linearized_writers_idetntity {base f} (X : ∀ π : Π, tracker_inv base π (f !!! π)) (l : gset Π) :
        (∀ π : Π, π ∈ l ↔ f !!! π ≠ Idle) →
          f = linearize_many (linearized_writers X (elements l)) f.
      Proof.
        intros Hlin. pose proof linearized_writers_correct X l Hlin as Hw. clear Hlin.
        generalize dependent f.
        (* assert (NoDup (elements l)) by apply NoDup_elements. *)
        induction (elements l).
        - intros f X Hlin. reflexivity.
        - intros f X Hlin. cbn. cbn in Hlin. destruct (X a); try (now apply IHl0).
          cbn. *)

      Definition linearized_writer_frame {base} {f : Π → status Π ReadWrite.Cell} {X : ∀ π : Π, tracker_inv base π (f !!! π)} {π : Π} : linearized_writer X π → frame Π ReadWrite.Cell.
      Proof.
        unfold linearized_writer. intros Hlinw. destruct (X π); try contradiction.
        exact f0.
      Defined.

      (* Definition unlinearize_writer {base} {f : Π → status Π ReadWrite.Cell} (X : ∀ π : Π, tracker_inv base π (f !!! π)) (π : Π) (Hlinw : linearized_writer X π) :
        ∀ π', tracker_inv base π' (<[π := Pending (op (linearized_writer_frame Hlinw)) (arg (linearized_writer_frame Hlinw))]> f !!! π').
      Proof.
        unfold linearized_writer in *. intros π'. destruct (decide (π = π')).
        - subst. rewrite Map.lookup_insert at 1. unfold linearized_writer_frame. destruct (X π'); try contradiction.
          rewrite e0. eapply tracker_inv_write_cas_pending; eauto.
        - rewrite Map.lookup_insert_ne at 1; eauto.
      Qed. *)

      (* Lemma foo : ∀ x, { f : P x & ∀ x, Q f x } { f : ∀ x, P x & ∀ x, Q f x } *)

      Lemma unlinearize_writer {base} {f : Π → status Π ReadWrite.Cell} (X : ∀ π : Π, tracker_inv base π (f !!! π)) (π : Π) (Hlinw : linearized_writer X π) :
        ∀ π' : Π, tracker_inv base π' (<[π := @Pending Π ReadWrite.t _ _ _ ReadWrite.Write (linearized_writer_frame Hlinw).(arg)]> f !!! π').
      Proof.
        intros π'. unfold insert, "!!!", Map.map_insert, Map.map_lookup_total, Map.lookup, Map.insert. destruct (decide (π = π')).
        - destruct e. unfold linearized_writer in *. unfold linearized_writer_frame. destruct (X π).
          + destruct Hlinw.
          + destruct Hlinw.
          + destruct Hlinw.
          + destruct Hlinw.
          + apply tracker_inv_write_cas_pending; assumption.
          + destruct Hlinw.
        - unfold insert, "!!!", Map.map_insert, Map.map_lookup_total, Map.lookup, Map.insert. apply X.
      Defined.

      Lemma unlinearize_writer_id {base} {f : Π → status Π ReadWrite.Cell} (X : ∀ π : Π, tracker_inv base π (f !!! π)) (π : Π) (Hlinw : linearized_writer X π) :
        update (unlinearize_writer X π Hlinw) = update X.
      Proof.
        extensionality π'. unfold unlinearize_writer, linearized_writer, update in *.
        unfold linearized_writer_frame. destruct (decide (π = π')).
        - destruct e. destruct (X π); try contradiction. rewrite Map.lookup_insert at 1. congruence.
        - assert (∀ v, <[π := v]>f !!! π' = f !!! π').
          { intros. now rewrite Map.lookup_insert_ne at 1. }
          now destruct (X π').
      Qed.

      (* Search (~ (?P \/ ?Q) -> ~ ?P /\ ~ ?Q). *)

      Lemma linearize_writers_step {base f} (X : ∀ π : Π, tracker_inv base π (f !!! π)) (l : gset Π) σ :
        (∀ π : Π, π ∈ l ↔ f !!! π ≠ Idle) →
          ∃ σ', δ_multi σ (update X) (list_of_list (linearized_writers X (elements l))) σ' f.
      Proof.
        intros Hout. pose proof linearized_writers_correct X l Hout as Hlin. clear Hout.
        generalize dependent X. revert f. assert (NoDup (elements l)) as Hunique by apply NoDup_elements. induction (elements l).
        - cbn. intros f X Hlin. exists σ. assert (update X = f) as Heq.
          { extensionality π'. unfold linearized_writer in Hlin. unfold update.
            pose proof Hlin π' as [Hfwd Hrev]. change (f π') with (f !!! π'). now destruct (X π'). }
          rewrite Heq. constructor.
        - intros f X Hlin. cbn. cbn in Hlin. assert (∀ v, <[a := f !!! a]>(<[a := v]>f) = f) as η.
          { intros v. erewrite <- Map.insert_insert; eauto. }
          pose proof (unlinearize_writer_id X a) as uwl. unfold linearized_writer, unlinearize_writer, linearized_writer_frame in uwl. destruct (X a).
          + inv Hunique. auto.
          + inv Hunique. auto.
          + inv Hunique. auto.
          + inv Hunique. auto.
          + exists (arg f0). rewrite <- η with (v := Pending f0.(op) f0.(arg)). cbn. 
            cbn in *. fold (linearized_writers X l0) in *. pose proof uwl I as uwl.
            remember (
              (λ π' : Π,
                match decide (a = π') as s
                return (tracker_inv base π' match s with
                | left eq_refl => _
                | right _ => f π'
                end)
                with
                | left e2 =>
                match e2 as e in (_ = π) return (tracker_inv base π
                match e with
                | eq_refl => _
                end) with
                | eq_refl => tracker_inv_write_cas_pending base a f0 e e0 e1
                end
                | right _ => X π'
                end)
            ) as X'. rewrite <- uwl. inversion Hunique. clear Hunique. destruct H0, H1.
            assert (linearized_writers X l1 = linearized_writers X' l1) as Hlineq.
            { clear IHl0 Hlin. induction l1.
              - reflexivity.
              - set_unfold in H2. apply not_or_and in H2 as [Hxnota Hxl1].
                inversion H3. destruct H0, H1. subst. cbn. destruct (decide (x = x0)).
                + contradiction.
                + cbn. destruct (X x0); auto.
                  f_equal; auto. }
            rewrite Hlineq.
            unshelve epose proof IHl0 H3 (<[x := @Pending Π ReadWrite.t _ _ _ ReadWrite.Write (arg f0)]> f) X' _ as [σ' Hσ'].
            * intros π'. rewrite <- Hlineq at 1.
              pose proof Hlin π' as [Hfwd Hrev]. split.
              -- intros Hin.
                 pose proof (Hfwd (or_introl Hin)) as Hlw.
                 unfold linearized_writer in *.
                 rewrite HeqX'. destruct (decide (x = π')).
                 ++ unfold not. intros. subst.
                    apply snoc_in_iff_list_in in Hin.
                    rewrite elem_of_list_In in Hin.
                    unfold linearized_writers in Hin.
                    apply filter_In in Hin as [Hin _].
                    now rewrite <- elem_of_list_In in Hin.
                 ++ assumption.
              -- clear Hfwd. intros Hlw. unfold linearized_writer in *.
                 rewrite HeqX' in Hlw. destruct (decide (x = π')).
                 ++ subst. contradiction.
                 ++ pose proof Hrev Hlw as [? | ?].
                    ** assumption.
                    ** now symmetry in H0.
            * rewrite e0. econstructor.
              -- eassumption.
              -- rewrite Map.lookup_insert at 1. eauto.
              -- constructor.
          + inv Hunique. auto.
      Qed.
        
(* 
      Definition linearize_writers {base} {f : Π → status Π ReadWrite.Cell} (X : ∀ π : Π, tracker_inv base π (f !!! π)) (l : gset Π) (Hfin : (∀ π : Π, π ∈ l ↔ f !!! π ≠ Idle)) : 
      { g : Π → status Π ReadWrite.Cell & { Y : ∀ π : Π, tracker_inv base π (g !!! π) & g = update Y } }.
      Proof.
        pose proof linearized_writers_correct X l Hfin as Hlin. generalize dependent X.
         (* apply forall_iff in Hlin as [Hfwd _]. *)
        clear Hfin. induction (elements l) as [|π πs IH].
        - intros. exists f. exists X. admit.
        - intros X Hlin.
          assert (g : Π → status Π ReadWrite.Cell).
          { intros π'. pose proof (Hlin π') as Hlinπ'. destruct (X π').
            - 
            - subst. pose proof Hlin π'. cbn in H0. }
          apply @existT.
        
        intros π'. pose proof Hfwd π' as Hlin. destruct (decide (π = π')).
          + subst. pose proof Hlin 
        exact (λ _, Idle).
      Defined. *)

      (* Lemma linearized_writers_correct {base f} (X : ∀ π : Π, tracker_inv base π (f !!! π)) (l : gset Π) π :
        (∀ π : Π, π ∈ l ↔ f !!! π ≠ Idle) → *)

      Lemma linearizable : FullTracker.invariant impl (λ c M, S c ⊆ M).
      Proof.
        unfold FullTracker.invariant, invariant, Procedure.invariant. intros r. induction r; intros.
        - inv H0. simpl.
          unfold initial_configuration, FullTracker.σ₀. simpl.
          unfold FullTracker.initial_tracker. unfold "⊆", relation_SubsetEq, refines.
          intros. inv H0. simpl. constructor. intros.
          pose proof (X π). inv X0. now unfold Map.lookup in *.
        - inversion H0. subst. inv H6. inv H2. simpl in *. inv H1.
          + unfold "⊆", relation_SubsetEq, refines. intros σ g HS.
            inv HS. pose proof X π. inv X0;
            try (erewrite <- H2 in H4; rewrite lookup_insert in H4; inv H4).
            simpl in *. inv H5. rewrite <- H8.
            assert (g = invoke (<[π := Idle]> g) π op0 arg0).
            { unfold invoke, insert, Map.map_insert.
              rewrite H1. unfold "!!!", Map.map_lookup_total.
              now rewrite Map.Dep.insert_insert. }
            eapply linearize_pending_intro with (πs := []) (f := g) (σ := ϵ base Cell).
            -- rewrite H4. econstructor.
              ++ apply IHr.
                ** auto.
                ** rewrite <- H8. econstructor. intros.
                    destruct (decide (π = π0)).
                    --- subst. unfold "!!!", insert, Map.map_lookup_total, Map.map_insert.
                        rewrite Map.Dep.lookup_insert. now constructor.
                    --- rewrite Map.lookup_insert_ne at 1 by assumption. apply tracker_inv_step_diff with (c := base).
                        +++ rewrite <- H2. now rewrite lookup_insert_ne.
                        +++ now rewrite H8.
                        +++ easy.
              ++ now rewrite Map.lookup_insert at 1.
            -- rewrite H8. constructor.
          + unfold "⊆", relation_SubsetEq, refines. intros σ g HS. pose proof outstanding_finite (Step r π Intermediate _) H0 σ g HS as [l Hfin]. inv HS.
            pose proof X π as Hinvπ. inv H9; [ idtac | exfalso; eapply no_goto; eauto ]. inv Hinvπ.
            -- rewrite <- H2 in H6. now rewrite lookup_insert in H6.
            -- simpl. rewrite <- H2 in H6. rewrite lookup_insert in H6. inv H6.
            -- simpl. cbn in *. rewrite <- H2 in H6. rewrite lookup_insert in H6. inv H8.
                cbn in *. rewrite H7 in H5. inv H10. inv H5. inv H13.
                inv H9. inv H8. inv H12. inv H5. rewrite lookup_insert in H7.
                inv H7. destruct ω. cbn in *.
                rewrite H6. rewrite H6 in H1. rewrite H6 in H2.
                eapply linearize_pending_intro 
                  with
                  (f := <[π := @Pending Π ReadWrite.t _ _ ReadWrite.Cell _ arg0]> g)
                  (πs := [] ,, π)
                  (σ := ϵ base Cell).
                instantiate (1 := ReadWrite.Read).
              ** eapply IHr; eauto. rewrite <- H6. econstructor.
                  intros π'. destruct (decide (π = π')).
                  --- subst. rewrite Map.lookup_insert at 1.
                      remember ({| op := _; pc := 0; arg := arg0; registers := ψ |}).
                      replace arg0 with (f.(arg)) by now rewrite Heqf.
                      replace ReadWrite.Read with (f.(op)).
                      constructor.
                      +++ assumption.
                      +++ now rewrite Heqf.
                      +++ now rewrite Heqf.
                  --- subst. rewrite Map.lookup_insert_ne at 1 by easy.
                      apply tracker_inv_step_diff with (c := base).
                      +++ rewrite <- H2. now rewrite lookup_insert_ne by assumption.
                      +++ congruence.
                      +++ easy.
              ** assert (g = <[π := (@Linearized Π ReadWrite.t _ _ _ (Map.lookup Cell (ϵ base)))]> (<[π := (@Pending Π ReadWrite.t _ _ _ ReadWrite.Read arg0)]> g)).
                { replace (Linearized (Map.lookup Cell (ϵ base))) with (g !!! π).
                  unfold "!!!", Map.map_lookup_total, insert, Map.map_insert. now rewrite Map.Dep.insert_insert. }
                rewrite H5. econstructor. 
                --- rewrite <- H5. econstructor.
                --- now rewrite Map.lookup_insert at 1.
                --- econstructor.
            -- simpl. cbn in *. rewrite <- H2 in H6. rewrite lookup_insert in H6. inv H8.
               cbn in *. rewrite H7 in H5. inv H10. inv H5. inv H12.
               inv H8. inv H11. inv H5. destruct ω. cbn in *.
               rewrite H6. rewrite H6 in H2. eapply linearize_pending_intro with (f := g).
               ++ apply IHr.
                  ** assumption.
                  ** constructor. intros π'. destruct (decide (π = π')).
                     --- subst. rewrite <- H1.
                         remember ({| op := _; pc := 0; arg := arg0; registers := ψ |}).
                         replace (Pending _ _) with (Pending f.(op) f.(arg)) by now rewrite Heqf.
                         eapply tracker_inv_invoke.
                         +++ assumption.
                         +++ now rewrite Heqf. 
                     --- subst. unfold "!!!", Map.map_lookup_total. apply tracker_inv_step_diff with (c := base).
                         +++ rewrite <- H2. now rewrite lookup_insert_ne by assumption.
                         +++ congruence.
                         +++ easy.
               ++ rewrite H6. econstructor.
            -- simpl. cbn in *. rewrite <- H2 in H6. rewrite lookup_insert in H6. inv H8.
              cbn in *. rewrite H7 in H5. inv H10. inv H5. inv H14.
              inv H8. inv H13. rewrite lookup_insert in H9. inv H9. inv H5. destruct ω. cbn in *.
              exfalso. apply H11. unfold Map.lookup. congruence.
            -- cbn in *. rewrite <- H2 in H6. rewrite lookup_insert in H6. inv H8.
              cbn in *. rewrite H7 in H5. inv H10. inv H5. inv H6.
              inv H8. inv H11. inv H9. inv H10. inv H13. destruct ω, ω0. inv H5.
              ++ remember {| op := _; pc := 1; arg := σ; registers := ψ' |}.
                 rewrite <- Map.insert_insert with (k := π) (v := Pending f.(op) f.(arg)).
                 apply linearize_pending_intro
                  with 
                    (πs := list_of_list (linearized_writers X (elements l)) ,, π)
                    (f := <[π := Pending f.(op) f.(arg)]>(update X))
                    (σ := ϵ (base_configuration (final r)) Cell).
                ** eapply IHr; eauto. econstructor.
                    intros π'. destruct (decide (π = π')).
                    --- subst. rewrite Map.lookup_insert at 1. 
                        now apply tracker_inv_write_cas_pending.
                    --- subst. rewrite Map.lookup_insert_ne at 1 by easy.
                        unfold "!!!", Map.map_lookup_total, Map.lookup in *.
                        unfold update. destruct (X π').
                        +++ eapply tracker_inv_idle. rewrite <- H2 in e.
                            now rewrite lookup_insert_ne in e by assumption.
                        +++ econstructor; auto. rewrite <- H2 in e.
                            now rewrite lookup_insert_ne in e by assumption.
                        +++ econstructor; eauto.
                            rewrite <- H2 in e. now rewrite lookup_insert_ne in e by assumption.
                        +++ econstructor; eauto.
                            rewrite <- H2 in e. now rewrite lookup_insert_ne in e by assumption.
                        +++ rewrite e0. eapply tracker_inv_write_cas_pending; eauto.
                            rewrite <- H2 in e. now rewrite lookup_insert_ne in e by assumption.
                        +++ eapply tracker_inv_write_response; eauto.
                            rewrite <- H2 in e. now rewrite lookup_insert_ne in e by assumption.
                 ** cbn. rewrite <- H1 at 1.
                    pose proof linearize_writers_step X l (ϵ (base_configuration (final r)) Cell) Hfin as [σ' Hmulti]. econstructor.
                    --- apply δ_multi_mod.
                        +++ pose proof linearized_writers_correct X l Hfin π as Hlin.
                            unfold not. intros Hinlin. apply Hlin in Hinlin. unfold linearized_writer in *. destruct (X π); try contradiction.
                            rewrite <- H2 in e. rewrite lookup_insert in e. inv e.
                        +++ eassumption.
                    --- now rewrite Map.lookup_insert at 1.
                    --- subst. cbn. fold (Map.lookup Cell (Map.insert Cell σ (ϵ (base_configuration (final r))))).
                        rewrite Map.Dep.lookup_insert. constructor.          
              ++ rewrite Map.Dep.η in H6 by assumption.
                 apply linearize_pending_intro with  (πs := []) (f := g) (σ := ϵ base Cell).
                 ** auto. apply IHr; auto. rewrite <- H6. econstructor. intros π'.
                    destruct (decide (π = π')).
                    --- subst. rewrite <- H1. eapply tracker_inv_write_cas_linearized; eauto.
                    --- apply tracker_inv_step_diff with (c := base).
                        +++ rewrite <- H2. now rewrite lookup_insert_ne.
                        +++ congruence.
                        +++ auto.
                 ** rewrite Map.Dep.η. rewrite H6. constructor.
          + unfold "⊆", relation_SubsetEq, refines. intros σ g HS.
            inv HS. pose proof X π as Hinv. inv Hinv; erewrite <- H2 in H5; rewrite lookup_delete in H5; try discriminate.
            clear H5. cbn in *. inv H0. inv H11. inv H6. inv H14.
            assert (g = ret (<[π := Linearized v]> g) π).
            { unfold ret. rewrite H1. unfold insert, Map.map_insert, lookup_total, Map.map_lookup_total.
              now rewrite Map.Dep.insert_insert. }
            apply linearize_pending_intro with (πs := []) (f := g) (σ := ϵ base Cell).
            -- rewrite H0. econstructor.
              ++ apply IHr.
                ** assumption.
                ** destruct op0.
                  --- inv H9. clear H19. pose proof return_pc_read H6 H13. subst. inv H6. inv H13. inv H12.
                      constructor. intros π'. destruct (decide (π = π')).
                      +++ subst. rewrite Map.lookup_insert at 1. eapply tracker_inv_read_return; eauto.
                      +++ rewrite Map.lookup_insert_ne at 1 by assumption.
                          apply tracker_inv_step_diff with (c := base).
                          *** rewrite <- H2. now rewrite lookup_delete_ne by assumption.
                          *** congruence.
                          *** auto.
                  --- inv H9. clear H19. pose proof return_pc_write H6 H13. subst. inv H6. inv H13. inv H12.
                      constructor. intros π'. destruct (decide (π = π')).
                      +++ subst. rewrite Map.lookup_insert at 1. eapply tracker_inv_write_response; eauto.
                      +++ rewrite Map.lookup_insert_ne at 1 by assumption.
                          apply tracker_inv_step_diff with (c := base).
                          *** rewrite <- H2. now rewrite lookup_delete_ne by assumption.
                          *** congruence.
                          *** auto.
              ++ now rewrite Map.lookup_insert at 1.
            -- constructor.
      Qed.

End RWCAS.

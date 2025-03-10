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

Inductive snoc_list (A : Type) : Type :=
  | Nil
  | Snoc (h : snoc_list A) (t : A).

Arguments Nil {_}.
Arguments Snoc {_}.

Notation "⟨⟩" := Nil (format "⟨⟩") : list_scope.
Notation "⟨ x ⟩" := (Snoc Nil x) : list_scope.
Notation "⟨ x ; y ; .. ; z ⟩" := (Snoc .. (Snoc (Snoc Nil x) y) .. z) : list_scope.

Infix ",," := Snoc (at level 50, left associativity).

Inductive SnocForall {A} (P : A → Prop) : snoc_list A → Prop :=
  | SnocForall_nil : SnocForall P ⟨⟩
  | SnocForall_cons x xs : SnocForall P xs → P x → SnocForall P (xs ,, x).

Inductive δ_multi {Π Ω} `{EqDecision Π, Object Π Ω} {ω : Ω} : (type ω).(Σ) → (Π → status Π ω) → snoc_list Π → (type ω).(Σ) → (Π → status Π ω) → Prop :=
  | δ_multi_refl σ f : δ_multi σ f ⟨⟩ σ f
  | δ_multi_step f σ π πs op arg σ' res σ'' f' :
    δ_multi σ (f : Π → status Π ω) πs σ' (f' : Π → status Π ω) →
    (* if [π] has invoked [op(arg)], but not returned *)
    f' !!! π = Pending op arg →
    (* And (σ', res) ∈ δ(σ, π, op, arg) *)
    (type ω).(δ) σ' π op arg σ'' res →
    δ_multi σ f (πs ,, π) σ'' (<[π := Linearized res]>f').

(* Lemma δ_multi_trans {Π Ω} `{EqDecision Π, Object Π Ω} {ω : Ω} σ σ' σ'' (f f' f'' : Π → status Π ω) : 
  δ_multi σ f σ' f' → δ_multi σ' f' σ'' f'' → δ_multi σ f σ'' f''.
Proof.
  intros Hmany Hmany'. generalize dependent Hmany. revert σ f. induction Hmany'.
  - tauto.
  - econstructor; eauto.
Qed. *)

Definition invoke `{EqDecision Π, Object Π Ω} {ω} (f : Π → status Π ω) (π : Π) (op : (type ω).(OP)) (arg : Value.t) : Π → status Π ω :=
  Map.insert π (Pending op arg) f.

Definition ret `{EqDecision Π, Object Π Ω} {ω} (f : Π → status Π ω) (π : Π) := Map.insert π Idle f.

(* A meta configuration relates states of the implemented object and the status of each process *)
Definition meta_configuration Π {Ω} `{Object Π Ω} (ω : Ω) := (type ω).(Σ) → (Π → status Π ω) → Prop.

Definition inhabited {A B} (R : A → B → Prop) : Prop := ∃ a b, R a b.

Definition singleton {A B} (R : A → B → Prop) (x : A) (y : B) : Prop :=
  R x y ∧ ∀ x' y', R x' y' → x = x' ∧ y = y'.

(* Variant evolve_inv `{EqDecision Π, Object Π Ω} {ω} (op : (type ω).(OP)) (π : Π) (arg : Value.t) (C : meta_configuration Π ω) : meta_configuration Π ω :=
  evolve_inv_intro σ f πs σ' f' :
    (* If (σ, f) ∈ C *)
    C σ f →
    f !!! π = Idle →
    (* And atomic configuration (σ', f') results after linearizing every outstanding operation of [πs] *)
    δ_multi σ (invoke f π op arg) πs σ' f' →
    (* Then (σ', f') is in the resulting metaconfiguration *)
    evolve_inv op π arg C σ' f'.

Lemma evolve_inv_monotone `{EqDecision Π, Object Π Ω} {ω} (op : (type ω).(OP)) (π : Π) (arg : Value.t) : monotone (evolve_inv op π arg).
Proof.
  unfold monotone. intros x y Hless.
  intros σ f Hevolve. inv Hevolve. econstructor; eauto.
Qed. *)

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

Fixpoint behavior {C Π : Type} `{Object Π Ω} {ω : Ω} (r : run C Π ω) : snoc_list (Π * line Π ω) :=
  match r with
  | Initial _ => ⟨⟩
  | Step r π l c =>
      match l with
      | Invoke _ _ | Response _ => behavior r ,, (π, l)
      | Intermediate => behavior r
      end
  end.

Inductive subsequence {A : Type} : snoc_list A → snoc_list A → Prop :=
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

Module Augmented.

  Section Auxillary.

  Context {Aux : Type}.

  Variable Σ : Aux → Type.

  Variable σ₀ : Map.dependent Aux Σ.

  Record configuration Π Ω {Ω₀} `{Countable Π, Object Π Ω, Object Π Ω₀} (ω : Ω₀) := {
    base_configuration : Implementation.configuration Π Ω ω;
    auxiliary_state : Map.dependent Aux Σ;
  }.

  Arguments base_configuration : default implicits.
  Arguments auxiliary_state : default implicits.

  Definition run Π Ω {Ω₀} `{Countable Π, Object Π Ω, Object Π Ω₀} (ω : Ω₀) := run (configuration Π Ω ω) Π ω.

  Section Semantics.

    Context {Π Ω₀ Ω : Type} {ω : Ω₀}.

    Context `{Countable Π, Object Π Ω₀, Object Π Ω}.

    Variable impl : Implementation Π Ω ω.

    Definition initial_configuration := {| auxiliary_state := σ₀; base_configuration := Implementation.initial_configuration impl |}.

    (* Unlike normal objects, auxiliary objects can access other processes' local state *)
    Variable step_auxiliary : Map.dependent Aux Σ → Π → line Π ω → Implementation.configuration Π Ω ω → Map.dependent Aux Σ → Prop.

    Variant step_augmented (c : configuration Π Ω ω) (π : Π) (l : line Π ω) : configuration Π Ω ω → Prop :=
      | step_augmented_intro base f :
        Implementation.step_configuration impl c.(base_configuration) π l base →
          step_auxiliary c.(auxiliary_state) π l base f →
            step_augmented c π l {| auxiliary_state := f; base_configuration := base |}.

    Definition Run := Run initial_configuration step_augmented.

    Definition invariant := invariant initial_configuration step_augmented.

    Fixpoint project r : Implementation.run Π Ω ω :=
      match r with
      | Initial c => Initial c.(base_configuration)
      | Step r π l c => Step (project r) π l c.(base_configuration)
      end.

    (* Lemma project_sound r : Run r → Implementation.Run impl (project r).
    Proof.
      induction r; intros.
      - destruct c. simpl in *. econstructor. *)

  End Semantics.
  End Auxillary.
End Augmented.

Arguments Augmented.base_configuration : default implicits.
Arguments Augmented.auxiliary_state : default implicits.

(* Inductive coupled `{Countable Π, Object Π Ω, Object Π Ω₀} {ω : Ω₀} : Implementation.run Π Ω ω → Augmented.run Π Ω ω → Prop :=
  | coupled_initial c tracker : coupled (Initial c) (Initial {| Augmented.tracker := tracker; Augmented.base_configuration := c|})
  | coupled_step r r' π l tracker base :
    coupled r r' →
    coupled
      (Step r π l base)
      (Step r' π l {| Augmented.tracker := tracker; Augmented.base_configuration := base |}). *)

(* relation (run (aumented_configuration Π Ω ω) Π ω) :=
  | coupled_initial c : coupled (Initial c) (Initial c)
  | coupled_step r r' π l tracker tracker' outstanding ϵ :
    coupled r r' →
    coupled
      (Step r π l {| tracker := tracker; outstanding := outstanding; ϵ := ϵ |})
      (Step r' π l {| tracker := tracker'; outstanding := outstanding; ϵ := ϵ |}). *)

(* Variant linearization `{Countable Π, Object Π Ω₀, Object Π Ω} {ω : Ω₀} (impl : Implementation Π Ω ω) (r : run Π Ω ω) (atomic : run Π (sing ω) ω) : Prop :=
  linearization_intro : 
    Run impl r → Run (atomic_implementation ω impl.(initial_state)) atomic → behavior r = behavior atomic → linearization impl r atomic. *)


Require Import Coq.Logic.Classical.

Module PartialTracker.

  Section Adequacy.

  Context {Π Ω₀ Ω : Type} {ω : Ω₀}.

  Context `{Countable Π, Object Π Ω₀, Object Π Ω}.

  Variable impl : Implementation Π Ω ω.

  Variant initial_tracker : meta_configuration Π ω :=
    initial_tracker_intro f : (∀ π, f !!! π = Idle) → initial_tracker impl.(initial_state) f.

  Section Soundness.

    Context {Aux : Type}.

    (* The metaconfiguration *)
    Variable M : Aux.

    Variable Σ : Aux → Type.

    Variable σ₀ : Map.dependent Aux Σ.

    (* The metaconfiguration has the appropriate type *)
    Hypothesis M_meta_configuration : Σ M = meta_configuration Π ω.

    Hint Rewrite M_meta_configuration : core.

    Definition coerce : Σ M → meta_configuration Π ω.
    Proof.
      rewrite M_meta_configuration. exact (λ x, x).
    Defined.

    Variable step_auxiliary : 
      Map.dependent Aux Σ → Π → line Π ω → Implementation.configuration Π Ω ω → Map.dependent Aux Σ → Prop.

    Import Augmented.

    Definition run := run Σ Π Ω ω.
  
    Definition Run := Run Σ σ₀ impl step_auxiliary.

    Definition tracker (r : run) := coerce ((final r).(auxiliary_state) M).

    Variable refinement : 
      ∀ r π l base f',
        Run r →
          step_auxiliary (final r).(auxiliary_state) π l base f' → coerce (f' M) ⊆ evolve π l (tracker r).

    Variant linearizable_run (r : run) σ f : Prop :=
      linearizable_intro (atomic : Atomic.run Π ω) :
        Atomic.Run impl.(initial_state) atomic →
          behavior r = behavior atomic →
            final atomic = (σ, f) →
              linearizable_run r σ f.

    Definition tracker_sound (r : run) :=
      ∀ σ f, tracker r σ f → linearizable_run r σ f.

    Lemma sound_linearizations r atomic σ σ' πs f f' :
      Run r →
        Atomic.Run impl.(initial_state) atomic →
          behavior atomic = behavior r →
            tracker r σ f →
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
      eapply refinement in H2; eauto. inv H2. inv H5. remember (invoke f2 π op arg) in H6. induction H6.
      - intros. unfold tracker_sound in *.
        apply IH in H2. inversion H2.
        eapply linearizable_intro with (atomic := Step atomic π (Invoke op arg) _).
        + econstructor.
          * assumption.
          * rewrite H8. now econstructor. 
        + simpl. now rewrite H6. 
        + simpl. now rewrite Heqs.
      - intros. unfold tracker_sound in *. simpl in *.
        apply IH in H2 as ?. inv H10. eapply IHδ_multi in H2. inv H2.
        eapply linearizable_intro with (atomic := Step atomic0 π0 Intermediate _).
        + econstructor.
          * assumption.
          * rewrite H17. simpl in *. econstructor; eauto.
        + assumption.
        + easy.
        + reflexivity.
    Qed.

    Lemma sound_intermediate r π c :
      Run (Step r π Intermediate c) → tracker_sound r → tracker_sound (Step r π Intermediate c).
    Proof.
      intros HRunStep IH. inv HRunStep. inv H7. inv H2. unfold tracker_sound. simpl. intros.
      eapply refinement in H2; eauto. inv H2. induction H8.
      - intros. unfold tracker_sound in *.
        apply IH in H7. inv H7.
        now eapply linearizable_intro with (atomic := atomic).
      - intros. unfold tracker_sound in *. simpl in *.
        apply IH in H7 as ?. inv H11. eapply IHδ_multi in H7. inv H7.
        eapply linearizable_intro with (atomic := Step atomic0 π0 Intermediate _).
        + econstructor.
          * assumption.
          * rewrite H16. simpl in *. econstructor; eauto.
        + assumption.
        + reflexivity.
    Qed.

    Lemma sound_response r π v c :
      Run (Step r π (Response v) c) → tracker_sound r → tracker_sound (Step r π (Response v) c).
    Proof.
      intros HRunStep IH. inv HRunStep. inv H7. inv H2. unfold tracker_sound. simpl. intros.
      eapply refinement in H2; eauto. inv H2. inv H5. remember (ret f3 π) in H7. induction H7.
      - intros. unfold tracker_sound in *.
        apply IH in H2. inversion H2.
        eapply linearizable_intro with (atomic := Step atomic π (Response v) _).
        + econstructor.
          * assumption.
          * rewrite H9. now econstructor. 
        + simpl. now rewrite H7. 
        + simpl. now rewrite Heqd.
      - intros. unfold tracker_sound in *. simpl in *.
        apply IH in H2 as ?. inv H12. eapply IHδ_multi in H2; auto. inv H2.
        eapply linearizable_intro with (atomic := Step atomic0 π0 Intermediate _).
        + econstructor.
          * assumption.
          * rewrite H17. simpl in *. econstructor; eauto.
        + assumption.
        + easy.
    Qed.

  End Soundness.

  Section StrongLinearizability.

  Section Completeness.

    Definition unique {A B} (P : A → B → Prop) : Prop := ∀ a b b', P a b → P a b' → b = b'.

    Definition linearization (r : Implementation.run Π Ω ω) (atomic : Atomic.run Π ω) := Atomic.Run impl.(initial_state) atomic ∧ behavior r = behavior atomic.

    Hypothesis L : Implementation.run Π Ω ω → Atomic.configuration Π ω → Prop.

    Hypothesis L_unique : unique L.

    Hypothesis L_range : ∀ r, Implementation.Run impl r → ∃ conf, L r conf.

    Hypothesis L_wf : ∀ r conf, L r conf → ∃ atomic, linearization r atomic ∧ final atomic = conf.

    Variant Aux : Set := M | History.

    Instance aux_eq_dec : EqDecision Aux.
    Proof. solve_decision. Defined.

    Definition Σ (aux : Aux) :=
      match aux with
      | M => meta_configuration Π ω
      | History => Implementation.run Π Ω ω
      end.

    Variant step_auxiliary (aux : Map.dependent Aux Σ) (π : Π) (l : line Π ω) (base : Implementation.configuration Π Ω ω) : Map.dependent Aux Σ → Prop :=
      step_auxiliary_intro :
        step_auxiliary aux π l base 
          (λ a,
            let history := Step (aux History) π l base in
            match a with
            | M => λ σ f, L history (σ, f)
            | History => history
            end).

    Definition σ₀ : Map.dependent Aux Σ.
    Proof.
      intros [ | ]; cbn.
      - exact initial_tracker.
      - exact (Initial (Implementation.initial_configuration impl)).
    Defined.

    (* Check Augmented.invariant Σ σ₀ impl step_auxiliary (λ _, True). *)

    Import Augmented.

    Lemma completeness :
      ∀ r π l base f',
        Run Σ σ₀ impl step_auxiliary r →
          step_auxiliary (final r).(auxiliary_state) π l base f' → f' M ⊆ evolve π l ((final r).(auxiliary_state) M).
    Proof.
      induction r eqn:?.
      (* Is actually trivial, does not require induction *)
    Admitted.
    
    End Completeness.
  
    End StrongLinearizability.

End Adequacy.

End PartialTracker.

Module FullTracker.

  Definition Aux : Type := ().

  Definition Σ Π `{Object Π Ω} (ω : Ω) : Aux → Type := const (meta_configuration Π ω).

  Definition run Π Ω `{Countable Π, Object Π Ω, Object Π Ω₀} (ω : Ω₀) := Augmented.run (Σ Π ω) Π Ω ω.

  Definition configuration Π Ω `{Countable Π, Object Π Ω, Object Π Ω₀} (ω : Ω₀) := Augmented.configuration (Σ Π ω) Π Ω ω.

  Section Adequacy.

  Context {Π Ω₀ Ω : Type} {ω : Ω₀}.

  Context `{Countable Π, Object Π Ω₀, Object Π Ω}.

  Variable impl : Implementation Π Ω ω.

  Definition initial_tracker := PartialTracker.initial_tracker impl.

  Definition σ₀ : Map.dependent Aux (Σ Π ω) := const initial_tracker.

  Variant step_auxiliary (C : Map.dependent Aux (Σ Π ω)) (π : Π) (l : line Π ω) (c : Implementation.configuration Π Ω ω) : Map.dependent Aux (Σ Π ω) → Prop :=
    | step_auxiliary_intro : step_auxiliary C π l c (const (evolve π l (C tt))).

  Definition Run := Augmented.Run (Σ Π ω) σ₀ impl step_auxiliary.

  Definition tracker (c : configuration Π Ω ω) := c.(Augmented.auxiliary_state) tt.

  Definition invariant p := Augmented.invariant (Σ Π ω) σ₀ impl step_auxiliary (λ c, p c.(Augmented.base_configuration) (c.(Augmented.auxiliary_state) tt)).

  End Adequacy.

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

    Import Augmented.
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
      Qed.

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

      (* Lemma outstanding_finite : FullTracker.invariant impl (λ c M, ∀ σ f, S c σ f → ∃ l, ∀ π : Π, In π l ↔ f !!! π ≠ Idle).
      Proof.
        unfold FullTracker.invariant, invariant, Procedure.invariant. intros r. induction r; intros Hrun.
        - inv Hrun. cbn in *. intros σ f HS. exists []. intros. inv HS.
          pose proof X π as Hinv. inv Hinv. split.
          + intros. inv H2.
          + intros. contradiction.
        - inv Hrun. inv H5. inv H1. inv H0.
          + cbn in *. intros σ f HS.
            pose proof IHr H2 as IH. pose proof IH σ (<[π := Idle]>f) as IH.
            inv HS. pose proof X π as Hinv. inv Hinv;
            (rewrite <- H1 in H3; rewrite lookup_insert in H3; inv H3).
            cbn in *.
            assert (S (base_configuration (final r)) (ϵ base Cell) (<[π:=Idle]> f)) as HS.
            { rewrite <- H7. econstructor. intros π'.
              destruct (decide (π = π')).
              - subst. unfold insert, Map.map_insert, "!!!", Map.map_lookup_total. 
                rewrite Map.lookup_insert. now econstructor.
              - subst. unfold insert, Map.map_insert, "!!!", Map.map_lookup_total. 
                rewrite Map.lookup_insert_ne by assumption.
                apply tracker_inv_step_diff with (c := base).
                + rewrite <- H1. now rewrite lookup_insert_ne by assumption.
                + now rewrite H7.
                + auto. }
            pose proof IH HS as [l Hfin].
            exists (π :: l).
            intros π'. split.
            * intros Hmem. inv Hmem.
              -- unfold not. rewrite <- H0. intros. discriminate.
              -- pose proof Hfin π' as [Hfwd _]. destruct (decide (π = π')).
                ++ subst. unfold insert, "!!!", Map.map_insert, Map.map_lookup_total in *.
                   rewrite Map.lookup_insert in Hfwd. exfalso.
                   pose proof Hfwd H3. contradiction.
                ++ unfold insert, "!!!", Map.map_insert, Map.map_lookup_total in *.
                   rewrite Map.lookup_insert_ne in Hfwd by assumption.
                   auto.
            * intros Hneq. destruct (decide (π = π')).
              -- subst. cbn. tauto.
              -- cbn. right. pose proof Hfin π' as [_ Hrev].
                 unfold insert, "!!!", Map.map_insert, Map.map_lookup_total in *.
                 rewrite Map.lookup_insert_ne in Hrev by assumption.
                 auto.
          + cbn in *. intros σ F HS. inv H8.
            * admit.
            * inv H9.
          pose proof IHr H2 as IH. pose proof IH σ (<[π := Pending ]>F) as IH.
          inv HS. pose proof X π as Hinv. inv Hinv;
          (rewrite <- H1 in H3; rewrite lookup_insert in H3; inv H3).
          cbn in *. inv
          assert (S (base_configuration (final r)) (ϵ base Cell) (<[π:=Idle]> F)) as HS.
          { rewrite <- H7. econstructor. intros π'.
            destruct (decide (π = π')).
            - subst. unfold insert, Map.map_insert, "!!!", Map.map_lookup_total. 
              rewrite Map.lookup_insert. now econstructor.
            - subst. unfold insert, Map.map_insert, "!!!", Map.map_lookup_total. 
              rewrite Map.lookup_insert_ne by assumption.
              apply tracker_inv_step_diff with (c := base).
              + rewrite <- H1. now rewrite lookup_insert_ne by assumption.
              + now rewrite H7.
              + auto. }
          pose proof IH HS as [l Hfin].
          exists (π :: l).
          intros π'. split.
          * intros Hmem. inv Hmem.
            -- unfold not. rewrite <- H0. intros. discriminate.
            -- pose proof Hfin π' as [Hfwd _]. destruct (decide (π = π')).
              ++ subst. unfold insert, "!!!", Map.map_insert, Map.map_lookup_total in *.
                 rewrite Map.lookup_insert in Hfwd. exfalso.
                 pose proof Hfwd H3. contradiction.
              ++ unfold insert, "!!!", Map.map_insert, Map.map_lookup_total in *.
                 rewrite Map.lookup_insert_ne in Hfwd by assumption.
                 auto.
          * intros Hneq. destruct (decide (π = π')).
            -- subst. cbn. tauto.
            -- cbn. right. pose proof Hfin π' as [_ Hrev].
               unfold insert, "!!!", Map.map_insert, Map.map_lookup_total in *.
               rewrite Map.lookup_insert_ne in Hrev by assumption.
               auto. *)


      Lemma linearizable : FullTracker.invariant impl (λ c M, inhabited (S c) ∧ S c ⊆ M ∧ (∀ σ f, S c σ f → (∃ l, ∀ π, In π l ↔ f !!! π ≠ Idle))).
      Proof.
        unfold FullTracker.invariant, invariant, Procedure.invariant. intros r. induction r; intros.
        - inv H0. simpl. split.
          + unfold initial_configuration. eexists. eexists. econstructor. intros.
            now econstructor.
          + split.
            * unfold initial_configuration, FullTracker.σ₀. simpl.
              unfold FullTracker.initial_tracker. unfold "⊆", relation_SubsetEq, refines.
              intros. inv H0. simpl. constructor. intros.
              pose proof (X π). inv X0. now unfold Map.lookup in *.
            * intros σ f HS. exists []. intros. inv HS. split.
              -- intros Hin. inv Hin.
              -- intros Hneq. pose proof X π as Hinv. inv Hinv.   
        - inversion H0. subst. inv H6. inv H2. simpl in *. inv H1.
          + simpl in *. repeat split.
            * admit.
            * unfold "⊆", relation_SubsetEq, refines. intros σ g HS.
              inv HS. pose proof X π. inv X0;
              try (erewrite <- H2 in H4; rewrite lookup_insert in H4; inv H4).
              simpl in *. inv H5. rewrite <- H8.
              assert (g = invoke (<[π := Idle]> g) π op0 arg0).
              { unfold invoke, insert, Map.map_insert.
                rewrite H1. unfold "!!!", Map.map_lookup_total.
                now rewrite Map.insert_insert. }
              eapply linearize_pending_intro with (πs := ⟨⟩) (f := g) (σ := ϵ base Cell).
              -- rewrite H4. econstructor.
                ++ apply IHr.
                  ** auto.
                  ** rewrite <- H8. econstructor. intros.
                     destruct (decide (π = π0)).
                     --- subst. unfold "!!!", insert, Map.map_lookup_total, Map.map_insert.
                         rewrite Map.lookup_insert. now constructor.
                     --- unfold insert, "!!!", Map.map_insert, Map.map_lookup_total.
                         rewrite Map.lookup_insert_ne; auto. apply tracker_inv_step_diff with (c := base).
                      +++ rewrite <- H2. now rewrite lookup_insert_ne.
                      +++ now rewrite H8.
                      +++ easy.
                ++ unfold "!!!", insert, Map.map_lookup_total, Map.map_insert.
                   now rewrite Map.lookup_insert.
              -- rewrite H8. constructor.
            * admit.
          + repeat split.
            * admit.
            * unfold "⊆", relation_SubsetEq, refines. intros σ g HS. inv HS.
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
                    (f := Map.insert π (@Pending Π ReadWrite.t _ _ ReadWrite.Cell _ arg0) g)
                    (πs := ⟨⟩ ,, π)
                    (σ := ϵ base Cell).
                 instantiate (1 := ReadWrite.Read).
                ** eapply IHr; eauto. rewrite <- H6. econstructor.
                   intros π'. destruct (decide (π = π')).
                   --- subst. unfold "!!!", Map.map_lookup_total. rewrite Map.lookup_insert.
                       remember ({| op := _; pc := 0; arg := arg0; registers := ψ |}).
                       replace arg0 with (f.(arg)) by now rewrite Heqf.
                       replace ReadWrite.Read with (f.(op)).
                       constructor.
                       +++ assumption.
                       +++ now rewrite Heqf.
                       +++ now rewrite Heqf.
                  --- subst. unfold "!!!", Map.map_lookup_total. rewrite Map.lookup_insert_ne by easy.
                      apply tracker_inv_step_diff with (c := base).
                      +++ rewrite <- H2. now rewrite lookup_insert_ne by assumption.
                      +++ congruence.
                      +++ easy.
                ** assert (g = Map.insert π (@Linearized Π ReadWrite.t _ _ _ (Map.lookup Cell (ϵ base))) (Map.insert π (@Pending Π ReadWrite.t _ _ _ ReadWrite.Read arg0) g)).
                  { replace (Linearized (Map.lookup Cell (ϵ base))) with (g !!! π).
                    unfold "!!!", Map.map_lookup_total. now rewrite Map.insert_insert. }
                  rewrite H5. econstructor; [
                      idtac
                    | unfold "!!!", Map.map_lookup_total; now rewrite Map.lookup_insert
                    | unfold Map.lookup; constructor
                  ].
                  rewrite <- H5. econstructor.
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
              -- admit.
                cbn in *. rewrite <- H2 in H6. rewrite lookup_insert in H6. inv H8.
                (* cbn in *. rewrite H7 in H5. inv H10. inv H5. inv H6.
                inv H8. inv H11. inv H9. inv H10. inv H13. destruct ω.
                inv H5.
                ++ destruct ω0.
                eapply linearize_pending_intro with ().
                rewrite H6. rewrite H6 in H2.
                 eapply linearize_pending_intro 
                    with
                    (f := Map.insert π (@Pending Π ReadWrite.t _ _ ReadWrite.Cell _ arg0) g)
                    (πs := ⟨⟩ ,, π)
                    (σ := ϵ base Cell).
                  instantiate (1 := ReadWrite.Read).
                ** eapply IHr; eauto. rewrite <- H10. econstructor.
                    intros π'. destruct (decide (π = π')).
                    --- subst. unfold "!!!", Map.map_lookup_total. rewrite Map.lookup_insert.
                        remember ({| op := _; pc := 0; arg := arg0; registers := ψ |}).
                        replace arg0 with (f.(arg)) by now rewrite Heqf.
                        replace ReadWrite.Read with (f.(op)).
                        constructor.
                        +++ assumption.
                        +++ now rewrite Heqf.
                        +++ now rewrite Heqf.
                  --- subst. unfold "!!!", Map.map_lookup_total. rewrite Map.lookup_insert_ne by easy.
                      apply tracker_inv_step_diff with (c := base).
                      +++ rewrite <- H2. now rewrite lookup_insert_ne by assumption.
                      +++ congruence.
                      +++ easy. *)
                ** assert (g = Map.insert π (@Linearized Π ReadWrite.t _ _ _ (Map.lookup Cell (ϵ base))) (Map.insert π (@Pending Π ReadWrite.t _ _ _ ReadWrite.Read arg0) g)).
                  { replace (Linearized (Map.lookup Cell (ϵ base))) with (g !!! π).
                    unfold "!!!", Map.map_lookup_total. now rewrite Map.insert_insert. }
                  rewrite H5. econstructor; [
                      idtac
                    | unfold "!!!", Map.map_lookup_total; now rewrite Map.lookup_insert
                    | unfold Map.lookup; constructor
                  ].
                  rewrite <- H5. econstructor. (* Impossible? *)
          + split.
            * admit.
            * unfold "⊆", relation_SubsetEq, refines. intros σ g HS.
              inv HS. pose proof H1 π. inv H5;
              try (erewrite <- H2 in H7; now rewrite lookup_delete in H7).
              clear H7. simpl in *.
              assert (g = ret (Map.insert π (Linearized v) g) π).
              { extensionality π'. unfold ret, Map.insert. destruct (decide (π = π')).
                - destruct e. simpl in *. symmetry. assumption.
                - reflexivity. }
              apply linearize_pending_intro with (πs := ⟨⟩) (f := g) (σ := ϵ base Cell).
              -- rewrite H5. econstructor.
                ++ apply IHr.
                  ** assumption.
                  ** inv H9. pose proof return_state_constant H8 H13 as [_ Hϵ].
                    rewrite <- Hϵ. constructor. intros π'.
                    destruct (decide (π = π')).
                    --- subst. cbn in *. rewrite Map.lookup_insert. destruct op0.
                      *** pose proof return_pc_read H8 H13. subst. inv H8.
                          inv H13. inv H11. eapply tracker_inv_read_return; eauto.
                      *** pose proof return_pc_write H8 H13. subst. inv H8.
                      inv H13. inv H11. eapply tracker_inv_write_response; eauto.
                    --- rewrite Map.lookup_insert_ne by assumption.
                        apply tracker_inv_step_diff with (c := base).
                        +++ rewrite <- H2. now rewrite lookup_delete_ne.
                        +++ congruence.
                        +++ easy.
                ++ now rewrite Map.lookup_insert.
              -- constructor.
      Admitted.

End RWCAS.

Module FullTracker (Impl : Implementation).
  
  Module Sem <: Semantics.

    Include Impl.

    Variant step `{Countable Π, Object Π Ω₀, Object Π Ω} (C : meta_configuration Π ω) (π : Π) (l : line Π ω) : meta_configuration Π ω → Prop :=
      Aacker : step C π l (evolve π l C).

    Definition step_tracker `{Countable Π, Object Π Ω₀, Object Π Ω} := step.

  End Sem.

  Include Augmented Sem.

End FullTracker.


Module Adequacy (Impl : Implementation).

  Module Full := FullTracker Impl.
  Module Partial := PartialTracker Impl.

  Include Impl.

  Context `{Countable Π, Object Π Ω₀, Object Π Ω}.

  Variant linearizable_run (r : run (configuration Π Ω ω) Π ω) σ f : Prop :=
    linearizable_intro atomic :
      Atomic.Run impl.(initial_state) atomic →
        behavior r = behavior atomic →
          final atomic = (σ, f) →
            linearizable_run r σ f.

  Definition tracker_sound (r : run (configuration Π Ω ω) Π ω) :=
    ∀ σ f, (final r).(tracker) σ f → linearizable_run r σ f.

  Lemma sound_linearizations r atomic σ σ' πs f f' :
    Full.Run r →
      Atomic.Run impl.(initial_state) atomic →
        behavior atomic = behavior r →
          (final r).(tracker) σ f →
            final atomic = (σ, f) →
              δ_multi σ f πs σ' f' →
                ∃ atomic',
                  Atomic.Run impl.(initial_state) atomic' ∧
                    behavior atomic' = behavior r ∧
                      final atomic' = (σ', f').
  Proof.
    revert σ' f'. induction πs.
    - intros. exists atomic. split.
      + assumption.
      + now inv H7.
    - intros. inv H7. pose proof IHπs σ'0 f'0 as IH. eapply IH in H2; eauto.
      destruct H2 as (atomic' & Hatomic & Hbehavior & Hfinal).
      eexists (Step atomic' t Intermediate _).
      split.
      + econstructor; eauto. rewrite Hfinal. econstructor; eauto.
      + now split.
  Qed.

  Lemma sound_invoke r π op arg c :
    Full.Run (Step r π (Invoke op arg) c) → tracker_sound r → tracker_sound (Step r π (Invoke op arg) c).
  Proof.
    intros HRunStep IH. inv HRunStep. inv H7. inv H3.  unfold tracker_sound. simpl. intros.
    rewrite <- H6 in H3. inv H3. generalize dependent f. generalize dependent σ. induction πs.
    - intros. unfold tracker_sound in *. inv H13.
      apply IH in H8. inv H8.
      eapply linearizable_intro with (atomic := Step atomic π (Invoke op arg) _).
      + econstructor.
        * assumption.
        * rewrite H7. now econstructor. 
      + simpl. now rewrite H5. 
      + reflexivity.
    - intros. inv H13. unfold tracker_sound in *. simpl in *.
      apply IH in H8. inv H8. eapply IHπs in H7. inv H7.
      eapply linearizable_intro with (atomic := Step atomic0 t Intermediate _).
      + econstructor.
        * assumption.
        * rewrite H13. simpl in *. econstructor; eauto.
      + assumption.
      + easy.
  Qed.

  Lemma step_intermediate_idempotent :


  Lemma sound_intermediate r π c :
    Full.Run (Step r π Intermediate c) → tracker_sound r → tracker_sound (Step r π Intermediate c).
  Proof.


  Lemma sound_intermediate r π c :
    Full.Run (Step r π Intermediate c) → tracker_sound r → tracker_sound (Step r π Intermediate c).
  Proof.
    intros HRunStep IH. inv HRunStep. inv H7. unfold tracker_sound. simpl. intros. inv H3.
    rewrite <- H7 in H5. inv H5. generalize dependent f0. generalize dependent σ. induction πs.
    - intros. unfold tracker_sound in *. simpl in *. inv H6.
      apply IH in H3. inv H3. 
      now apply linearizable_intro with (atomic := atomic).
    - intros. inv H6. unfold tracker_sound in *.
      apply IH in H3 as ?. inv H5. eapply IHπs in H3.
      + admit.
      + 
      inv H3.
      eapply linearizable_intro with (atomic := Step atomic0 t Intermediate _).
      + econstructor.
        * assumption.
        * rewrite H13. simpl in *. econstructor; eauto.
      + assumption.
      + easy.
  Qed.

  Lemma sound_response r π v c :
    Implementation.Run impl (Step r π (Response v) c) → tracker_sound r → tracker_sound (Step r π (Response v) c).
  Proof.
    intros HRunStep IH. inv HRunStep. inv H7. unfold tracker_sound. simpl. intros. inv H3.
    generalize dependent f0. generalize dependent σ. induction πs.
    - intros. unfold tracker_sound in *. rewrite <- H2 in IH. simpl in *. inv H9.
      apply IH in H7. inv H7.
      eapply linearizable_intro with (atomic := Step atomic π (Response v) _).
      + econstructor.
        * assumption.
        * rewrite H10. now econstructor. 
      + simpl. now rewrite H9. 
      + reflexivity.
    - intros. inv H9. unfold tracker_sound in *. rewrite <- H2 in IH. simpl in *.
      apply IH in H7. inv H5. eapply IHπs in H11. inv H11.
      eapply linearizable_intro with (atomic := Step atomic t Intermediate _).
      + econstructor.
        * assumption.
        * rewrite H10. simpl in *. econstructor; eauto.
      + assumption.
      + easy.
  Qed.

  (* Lemma sound r σ f :
    FullTracker.Run impl r →
      (final r).(tracker) σ f →
        ∃ atomic,
          Atomic.Run impl.(initial_state) atomic ∧ behavior atomic = behavior r ∧ final atomic = (σ, f).
  Proof.
    revert σ f. induction r.
    - simpl. intros σ f Hrun Htracker. eexists (Initial _). split.
      + econstructor.
      + split.
        * reflexivity.
        * inv Hrun. simpl in *. now inv Htracker. 
    - intros. simpl in *. inversion H2. subst.
      inv H9. inv H5. pose proof H3 as Htracker. rewrite <- H8 in H3. inv H3.
      + eapply IHr in H6 as (atomic & Hatomic & Hbehavior & Hfinal); eauto.
        eapply sound_linearizations with (atomic := Step atomic π (Invoke op arg) _) in H2.
        * shelve.
        * econstructor; eauto. rewrite Hfinal. now econstructor.
        * simpl. now rewrite Hbehavior.
        * simpl. rewrite <- H8. econstructor.
          -- eassumption.
          -- assumption.
          -- econstructor.
        * reflexivity.
        * eassumption.
        Unshelve. simpl in *.
        inv H2 as (atomic' & ? & ? & ?). exists atomic'. split.
        -- assumption.
        -- now split.
      + eapply IHr in H6 as (atomic & Hatomic & Hbehavior & Hfinal).
        eapply sound_linearizations with (atomic := Step atomic π (Invoke op arg) _) in H2.
        * shelve.
        * econstructor; eauto. rewrite Hfinal. now econstructor.
        * simpl. now rewrite Hbehavior.
        * simpl. rewrite <- H8. econstructor.
          -- eassumption.
          -- assumption.
          -- econstructor.
        * reflexivity.
        * eassumption.
        Unshelve. simpl in *.
        inv H2 as (atomic' & ? & ? & ?). exists atomic'. split.
        -- assumption.
        -- now split.
        


      apply sound_invoke; auto.
      + apply sound_intermediate; auto.
      + apply sound_response; auto.
  Qed. *)

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
          Implementation.Run impl (Step r π (Invoke op arg) c) →
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
          exists ⟨⟩.
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
          Implementation.Run impl (Step r π (Response v) c) →
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
          exists ⟨⟩.
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
    Implementation.Run impl (Initial c) → Atomic.Run impl.(initial_state) atomic → behavior (Initial c) = behavior atomic → atomic = Initial (impl.(initial_state), λ _, Idle).
  Proof.
    simpl. intros Hrun. inv Hrun. induction atomic.
    - intros. inv H2. reflexivity.
    - intros. inv H2. destruct l; simpl in *.
      + discriminate.
      + apply IHatomic in H6; auto. inv H9. simpl in *. inv H2.
      + discriminate.
  Qed.

  Lemma complete r atomic σ f : Implementation.Run impl r → Atomic.Run impl.(initial_state) atomic → behavior r = behavior atomic → final atomic = (σ, f) → (final r).(tracker) σ f.
  Proof.
    revert atomic σ f.
    induction r.
    - simpl. intros. eapply linearization_empty in H2 as ?; eauto. 
      subst. simpl in *. inv H5. inv H2. simpl. econstructor.
    - destruct l.
      + intros. eapply linearization_invoke in H3 as ?; eauto.
        inv H6 as [atomic' [σ' [f' [πs [? [? [? [? ?]]]]]]]].
        simpl in *. inv H2. inv H16. simpl. econstructor.
        * assert (tracker0 = tracker (final r)).
          { rewrite <- H2. reflexivity. }
          erewrite H6; eauto.
        * auto.
        * eauto.
      + simpl in *. intros. inv H2. inv H11. simpl. econstructor.
        * rewrite <- H2 in IHr. simpl in *. eapply IHr; eauto.
        * econstructor.
      + intros. eapply linearization_response in H3 as ?; eauto.
        inv H6 as [atomic' [σ' [f' [πs [? [? [? [? ?]]]]]]]].
        simpl in *. inv H2. inv H16. simpl.
        assert (tracker0 = tracker (final r)).
        { rewrite <- H2. reflexivity. }
        erewrite H6.
        econstructor; eauto.
  Qed.

  (** An implementation is linearizable iff there exists a linearization for each of its runs *)
  Definition linearizable :=
    ∀ r,
      Implementation.Run impl r →
        ∃ atomic, Atomic.Run impl.(initial_state) atomic ∧ behavior r = behavior atomic.

  Lemma soundness : invariant (λ c, ∃ σ f, tracker c σ f) → linearizable.
  Proof.
    unfold linearizable, invariant. intros Hinv r Hrun.
    pose proof Hinv r Hrun as [σ [f Hmeta]].
    pose proof sound r Hrun.
    unfold tracker_sound in *.
    pose proof H2 _ _ Hmeta as [atomic Hatomic Hlinearization Hfinal].
    now exists atomic.
  Qed.

  Lemma completeness : linearizable → invariant (λ c, ∃ σ f, tracker c σ f).
  Proof.
    unfold linearizable, invariant. intros Hlinearizable r Hrun.
    pose proof Hlinearizable r Hrun as [atomic [Hatomic Hbehavior]].
    destruct (final atomic) as [σ f] eqn:Hfinal.
    exists σ. exists f.
    eapply complete; eauto.
  Qed.

  (* An implementation is linearizable iff its tracker being non-empty is an invariant of the algorithm *)
  Theorem adequacy : linearizable ↔ invariant (λ c, ∃ σ f, tracker c σ f).
  Proof.
    split.
    - exact completeness.
    - exact soundness.
  Qed.

  Lemma partial_full_coupled r r' :
    Implementation.Run impl r → PartialTracker.Run impl r' → coupled r r' → (final r').(tracker) ⊆ (final r).(tracker).
  Proof.
    intros HRun HRunPartial Hcoupled. induction Hcoupled.
    - reflexivity.
    - simpl. inv HRun. inv HRunPartial.
      apply IHHcoupled in H4 as IH; auto. clear H4 H5 IHHcoupled.
      inv H7; inv H9; (rewrite <- H2 in IH; rewrite <- H3 in IH; simpl in *); etransitivity; eauto.
      + now apply evolve_inv_monotone.
      + now apply evolve_monotone.
      + now apply evolve_ret_monotone.
  Qed.

End Adequacy.

Section LiftL.

  Context {Π Ω : Type}.

  Context `{Object Π Ω}.

  (* Auxillary objects *)
  Variable Ω' : Type.

  Context `{Object Π Ω'}.

  (* Definition lift_term_l (e : Term.t Π Ω) :  Term.t Π (Ω + Ω').
  Proof.
  Defined. *)

  Fixpoint lift_term_l (e : Term.t Π Ω) : Term.t Π (Ω + Ω') :=
    match e with
    | Var x => Var x
    | Term.Invoke ω op arg => Term.Invoke (inl ω) op (lift_term_l arg)
    | Bop op e₁ e₂ => Bop op (lift_term_l e₁) (lift_term_l e₂)
    | Uop op e => Uop op (lift_term_l e)
    | Term.Pair e₁ e₂ => Term.Pair (lift_term_l e₁) (lift_term_l e₂)
    | ProjL e => ProjL (lift_term_l e)
    | ProjR e => ProjR (lift_term_l e)
    | Term.Int n => Term.Int n
    | Term.Bool b => Term.Bool b
    | Term.Unit => Term.Unit
    end.
  
  Local Open Scope dynamics_scope.

  Lemma lift_term_l_complete :
    ∀ e π ψ (ϵ₁ ϵ₁' : states Π Ω) v (ϵ₂ : states Π Ω'),
      ⟨ π , arg , ψ , ϵ₁ , e ⟩ ⇓ₑ ⟨ ϵ₁' , v ⟩ →
        ⟨ π , arg , ψ , disjoint_union ϵ₁ ϵ₂ , lift_term_l e ⟩ ⇓ₑ ⟨ disjoint_union ϵ₁' ϵ₂ , v ⟩.
  Proof.
    induction e; intros; simpl in *; inv H1; try (econstructor; eauto).
    rewrite insert_union_distr_l. econstructor.
      + eapply IHe. eauto.
      + inv H8. econstructor. unfold Map.lookup in *. simpl in *. assumption.
  Qed.

  Lemma lift_term_l_sound_l :
    ∀ e π ψ ϵ v ϵ',
      ⟨ π , arg , ψ , ϵ , lift_term_l e ⟩ ⇓ₑ ⟨ ϵ' , v ⟩ →
        ⟨ π , arg , ψ , πₗ ϵ , e ⟩ ⇓ₑ ⟨ πₗ ϵ' , v ⟩.
  Proof.
    induction e; intros; simpl in *; inv H1; try (econstructor; eauto).
    rewrite πₗ_insert_comm. econstructor.
    + apply IHe. eassumption.
    + inv H8. constructor. simpl in *.
      replace (Map.lookup ω (πₗ ϵ0)) 
          with (Map.lookup (inl ω) ϵ0) by reflexivity.
      assumption.
  Qed.

  Lemma lift_term_l_sound_r :
    ∀ e π ψ ϵ v ϵ',
      ⟨ π , arg , ψ , ϵ , lift_term_l e ⟩ ⇓ₑ ⟨ ϵ' , v ⟩ → πᵣ ϵ = πᵣ ϵ'.
  Proof.
    induction e; intros; simpl in *; inv H1; intuition.
    - apply IHe in H7. subst. simpl in *.
      replace (πᵣ ϵ0) with (πᵣ ϵ'0). apply insert_l_πᵣ.
    - apply IHe1 in H5. apply IHe2 in H8. congruence.
    - inv H7. eauto.
    - apply IHe1 in H4. apply IHe2 in H7. congruence.
    - apply IHe in H3. assumption.
    - apply IHe in H3. assumption.
  Qed.

  Fixpoint lift_stmt_l (s : Stmt.t Π Ω) : Stmt.t Π (Ω + Ω') :=
    match s with
    | Seq s₁ s₂ => Seq (lift_stmt_l s₁) (lift_stmt_l s₂)
    | Assign x e => Assign x (lift_term_l e)
    | If e s₁ s₂ => If (lift_term_l e) (lift_stmt_l s₁) (lift_stmt_l s₂)
    | Syntax.Stmt.Goto l => Syntax.Stmt.Goto l
    | Syntax.Stmt.Return e => Syntax.Stmt.Return (lift_term_l e)
    | Stmt.Invoke (Invocation ω op arg) => @Syntax.Stmt.Invoke _ (Ω + Ω') _ _ (Invocation (inl ω) op (lift_term_l arg))
    | Skip => Skip
    end.

  Lemma lift_stmt_l_complete :
    ∀ s π ψ ψ' (ϵ₁ ϵ₁' : states Π Ω) sig,
      ⟨ π , arg , ψ , ϵ₁ , s ⟩ ⇓ₛ ⟨ ψ' , ϵ₁' , sig ⟩ →
        ∀ ϵ₂,
          ⟨ π , arg , ψ , disjoint_union ϵ₁ ϵ₂ , lift_stmt_l s ⟩ ⇓ₛ ⟨ ψ' , disjoint_union ϵ₁' ϵ₂ , sig ⟩.
  Proof.
    intros. generalize dependent ϵ₂. induction H1; intros.
    - econstructor.
    - econstructor. fold lift_stmt_l. eauto.
    - econstructor. eauto.
    - econstructor; fold lift_stmt_l; eauto.
    - econstructor; eauto. eapply lift_term_l_complete. auto.
    - eapply eval_if_false.
      + eapply lift_term_l_complete. eauto.
      + fold lift_stmt_l. eapply IHeval.
    - econstructor. eapply lift_term_l_complete. eassumption.
    - econstructor.
    - econstructor. eapply lift_term_l_complete in H1. eauto.
    - econstructor. eapply lift_term_l_complete. eassumption.
  Qed.

  Lemma lift_stmt_l_sound_l :
    ∀ s π ψ ϵ sig ψ' ϵ',
      ⟨ π , arg , ψ , ϵ , lift_stmt_l s ⟩ ⇓ₛ ⟨ ψ' , ϵ' , sig ⟩ →
        ⟨ π , arg , ψ , πₗ ϵ , s ⟩ ⇓ₛ ⟨ ψ' , πₗ ϵ' , sig ⟩.
  Proof.
    induction s; intros.
    - inv H1; econstructor; eauto.
    - inv H1. econstructor. eapply lift_term_l_sound_l. eassumption.
    - inv H1.
      + econstructor.
        * eapply lift_term_l_sound_l. eassumption.
        * eauto.
      + eapply eval_if_false.
        * eapply lift_term_l_sound_l. eassumption.
        * eauto.
    - inv H1. econstructor.
    - inv H1. econstructor. eapply lift_term_l_sound_l. assumption.
    - simpl in *. destruct inv. inv H1. econstructor. eapply lift_term_l_sound_l. simpl. eassumption.
    - inv H1. econstructor.
  Qed.

  Lemma lift_stmt_l_sound_r :
    ∀ s π ψ ϵ sig ψ' ϵ',
      ⟨ π , arg , ψ , ϵ , lift_stmt_l s ⟩ ⇓ₛ ⟨ ψ' , ϵ' , sig ⟩ → πᵣ ϵ = πᵣ ϵ'.
  Proof.
    induction s; intros.
    - inv H1.
      + eauto.
      + eauto.
      + etransitivity.
        * eapply IHs1. eauto.
        * eauto.
    - inv H1. reflexivity.
    - inv H1.
      + etransitivity.
        * eapply lift_term_l_sound_r. eassumption.
        * eauto.
      + etransitivity.
        * eapply lift_term_l_sound_r. eassumption.
        * eauto.
    - inv H1. econstructor.
    - inv H1. eapply lift_term_l_sound_r. eassumption.
    - cbn in *. destruct inv. inv H1. eapply lift_term_l_sound_r.
      assert (Term.Invoke (inl ω) op (lift_term_l arg) = lift_term_l (Term.Invoke ω op arg)) by reflexivity.
      erewrite <- H1.
      eassumption.
    - inv H1. econstructor.
  Qed.

End LiftL.

Section LiftR.

  Context {Π Ω' : Type}.

  Context `{Object Π Ω'}.

  Variable Ω : Type.

  Context `{Object Π Ω}.

  Fixpoint lift_term_r (e : Term.t Π Ω') : Term.t Π (Ω + Ω') :=
    match e with
    | Var x => Var x
    | Term.Invoke ω op arg => @Term.Invoke _ (Ω + Ω') _ _ (inr ω) op (lift_term_r arg)
    | Bop op e₁ e₂ => Bop op (lift_term_r e₁) (lift_term_r e₂)
    | Uop op e => Uop op (lift_term_r e)
    | Term.Pair e₁ e₂ => Term.Pair (lift_term_r e₁) (lift_term_r e₂)
    | ProjL e => ProjL (lift_term_r e)
    | ProjR e => ProjR (lift_term_r e)
    | Term.Int n => Term.Int n
    | Term.Bool b => Term.Bool b
    | Term.Unit => Term.Unit
    end.

  Lemma lift_term_r_complete :
    ∀ e π ψ (ϵ₂ ϵ₂' : states Π Ω') v (ϵ₁ : states Π Ω),
      ⟨ π , arg , ψ , ϵ₂ , e ⟩ ⇓ₑ ⟨ ϵ₂' , v ⟩ →
        ⟨ π , arg , ψ , disjoint_union ϵ₁ ϵ₂ , lift_term_r e ⟩ ⇓ₑ ⟨ disjoint_union ϵ₁ ϵ₂' , v ⟩.
  Proof.
    induction e; intros; simpl in *; inv H1; try (econstructor; eauto).
    rewrite insert_union_distr_r. econstructor.
      + eapply IHe. eauto.
      + inv H8. econstructor. unfold Map.lookup in *. simpl in *. assumption.
  Qed.

  Lemma lift_term_r_sound_r :
    ∀ e π ψ ϵ v ϵ',
      ⟨ π , arg , ψ , ϵ , lift_term_r e ⟩ ⇓ₑ ⟨ ϵ' , v ⟩ →
        ⟨ π , arg , ψ , πᵣ ϵ , e ⟩ ⇓ₑ ⟨ πᵣ ϵ' , v ⟩.
  Proof.
    induction e; intros; simpl in *; inv H1; try (econstructor; eauto).
    rewrite πᵣ_insert_comm. econstructor.
    + apply IHe. eassumption.
    + inv H8. constructor. simpl in *.
      replace (Map.lookup ω (πᵣ ϵ0)) 
          with (Map.lookup (inr ω) ϵ0) by reflexivity.
      assumption.
  Qed.

  Lemma lift_term_r_sound_l :
    ∀ e π ψ ϵ v ϵ',
      ⟨ π , arg , ψ , ϵ , lift_term_r e ⟩ ⇓ₑ ⟨ ϵ' , v ⟩ → πₗ ϵ = πₗ ϵ'.
  Proof.
    induction e; intros; simpl in *; inv H1; intuition.
    - apply IHe in H7. simpl in *.
      replace (πₗ ϵ0) with (πₗ ϵ'0).  apply insert_r_πₗ.
    - etransitivity.
      + eapply IHe1. eassumption.
      + eapply IHe2. eassumption.
    - inv H7. eauto.
    - etransitivity.
      + eapply IHe1. eassumption.
      + eapply IHe2. eassumption.
    - eapply IHe. eassumption.
    - eapply IHe. eassumption.
  Qed.

  Fixpoint lift_stmt_r (s : Stmt.t Π Ω') : Stmt.t Π (Ω + Ω') :=
    match s with
    | Seq s₁ s₂ => Seq (lift_stmt_r s₁) (lift_stmt_r s₂)
    | Assign x e => Assign x (lift_term_r e)
    | If e s₁ s₂ => If (lift_term_r e) (lift_stmt_r s₁) (lift_stmt_r s₂)
    | Syntax.Stmt.Goto l => Syntax.Stmt.Goto l
    | Syntax.Stmt.Return e => Syntax.Stmt.Return (lift_term_r e)
    | Stmt.Invoke (Invocation ω op arg) => @Syntax.Stmt.Invoke _ (Ω + Ω') _ _ (@Invocation _ (Ω + Ω') _ _ (inr ω) op (lift_term_r arg))
    | Skip => Skip
    end.

  Lemma lift_stmt_r_complete :
    ∀ s π ψ ψ' (ϵ₂ ϵ₂' : states Π Ω') sig,
      ⟨ π , arg , ψ , ϵ₂ , s ⟩ ⇓ₛ ⟨ ψ' , ϵ₂' , sig ⟩ →
        ∀ ϵ₁,
          ⟨ π , arg , ψ , disjoint_union ϵ₁ ϵ₂ , lift_stmt_r s ⟩ ⇓ₛ ⟨ ψ' , disjoint_union ϵ₁ ϵ₂' , sig ⟩.
  Proof.
    intros. generalize dependent ϵ₁. induction H1; intros.
    - econstructor.
    - econstructor. fold lift_stmt_r. eauto.
    - econstructor. eauto.
    - econstructor; fold lift_stmt_r; eauto.
    - econstructor; eauto. eapply lift_term_r_complete. auto.
    - eapply eval_if_false.
      + eapply lift_term_r_complete. eauto.
      + fold lift_stmt_r. eapply IHeval.
    - econstructor. eapply lift_term_r_complete. eassumption.
    - econstructor.
    - econstructor. eapply lift_term_r_complete in H1. eauto.
    - econstructor. eapply lift_term_r_complete. eassumption.
  Qed.

  Lemma lift_stmt_r_sound_r :
    ∀ s π ψ ϵ sig ψ' ϵ',
      ⟨ π , arg , ψ , ϵ , lift_stmt_r s ⟩ ⇓ₛ ⟨ ψ' , ϵ' , sig ⟩ →
        ⟨ π , arg , ψ , πᵣ ϵ , s ⟩ ⇓ₛ ⟨ ψ' , πᵣ ϵ' , sig ⟩.
  Proof.
    induction s; intros.
    - inv H1; econstructor; eauto.
    - inv H1. econstructor. eapply lift_term_r_sound_r. eassumption.
    - inv H1.
      + econstructor.
        * eapply lift_term_r_sound_r. eassumption.
        * eauto.
      + eapply eval_if_false.
        * eapply lift_term_r_sound_r. eassumption.
        * eauto.
    - inv H1. econstructor.
    - inv H1. econstructor. eapply lift_term_r_sound_r. assumption.
    - simpl in *. destruct inv. inv H1. econstructor. eapply lift_term_r_sound_r. simpl. eassumption.
    - inv H1. econstructor.
  Qed.

  Lemma lift_stmt_r_sound_l :
    ∀ s π ψ ϵ sig ψ' ϵ',
      ⟨ π , arg , ψ , ϵ , lift_stmt_r s ⟩ ⇓ₛ ⟨ ψ' , ϵ' , sig ⟩ → πₗ ϵ = πₗ ϵ'.
  Proof.
    induction s; intros.
    - inv H1.
      + eauto.
      + eauto.
      + etransitivity.
        * eapply IHs1. eauto.
        * eauto.
    - inv H1. reflexivity.
    - inv H1.
      + etransitivity.
        * eapply lift_term_r_sound_l. eassumption.
        * eauto.
      + etransitivity.
        * eapply lift_term_r_sound_l. eassumption.
        * eauto.
    - inv H1. econstructor.
    - inv H1. eapply lift_term_r_sound_l. eassumption.
    - cbn in *. destruct inv. inv H1. eapply lift_term_r_sound_l.
      assert (@Term.Invoke _ (Ω + Ω') _ _ (inr _) op (lift_term_r arg) = lift_term_r (Term.Invoke ω op arg)) by reflexivity.
      erewrite <- H1.
      eassumption.
    - inv H1. econstructor.
  Qed.

End LiftR.

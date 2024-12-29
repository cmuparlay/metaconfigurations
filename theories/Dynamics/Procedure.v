From Metaconfigurations.Syntax Require Import Value Term Stmt.

From Metaconfigurations Require Import 
  Map Syntax.Term Syntax.Stmt
  Syntax.Value
  Dynamics.Term Object.

From Metaconfigurations.Dynamics Require Import Term Stmt.
From stdpp Require Import base decidable list stringmap gmap fin_maps.

Record procedure (Π Ω : Type) `{Object Π Ω} := {
  param : string;
  body : list (Stmt.t Π Ω);
}.

Arguments param {_ _ _ _}.
Arguments body {_ _ _ _}.

Record frame (Π Ω : Type) `{Object Π Ω} := {
  pc : nat;
  registers : stringmap Value.t;
  proc : procedure Π Ω;
}.

Arguments pc {_ _ _ _}.
Arguments registers {_ _ _ _}.
Arguments proc {_ _ _ _}.

Variant signal (Π Ω : Type) `{Object Π Ω} :=
  | Next (f : frame Π Ω) (* On next step, go to line [l] *)
  | Return (v : Value.t). (* Procedure has returned with value [v] *)

Arguments Next {_ _ _ _}.
Arguments Return {_ _ _ _}.

Record Implementation (Π Ω : Type) {Ω₀} `{Object Π Ω₀, Object Π Ω} (ω : Ω₀) := {
  initial_state : (type ω).(Σ);
  (* Initial states for every base object *)
  initial_states : states Π Ω;
  (* Assignment from every process π and operation OP to a procedure *)
  procedures : (type ω).(OP) → procedure Π Ω;
}.

Arguments initial_state : default implicits.
Arguments initial_states : default implicits.
Arguments procedures : default implicits.

Local Open Scope dynamics_scope.

Variant step_procedure {Π Ω} `{Object Π Ω} (π : Π) : states Π Ω → frame Π Ω → states Π Ω → signal Π Ω → Prop :=
  | step_continue pc s ψ ψ' proc ϵ ϵ' :
    (* If [pc] points to line containing statement [s] in [proc] *)
    proc.(body) !! pc = Some s →
    ⟨ π , ψ , ϵ , s ⟩ ⇓ₛ ⟨ ψ' , ϵ' , Continue ⟩ →
    step_procedure π ϵ {| pc := pc; registers := ψ; proc := proc |} ϵ' (Next {| pc := S pc; registers := ψ'; proc := proc |})
  | step_goto pc pc' s ψ ψ' proc ϵ ϵ' :
    (* If [pc] points to line containing statement [s] in [proc] *)
    proc.(body) !! pc = Some s →
    ⟨ π , ψ , ϵ , s ⟩ ⇓ₛ ⟨ ψ' , ϵ' , Goto pc' ⟩ →
    step_procedure π ϵ {| pc := pc; registers := ψ; proc := proc |} ϵ' (Next {| pc := pc'; registers := ψ'; proc := proc |})
  | step_implicit_return pc ψ proc ϵ :
    (* Control has fallen off end of procedure *)
    proc.(body) !! pc = None →
    step_procedure π ϵ {| pc := pc; registers := ψ; proc := proc |} ϵ (Return ⊤ᵥ)
  | step_return pc s ψ proc ϵ ϵ' v:
    proc.(body) !! pc = Some s →
    ⟨ π , ψ , ϵ , s ⟩ ⇓ₛ ⟨ ψ , ϵ' , Stmt.Return v ⟩ →
    step_procedure π ϵ {| pc := pc; registers := ψ; proc := proc |} ϵ (Return v).

Definition singleton_states `{Object Π Ω} (ω : Ω) (ϵ₀ : (type ω).(Σ)) : states Π (sig (eq ω)).
Proof.
  unfold states, dependent. intros [x P]. subst. simpl. exact ϵ₀.
Qed.

(* Definition atomic_implementation {Π Ω} `{Object Π Ω} (ω : Ω) (ϵ₀ : (type ω).(Σ)) : Implementation Π (sig (eq ω)) ω :=
  {|
    initial_state := ϵ₀;
    initial_states := singleton_states ω ϵ₀;
    procedures op :=
      {|
        param := "arg";
        body :=
          [
            Assign "r" (Term.Invoke (exist (eq ω) ω (eq_refl ω)) op (Var "arg"));
            Syntax.Stmt.Return (Var "r")
          ]
      |}
  |}. *)

Definition atomic_implementation {Π Ω} `{Object Π Ω} (ω : Ω) (ϵ₀ : (type ω).(Σ)) : Implementation Π (sing ω) ω.
Proof.
  split.
  - exact ϵ₀.
  - unfold states, dependent. intros. destruct k. simpl. exact ϵ₀.
  - intros op. split.
    + (* param *) exact "arg".
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

(* A meta configuration relates states of the implemented object and the status of each process *)
Definition meta_configuration Π {Ω} `{Object Π Ω} (ω : Ω) := (type ω).(Σ) → (Π → status Π ω) → Prop.

Inductive snoc_list (A : Type) : Type :=
  | Nil
  | Snoc (h : snoc_list A) (t : A).

Arguments Nil {_}.
Arguments Snoc {_}.

Notation "⟨⟩" := Nil (format "⟨⟩") : list_scope.
Notation "⟨ x ⟩" := (Snoc Nil x) : list_scope.
Notation "⟨ x ; y ; .. ; z ⟩" := (Snoc .. (Snoc (Snoc Nil x) y) .. z) : list_scope.

Infix ",," := Snoc (at level 50, left associativity).

Inductive δ_many {Π Ω} `{EqDecision Π, Object Π Ω} {ω : Ω} : (type ω).(Σ) → (Π → status Π ω) → snoc_list Π → (type ω).(Σ) → (Π → status Π ω) → Prop :=
  | δ_many_refl σ f : δ_many σ f ⟨⟩ σ f
  | δ_many_trans f σ π op arg σ' res πs σ'' f' :
    δ_many σ f πs σ' f' →
    (* if [π] has invoked [op(arg)], but not returned *)
    f' π = Pending op arg →
    (* And (σ', res) ∈ δ(σ, π, op, arg) *)
    (type ω).(δ) σ' π op arg σ'' res →
    δ_many σ f (πs ,, π) σ'' (Map.rebind π (Linearized res) f').

Definition invoke `{EqDecision Π, Object Π Ω} {ω} (f : Π → status Π ω) (π : Π) (op : (type ω).(OP)) (arg : Value.t) : Π → status Π ω :=
  Map.rebind π (Pending op arg) f.

Definition ret `{EqDecision Π, Object Π Ω} {ω} (f : Π → status Π ω) (π : Π) := Map.rebind π Idle f.

Variant evolve_inv `{EqDecision Π, Object Π Ω} {ω} (C : meta_configuration Π ω) (op : (type ω).(OP)) (π : Π) (arg : Value.t) : meta_configuration Π ω :=
  evolve_inv_intro σ f πs σ' f' :
    (* If (σ, f) ∈ C *)
    C σ f →
    f π = Idle →
    (* And atomic configuration (σ', f') results after linearizing every outstanding operation of [πs] *)
    δ_many σ (invoke f π op arg) πs σ' f' →
    (* Then (σ', f') is in the resulting metaconfiguration *)
    evolve_inv C op π arg σ' f'.

Variant evolve `{EqDecision Π, Object Π Ω} {ω} (C : meta_configuration Π ω) : meta_configuration Π ω :=
  evolve_intro σ f πs σ' f' :
    (* If (σ, f) ∈ C *)
    C σ f →
    (* And atomic configuration (σ', f') results after linearizing every outstanding operation of [πs] *)
    δ_many σ f πs σ' f' →
    (* Then (σ', f') is in the resulting metaconfiguration *)
    evolve C σ' f'.

Variant evolve_ret `{EqDecision Π, Object Π Ω} {ω} (C : meta_configuration Π ω) (π : Π) (res : Value.t) : meta_configuration Π ω :=
  evolve_ret_intro σ f πs σ' f' :
    f π = Linearized res →
    (* If (σ, f) ∈ C *)
    C σ f →
    (* And atomic configuration (σ', f') results after linearizing every outstanding operation of [πs] *)
    δ_many σ (ret f π) πs σ' f' →
    (* Then (σ', f') is in the resulting metaconfiguration *)
    evolve_ret C π res σ' f'.

(* Definition atomic_run {Π Ω} `{Countable Π, Object Π Ω} (ϵ : states Π Ω) (ω : Ω) (l : line ω) : list (Π * line) :=
  Run (atomic_implementation ϵ ω). *)

Inductive run (C Π : Type) `{Object Π Ω} (ω : Ω) :=
  | Initial (c : C)
  | Step (r : run C Π ω) (π : Π) (l : line Π ω) (c : C).

Arguments Initial {_ _ _ _ _ _}.
Arguments Step {_ _ _ _ _ _}.

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

Module Atomic.
  Definition configuration (Π : Type) `{Countable Π, Object Π Ω} (ω : Ω) := ((type ω).(Σ) * (Π → status Π ω))%type.

  Definition run (Π : Type) `{Countable Π, Object Π Ω} (ω : Ω) := run (configuration Π ω) Π ω.

  Inductive step `{Countable Π, Object Π Ω} {ω : Ω} : configuration Π ω → Π → line Π ω → configuration Π ω → Prop :=
    | step_invoke σ f π op arg :
      (* If [π] has no outstanding operations*)
      f π = Idle →
      (* Then π can invoke an operation on the shared object *)
      step (σ, f) π (Invoke op arg) (σ, Map.rebind π (Pending op arg) f)
    | step_linearize σ σ' f π op arg res :
      (* If [π] has invoked [op(arg)] but not yet responded *)
      f π = Pending op arg →
      (* And (σ', res) ∈ δ(σ, π, op, arg) *)
      (type ω).(δ) σ π op arg σ' res →
      (* Then [op(arg)] can linearize with value [res] and state [σ'] *)
      step (σ, f) π Intermediate (σ', Map.rebind π (Linearized res) f)
    | step_response σ f π v :
      f π = Linearized v →
      step (σ, f) π (Response v) (σ, Map.rebind π Idle f).

    Definition Run {Π : Type} `{Countable Π, Object Π Ω} {ω : Ω} (σ₀ : (type ω).(Σ)) : run Π ω → Prop := Run (σ₀, λ _, Idle) step.

End Atomic.

  (* | idle_initial c : idle π (Initial c)
  | idle_step_response r c v : idle π (Step r π (Response v) c)
  | idle_step_intermediate r π' c : idle π r → idle π (Step r π' Intermediate c)
  | idle_step_invoke : idle π r → π ≠ π' → idle π () *)

Record configuration Π Ω {Ω₀} `{Countable Π, Object Π Ω, Object Π Ω₀} (ω : Ω₀) := {
  tracker : meta_configuration Π ω;
  outstanding : gmap Π (frame Π Ω);
  ϵ : states Π Ω;
}.

(* Definition outstanding_related `{Countable Π, Object Π Ω} (m : gmap Π (frame Π Ω)) (f : Π → status Π Ω) (π : Π) : Prop.  *)

Arguments tracker : default implicits.
Arguments outstanding : default implicits.
Arguments ϵ : default implicits.

Module Implementation.

  Section Run.

    Context {Π Ω₀ Ω} `{Countable Π, Object Π Ω₀, Object Π Ω} {ω : Ω₀}.

    Variable impl : Implementation Π Ω ω.

    Definition initial_frame op arg :=
      let proc := procedures impl op in
      {|
        pc := 0;
        registers := singletonM proc.(param) arg;
        proc := proc;
      |}.

    Variant step : configuration Π Ω ω → Π → line Π ω → configuration Π Ω ω → Prop :=
      | step_invoke tracker outstanding π ϵ op arg :
        outstanding !! π = None →
        step 
          {| tracker := tracker; outstanding := outstanding; ϵ := ϵ |}
          π
          (Invoke op arg)
          {| tracker := evolve_inv tracker op π arg; outstanding := <[π := initial_frame op arg]>outstanding; ϵ := ϵ |}
      | step_intermediate tracker outstanding π ϵ ϵ' f f' :
        (* If process [π] has an outstanding request for proecedure [proc], interrupted at line [pc] *)
        outstanding !! π = Some f →
        step_procedure π ϵ f ϵ' (Next f') →
        step
          {| tracker := tracker; outstanding := outstanding; ϵ := ϵ |}
          π
          Intermediate
          {| tracker := evolve tracker; outstanding := <[π := f']>outstanding; ϵ := ϵ' |}
      | step_response tracker outstanding π ϵ ϵ' f v :
        (* If process [π] has an outstanding request for procedure [proc], interrupted at line [pc] *)
        outstanding !! π = Some f →
        step_procedure π ϵ f ϵ' (Return v) →
        step
          {| tracker := tracker; outstanding := outstanding; ϵ := ϵ |}
          π
          (Response v)
          {| tracker := evolve_ret tracker π v; outstanding := delete π outstanding; ϵ := ϵ' |}.

    Variant initial_tracker : meta_configuration Π ω :=
      initial_tracker_intro : initial_tracker impl.(initial_state) (λ _, Idle).

    Definition run := run (configuration Π Ω ω) Π ω.

    Definition Run := Run {| tracker := initial_tracker; outstanding := ∅; ϵ := impl.(initial_states) |} step.

    Variant Behavior : snoc_list (Π * line Π ω) → Prop :=
      | Behavior_intro (r : run) : Run r → Behavior (behavior r).

  End Run.

End Implementation.

(* Variant linearization `{Countable Π, Object Π Ω₀, Object Π Ω} {ω : Ω₀} (impl : Implementation Π Ω ω) (r : run Π Ω ω) (atomic : run Π (sing ω) ω) : Prop :=
  linearization_intro : 
    Run impl r → Run (atomic_implementation ω impl.(initial_state)) atomic → behavior r = behavior atomic → linearization impl r atomic. *)

Section Soundness.

  Context `{Countable Π, Object Π Ω₀, Object Π Ω} {ω : Ω₀}.

  Variable impl : Implementation Π Ω ω.

  Variant linearizable (r : run (configuration Π Ω ω) Π ω) σ f : Prop :=
    linearizable_intro atomic :
      Atomic.Run impl.(initial_state) atomic →
        behavior r = behavior atomic →
          final atomic = (σ, f) →
            linearizable r σ f.

  Definition tracker_sound (r : run (configuration Π Ω ω) Π ω) := ∀ σ f, (final r).(tracker) σ f → linearizable r σ f.

  Lemma sound_invoke r π op arg c :
    Implementation.Run impl (Step r π (Invoke op arg) c) → tracker_sound r → tracker_sound (Step r π (Invoke op arg) c).
  Proof.
    intros HRunStep IH. inv HRunStep. inv H7. unfold tracker_sound. simpl. intros. inv H3.
    generalize dependent f. generalize dependent σ. induction πs.
    - intros. unfold tracker_sound in *. rewrite <- H2 in IH. simpl in *. inv H7.
      apply IH in H5. inv H5.
      eapply linearizable_intro with (atomic := Step atomic π (Invoke op arg) _).
      + econstructor.
        * assumption.
        * rewrite H8. now econstructor. 
      + simpl. now rewrite H7. 
      + reflexivity.
    - intros. inv H7. unfold tracker_sound in *. rewrite <- H2 in IH. simpl in *.
      apply IH in H5. inv H5. eapply IHπs in H10. inv H10.
      eapply linearizable_intro with (atomic := Step atomic0 t Intermediate _).
      + econstructor.
        * assumption.
        * rewrite H12. simpl in *. econstructor; eauto.
      + assumption.
      + easy.
  Qed.

  Lemma sound_intermediate r π c :
    Implementation.Run impl (Step r π Intermediate c) → tracker_sound r → tracker_sound (Step r π Intermediate c).
  Proof.
    intros HRunStep IH. inv HRunStep. inv H7. unfold tracker_sound. simpl. intros. inv H6.
    generalize dependent f0. generalize dependent σ. induction πs.
    - intros. unfold tracker_sound in *. rewrite <- H2 in IH. simpl in *. inv H8.
      apply IH in H7. inv H7. 
      now apply linearizable_intro with (atomic := atomic).
    - intros. inv H8. unfold tracker_sound in *. rewrite <- H2 in IH. simpl in *.
      apply IH in H7. inv H7. eapply IHπs in H10. inv H10.
      eapply linearizable_intro with (atomic := Step atomic0 t Intermediate _).
      + econstructor.
        * assumption.
        * rewrite H12. simpl in *. econstructor; eauto.
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

  Lemma sound (r : run (configuration Π Ω ω) Π ω) : Implementation.Run impl r → tracker_sound r.
  Proof.
    induction r.
    - simpl. intros. unfold tracker_sound. intros. econstructor.
      + econstructor.
      + constructor.
      + inv H2. inv H3. reflexivity.
    - simpl. intros. inversion H2. destruct l.
      + apply sound_invoke; auto.
      + apply sound_intermediate; auto.
      + apply sound_response; auto.
  Qed.

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
      ⟨ π , ψ , ϵ₁ , e ⟩ ⇓ₑ ⟨ ϵ₁' , v ⟩ →
        ⟨ π , ψ , disjoint_union ϵ₁ ϵ₂ , lift_term_l e ⟩ ⇓ₑ ⟨ disjoint_union ϵ₁' ϵ₂ , v ⟩.
  Proof.
    induction e; intros; simpl in *; inv H1; try (econstructor; eauto).
    rewrite rebind_union_distr_l. econstructor.
      + eapply IHe. eauto.
      + inv H8. econstructor. unfold Map.lookup in *. simpl in *. assumption.
  Qed.

  Lemma lift_term_l_sound_l :
    ∀ e π ψ ϵ v ϵ',
      ⟨ π , ψ , ϵ , lift_term_l e ⟩ ⇓ₑ ⟨ ϵ' , v ⟩ →
        ⟨ π , ψ , πₗ ϵ , e ⟩ ⇓ₑ ⟨ πₗ ϵ' , v ⟩.
  Proof.
    induction e; intros; simpl in *; inv H1; try (econstructor; eauto).
    rewrite πₗ_rebind_comm. econstructor.
    + apply IHe. eassumption.
    + inv H8. constructor. simpl in *.
      replace (Map.lookup ω (πₗ ϵ0)) 
          with (Map.lookup (inl ω) ϵ0) by reflexivity.
      assumption.
  Qed.

  Lemma lift_term_l_sound_r :
    ∀ e π ψ ϵ v ϵ',
      ⟨ π , ψ , ϵ , lift_term_l e ⟩ ⇓ₑ ⟨ ϵ' , v ⟩ → πᵣ ϵ = πᵣ ϵ'.
  Proof.
    induction e; intros; simpl in *; inv H1; intuition.
    - apply IHe in H7. subst. simpl in *.
      replace (πᵣ ϵ0) with (πᵣ ϵ'0). apply rebind_l_πᵣ.
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
      ⟨ π , ψ , ϵ₁ , s ⟩ ⇓ₛ ⟨ ψ' , ϵ₁' , sig ⟩ →
        ∀ ϵ₂,
          ⟨ π , ψ , disjoint_union ϵ₁ ϵ₂ , lift_stmt_l s ⟩ ⇓ₛ ⟨ ψ' , disjoint_union ϵ₁' ϵ₂ , sig ⟩.
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
      ⟨ π , ψ , ϵ , lift_stmt_l s ⟩ ⇓ₛ ⟨ ψ' , ϵ' , sig ⟩ →
        ⟨ π , ψ , πₗ ϵ , s ⟩ ⇓ₛ ⟨ ψ' , πₗ ϵ' , sig ⟩.
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
      ⟨ π , ψ , ϵ , lift_stmt_l s ⟩ ⇓ₛ ⟨ ψ' , ϵ' , sig ⟩ → πᵣ ϵ = πᵣ ϵ'.
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
      ⟨ π , ψ , ϵ₂ , e ⟩ ⇓ₑ ⟨ ϵ₂' , v ⟩ →
        ⟨ π , ψ , disjoint_union ϵ₁ ϵ₂ , lift_term_r e ⟩ ⇓ₑ ⟨ disjoint_union ϵ₁ ϵ₂' , v ⟩.
  Proof.
    induction e; intros; simpl in *; inv H1; try (econstructor; eauto).
    rewrite rebind_union_distr_r. econstructor.
      + eapply IHe. eauto.
      + inv H8. econstructor. unfold Map.lookup in *. simpl in *. assumption.
  Qed.

  Lemma lift_term_r_sound_r :
    ∀ e π ψ ϵ v ϵ',
      ⟨ π , ψ , ϵ , lift_term_r e ⟩ ⇓ₑ ⟨ ϵ' , v ⟩ →
        ⟨ π , ψ , πᵣ ϵ , e ⟩ ⇓ₑ ⟨ πᵣ ϵ' , v ⟩.
  Proof.
    induction e; intros; simpl in *; inv H1; try (econstructor; eauto).
    rewrite πᵣ_rebind_comm. econstructor.
    + apply IHe. eassumption.
    + inv H8. constructor. simpl in *.
      replace (Map.lookup ω (πᵣ ϵ0)) 
          with (Map.lookup (inr ω) ϵ0) by reflexivity.
      assumption.
  Qed.

  Lemma lift_term_r_sound_l :
    ∀ e π ψ ϵ v ϵ',
      ⟨ π , ψ , ϵ , lift_term_r e ⟩ ⇓ₑ ⟨ ϵ' , v ⟩ → πₗ ϵ = πₗ ϵ'.
  Proof.
    induction e; intros; simpl in *; inv H1; intuition.
    - apply IHe in H7. simpl in *.
      replace (πₗ ϵ0) with (πₗ ϵ'0).  apply rebind_r_πₗ.
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
      ⟨ π , ψ , ϵ₂ , s ⟩ ⇓ₛ ⟨ ψ' , ϵ₂' , sig ⟩ →
        ∀ ϵ₁,
          ⟨ π , ψ , disjoint_union ϵ₁ ϵ₂ , lift_stmt_r s ⟩ ⇓ₛ ⟨ ψ' , disjoint_union ϵ₁ ϵ₂' , sig ⟩.
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
      ⟨ π , ψ , ϵ , lift_stmt_r s ⟩ ⇓ₛ ⟨ ψ' , ϵ' , sig ⟩ →
        ⟨ π , ψ , πᵣ ϵ , s ⟩ ⇓ₛ ⟨ ψ' , πᵣ ϵ' , sig ⟩.
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
      ⟨ π , ψ , ϵ , lift_stmt_r s ⟩ ⇓ₛ ⟨ ψ' , ϵ' , sig ⟩ → πₗ ϵ = πₗ ϵ'.
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

Section Augmentation.

  (* An augmentation specifies, f*)

  Context {Π Ω₀ Ω} `{EqDecision Π, Object Π Ω₀, Object Π Ω} {ω : Ω}.

  Variable impl : Implementation Π Ω ω.

  Variant pending : status → Prop := pending_intro op arg : pending (Pending op arg).

  Definition atomic_configuration := ((type ω).(Σ) * (Π → status))%type.

  (* A meta configuration relates states of the implemented object and the status of each process *)
  Definition meta_configuration := (type ω).(Σ) → (Π → status) → Prop.

  Variant meta_configurations := M.

  Instance meta_config_eq_dec : EqDecision meta_configurations.
  Proof. solve_decision. Defined.

  Definition invoke (f : Π → status) π op arg := Map.rebind π (Pending op arg) f.

  Definition ret (f : Π → status) π := Map.rebind π Idle f.

  Variant evolve_inv (C : meta_configuration) (op : (type ω).(OP)) (π : Π) (arg : Value.t) : meta_configuration :=
    evolve_inv_intro σ f πs σ' f' :
      (* If (σ, f) ∈ C *)
      C σ f →
      (* If every process in permutation [πs] is pending *)
      Forall (λ π, pending (f π)) πs → 
      (* And atomic configuration (σ', f') results after linearizing every outstanding operation of [πs] *)
      δ_many σ (invoke f π op arg) πs σ' f' →
      (* Then (σ', f') is in the resulting metaconfiguration *)
      evolve_inv C op π arg σ' f'.

  Variant evolve (C : meta_configuration) : meta_configuration :=
    evolve_intro σ f πs σ' f' :
      (* If (σ, f) ∈ C *)
      C σ f →
      (* If every process in permutation [πs] is pending *)
      Forall (λ π, pending (f π)) πs → 
      (* And atomic configuration (σ', f') results after linearizing every outstanding operation of [πs] *)
      δ_many σ f πs σ' f' →
      (* Then (σ', f') is in the resulting metaconfiguration *)
      evolve C σ' f'.

  Variant evolve_ret (C : meta_configuration) (π : Π) (res : Value.t) : meta_configuration :=
    evolve_ret_intro σ f πs σ' f' :
      f π = Linearized res →
      (* If (σ, f) ∈ C *)
      C σ f →
      (* If every process in permutation [πs] is pending *)
      Forall (λ π, pending (f π)) πs → 
      (* And atomic configuration (σ', f') results after linearizing every outstanding operation of [πs] *)
      δ_many σ (ret f π) πs σ' f' →
      (* Then (σ', f') is in the resulting metaconfiguration *)
      evolve_ret C π res σ' f'.

  Variant meta_config_operation := EvolveInv (op : (type ω).(OP)) | Evolve | EvolveRet.

  Variant transition_meta_config (C : meta_configuration) (π : Π) : meta_config_operation → Value.t → meta_configuration → Value.t → Prop :=
    | transition_evolve_inv op arg : transition_meta_config C π (EvolveInv op) arg (evolve_inv C op π arg) Value.Unit
    | transition_evolve : transition_meta_config C π Evolve Value.Unit (evolve C) Value.Unit
    | transition_evolve_ret arg : transition_meta_config C π EvolveRet arg (evolve_ret C π arg) Value.Unit.

  Instance object_meta_config : Object Π meta_configurations :=
    λ M, 
      {|
        Σ := (type ω).(Σ) → (Π → status) → Prop;
        OP := meta_config_operation;
        δ := transition_meta_config;
      |}.

End Augmentation.

  (* Auxillary objects *)
  (* Variable Ω' : Type.

  Context `{Object Π Ω'} := zip_with (λ l l', Seq (lift_stmt_l l) (lift_stmt_r l')).

  (* Type of implemented object *)
  Variable Ω₀ : Type.

  (* The object being implemented *)
  Variable ω : Ω₀.

  Context `{Object Π Ω₀}.

  Variable impl : Implementation Π Ω ω.

  
End Augmentation. *)
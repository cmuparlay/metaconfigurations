From Metaconfigurations.Syntax Require Import Value Term Stmt.

From Metaconfigurations Require Import 
  Map Syntax.Term Syntax.Stmt
  Syntax.Value
  Dynamics.Term Object.

From Metaconfigurations.Dynamics Require Import Term Stmt.
From stdpp Require Import base list stringmap gmap fin_maps.

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

Record Implementation (Π Ω : Type) {Ω} `{Object Π Ω₀, Object Π Ω} (ω : Ω₀) := {
  (* Initial states for every base object *)
  initial_states : states Π Ω;
  (* Assignment from every process π and operation OP to a procedure *)
  procedures : (type ω).(OP) → procedure Π Ω;
}.

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

Section Run.

  Context {Π Ω₀ Ω} `{Countable Π, Object Π Ω₀, Object Π Ω} {ω : Ω}.

  Variant status :=
    | Idle
    | Pending (op : (type ω).(OP)) (arg : Value.t)
    | Linearized (res : Value.t).

  (* A meta configuration relates states of the implemented object and the status of each process *)
  Definition meta_configuration := (type ω).(Σ) → (Π → status) → Prop.

  Inductive δ_many : (type ω).(Σ) → (Π → status) → list Π → (type ω).(Σ) → (Π → status) → Prop :=
    | δ_many_refl σ f : δ_many σ f [] σ f
    | δ_many_trans f σ π op arg σ' res πs σ'' f' :
      (* if [π] has invoked [op(arg)], but not returned *)
      f π = Pending op arg →
      (* And (σ', res) ∈ δ(σ, π, op, arg) *)
      (type ω).(δ) σ π op arg σ' res →
      δ_many σ' (Map.rebind π (Linearized res) f) πs σ'' f' →
      δ_many σ f (π :: πs) σ'' f'.

  Definition invoke (f : Π → status) π op arg := Map.rebind π (Pending op arg) f.

  Definition ret (f : Π → status) π res := Map.rebind π (Linearized res) f.

  Variant evolve_inv (C : meta_configuration) (op : (type ω).(OP)) (π : Π) (arg : Value.t) : meta_configuration :=
    evolve_inv_intro σ f πs σ' f' :
      (* If (σ, f) ∈ C *)
      C σ f →
      (* And atomic configuration (σ', f') results after linearizing every outstanding operation of [πs] *)
      δ_many σ (invoke f π op arg) πs σ' f' →
      (* Then (σ', f') is in the resulting metaconfiguration *)
      evolve_inv C op π arg σ' f'.

  Variant evolve (C : meta_configuration) : meta_configuration :=
    evolve_intro σ f πs σ' f' :
      (* If (σ, f) ∈ C *)
      C σ f →
      (* And atomic configuration (σ', f') results after linearizing every outstanding operation of [πs] *)
      δ_many σ f πs σ' f' →
      (* Then (σ', f') is in the resulting metaconfiguration *)
      evolve C σ' f'.

  Variant evolve_ret (C : meta_configuration) (π : Π) (res : Value.t) : meta_configuration :=
    evolve_ret_intro σ f πs σ' f' :
      f π = Linearized res →
      (* If (σ, f) ∈ C *)
      C σ f →
      (* And atomic configuration (σ', f') results after linearizing every outstanding operation of [πs] *)
      δ_many σ (ret f π res) πs σ' f' →
      (* Then (σ', f') is in the resulting metaconfiguration *)
      evolve_ret C π res σ' f'.

  Record configuration := {
    tracker : meta_configuration;
    outstanding : gmap Π (frame Π Ω);
    ϵ : states Π Ω;
  }.

  Variant line :=
    | Invoke (op : (type ω).(OP)) (arg : Value.t)
    | Intermediate
    | Response (resp : Value.t).

  Inductive run :=
    | Initial (c : configuration)
    | Step (r : run) (π : Π) (l : line) (c : configuration).

  Variable impl : Implementation Π Ω ω.

  Definition initial_frame op arg :=
    let proc := procedures impl op in
    {|
      pc := 0;
      registers := singletonM proc.(param) arg;
      proc := proc;
    |}.

  Variant step : configuration → Π → line → configuration → Prop :=
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
    (* If process [π] has an outstanding request for proecedure [proc], interrupted at line [pc] *)
      outstanding !! π = Some f →
      step_procedure π ϵ f ϵ' (Return v) →
      step
        {| tracker := tracker; outstanding := outstanding; ϵ := ϵ |}
        π
        (Response v)
        {| tracker := evolve_ret tracker π v; outstanding := delete π outstanding; ϵ := ϵ' |}.

  Definition final (r : run Π ω) :=
    match r with
    | Initial c | Step _ _ _ c => c
    end.

  Inductive Run : run Π ω → Prop :=
    | Run_initial : Run (Initial {| outstanding := ∅; ϵ := impl.(initial_states) |})
    | Run_step r π l c : Run r → step (final r) π l c → Run (Step r π l c).

  Fixpoint behavior (r : run Π ω) : list (Π * line Π ω) :=
    match r with
    | Initial _ => []
    | Step r π l c =>
        match l with
        | Invoke _ _ | Response _ => (π, l) :: behavior r
        | Intermediate => behavior r
        end
    end.

  Variant Behavior : list (Π * line Π ω) → Prop :=
    | Behavior_intro (r : run Π ω) : Run r → Behavior (behavior r).

  Lemma behavior_no_intermediate π l r : Behavior r → (π, l) ∈ r → l ≠ Intermediate.
  Proof.
  Admitted.

End Run.

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

  Variant status :=
    | Idle
    | Pending (op : (type ω).(OP)) (arg : Value.t)
    | Linearized (res : Value.t).

  Variant pending : status → Prop := pending_intro op arg : pending (Pending op arg).

  Definition atomic_configuration := ((type ω).(Σ) * (Π → status))%type.

  (* A meta configuration relates states of the implemented object and the status of each process *)
  Definition meta_configuration := (type ω).(Σ) → (Π → status) → Prop.

  Variant meta_configurations := M.

  Instance meta_config_eq_dec : EqDecision meta_configurations.
  Proof. solve_decision. Defined.

  Definition invoke (f : Π → status) π op arg := Map.rebind π (Pending op arg) f.

  Definition ret (f : Π → status) π res := Map.rebind π (Linearized res) f.

  Inductive δ_many : (type ω).(Σ) → (Π → status) → list Π → (type ω).(Σ) → (Π → status) → Prop :=
    | δ_many_refl σ f : δ_many σ f [] σ f
    | δ_many_trans f σ π op arg σ' res πs σ'' f' :
      (* if [π] has invoked [op(arg)], but not returned *)
      f π = Pending op arg →
      (* And (σ', res) ∈ δ(σ, π, op, arg) *)
      (type ω).(δ) σ π op arg σ' res →
      δ_many σ' (Map.rebind π (Linearized res) f) πs σ'' f' →
      δ_many σ f (π :: πs) σ'' f'.

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
      δ_many σ (ret f π res) πs σ' f' →
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
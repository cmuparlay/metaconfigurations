From stdpp Require Import base list stringmap gmap fin_maps.
From Metaconfigurations.Syntax Require Import Value Term Stmt.

From Metaconfigurations Require Import 
  Map Syntax.Term Syntax.Stmt
  Syntax.Value
  Dynamics.Term Object.
From stdpp Require Import base.
Require Import Coq.ZArith.BinInt.

From Metaconfigurations.Dynamics Require Import Term Stmt.


Section Procedure.
  Variable Π : Type.

  Context `{Countable Π}.

  (* Type of implemented object *)
  Variable Ω₀ : Type.

  (* The object being implemented *)
  Context {ω : Ω₀}.

  Context `{Object Π Ω₀}.

  (* Set of base objects *)
  Variable Ω : Type.

  (* Context `{EqDecision Ω}. *)

  Context `{Object Π Ω}.

  Record procedure := {
    param : string;
    body : list (Stmt.t Π Ω);
  }.

  Record Implementation := {
    (* Initial states for every base object *)
    initial_states : states Π Ω;
    (* Assignment from every process π and operation OP to a procedure *)
    procedures : (type ω).(OP Π) → procedure;
  }.

  Record frame := {
    pc : nat;
    registers : stringmap Value.t;
    proc : procedure;
  }.

  Variant signal :=
    | Next (f : frame) (* On next step, go to line [l] *)
    | Return (v : Value.t) (* Procedure has returned with value [v] *).

  Variant step_procedure (π : Π) : states Π Ω → frame → states Π Ω → signal → Prop :=
    | step_next pc pc' s ψ ψ' proc ϵ ϵ' :
      (* If [pc] points to line containing statement [s] in [proc] *)
      proc.(body) !! pc = Some s →
      Stmt.eval π ψ ϵ s ψ' ϵ' (Goto pc') →
      step_procedure π ϵ {| pc := pc; registers := ψ; proc := proc |} ϵ' (Next {| pc := pc'; registers := ψ'; proc := proc |})
    | step_implicit_return pc ψ proc ϵ :
      (* Control has fallen off end of procedure *)
      proc.(body) !! pc = None →
      step_procedure π ϵ {| pc := pc; registers := ψ; proc := proc |} ϵ (Return ⊤ᵥ)
    | step_return pc s ψ proc ϵ ϵ' v:
      proc.(body) !! pc = Some s →
      Stmt.eval π ψ ϵ s ψ ϵ' (Stmt.Return v) →
      step_procedure π ϵ {| pc := pc; registers := ψ; proc := proc |} ϵ (Return v).

  Record configuration := {
    outstanding : gmap Π frame;
    ϵ : states Π Ω;
  }.

  Variant line :=
    | Invoke (op : (type ω).(OP Π)) (arg : Value.t)
    | Intermediate
    | Response (resp : Value.t).

  Inductive run :=
    | Initial (c : configuration)
    | Step (r : run) (π : Π) (l : line) (c : configuration).

  Section Run.

    Variable impl : Implementation.

    Definition initial_frame op arg :=
      let proc := procedures impl op in
      {|
        pc := 0;
        registers := singletonM proc.(param) arg;
        proc := proc;
      |}.

    Variant step : configuration → Π → line → configuration → Prop :=
      | step_invoke outstanding π ϵ ϵ' op arg f :
        outstanding !! π = None →
        step_procedure π ϵ (initial_frame op arg) ϵ' (Next f) →
        step {| outstanding := outstanding; ϵ := ϵ |} π (Invoke op arg) {| outstanding := <[π := f]>outstanding; ϵ := ϵ' |}
      | step_intermediate outstanding π ϵ ϵ' f f' :
      (* If process [π] has an outstanding request for proecedure [proc], interrupted at line [pc] *)
        outstanding !! π = Some f →
        step_procedure π ϵ f ϵ' (Next f') →
        step {| outstanding := outstanding; ϵ := ϵ |} π Intermediate {| outstanding := <[π := f']>outstanding; ϵ := ϵ' |}
      | step_response outstanding π ϵ ϵ' f v :
      (* If process [π] has an outstanding request for proecedure [proc], interrupted at line [pc] *)
        outstanding !! π = Some f →
        step_procedure π ϵ f ϵ' (Return v) →
        step {| outstanding := outstanding; ϵ := ϵ |} π (Response v) {| outstanding := delete π outstanding; ϵ := ϵ' |}.

    Definition final r :=
      match r with
      | Initial c | Step _ _ _ c => c
      end.

    Inductive Run : run → Prop :=
      | Run_initial : Run (Initial {| outstanding := ∅; ϵ := impl.(initial_states) |})
      | Run_step r π l c : Run r → step (final r) π l c → Run (Step r π l c).

    Fixpoint behavior r : list (Π * line) :=
      match r with
      | Initial _ => []
      | Step r π l c =>
          match l with
          | Invoke _ _ | Response _ => behavior r ++ [(π, l)]
          | Intermediate => behavior r
          end
      end.

    Variant Behavior : list (Π * line) → Prop :=
      | Behavior_intro (r : run) : Run r → Behavior (behavior r).

    Lemma behavior_no_intermediate π l r : Behavior r → (π, l) ∈ r → l ≠ Intermediate.
    Proof.
    Admitted.

  End Run.

End Procedure.

Section Augmentation.

  Variable Π : Type.

  Context `{Countable Π}.

  (* Type of implemented object *)
  Variable Ω₀ : Type.

  (* The object being implemented *)
  Variable ω : Ω₀.

  Context `{Object Π Ω₀}.

  (* Set of base objects *)
  Variable Ω : Type.

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

  Lemma lift_term_l_complete :
    ∀ e π ψ (ϵ₁ ϵ₁' : states Π Ω) v (ϵ₂ : states Π Ω'),
      Term.eval π ψ ϵ₁ e ϵ₁' v →
        Term.eval π ψ (disjoint_union ϵ₁ ϵ₂) (lift_term_l e) (disjoint_union ϵ₁' ϵ₂) v.
  Proof.
    induction e; intros; simpl in *; inv H3; try (econstructor; eauto).
    rewrite rebind_union_distr_l. econstructor.
      + eapply IHe. eauto.
      + inv H10. econstructor. unfold Map.lookup in *. simpl in *. assumption.
  Qed.

  Lemma lift_term_l_sound_l :
    ∀ e π ψ ϵ v ϵ',
      Term.eval π ψ ϵ (lift_term_l e) ϵ' v →
        Term.eval π ψ (πₗ ϵ) e (πₗ ϵ') v.
  Proof.
    induction e; intros; simpl in *; inv H3; try (econstructor; eauto).
    rewrite πₗ_rebind_comm. econstructor.
    + apply IHe. eassumption.
    + inv H10. constructor. simpl in *.
      replace (Map.lookup ω0 (πₗ ϵ0)) 
          with (Map.lookup (inl ω0) ϵ0) by reflexivity.
      assumption.
  Qed.

  Lemma lift_term_l_sound_r :
    ∀ e π ψ ϵ v ϵ',
      Term.eval π ψ ϵ (lift_term_l e) ϵ' v → πᵣ ϵ = πᵣ ϵ'.
  Proof.
    induction e; intros; simpl in *; inv H3; intuition.
    - apply IHe in H9. subst. simpl in *.
      replace (πᵣ ϵ0) with (πᵣ ϵ'0). apply rebind_l_πᵣ.
    - apply IHe1 in H7. apply IHe2 in H10. congruence.
    - inv H9. eauto.
    - apply IHe1 in H6. apply IHe2 in H9. congruence.
    - apply IHe in H5. assumption.
    - apply IHe in H5. assumption.
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
      Stmt.eval π ψ ϵ₁ s ψ' ϵ₁' sig →
        ∀ ϵ₂,
          Stmt.eval π ψ (disjoint_union ϵ₁ ϵ₂) (lift_stmt_l s) ψ' (disjoint_union ϵ₁' ϵ₂) sig.
  Proof.
    intros. generalize dependent ϵ₂. induction H3; intros.
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
    - econstructor. eapply lift_term_l_complete in H3. eauto.
    - econstructor. eapply lift_term_l_complete. eassumption.
  Qed.

  Lemma lift_stmt_l_sound_l :
    ∀ s π ψ ϵ sig ψ' ϵ',
      Stmt.eval π ψ ϵ (lift_stmt_l s) ψ' ϵ' sig →
        Stmt.eval π ψ (πₗ ϵ) s ψ' (πₗ ϵ') sig.
  Proof.
    induction s; intros.
    - inv H3; econstructor; eauto.
    - inv H3. econstructor. eapply lift_term_l_sound_l. eassumption.
    - inv H3.
      + econstructor.
        * eapply lift_term_l_sound_l. eassumption.
        * eauto.
      + eapply eval_if_false.
        * eapply lift_term_l_sound_l. eassumption.
        * eauto.
    - inv H3. econstructor.
    - inv H3. econstructor. eapply lift_term_l_sound_l. assumption.
    - simpl in *. destruct inv. inv H3. econstructor. eapply lift_term_l_sound_l. simpl. eassumption.
    - inv H3. econstructor.
  Qed.

  Lemma lift_stmt_l_sound_r :
    ∀ s π ψ ϵ sig ψ' ϵ',
      Stmt.eval π ψ ϵ (lift_stmt_l s) ψ' ϵ' sig → πᵣ ϵ = πᵣ ϵ'.
  Proof.
    induction s; intros.
    - inv H3.
      + eauto.
      + eauto.
      + etransitivity.
        * eapply IHs1. eauto.
        * eauto.
    - inv H3. reflexivity.
    - inv H3.
      + etransitivity.
        * eapply lift_term_l_sound_r. eassumption.
        * eauto.
      + etransitivity.
        * eapply lift_term_l_sound_r. eassumption.
        * eauto.
    - inv H3. econstructor.
    - inv H3. eapply lift_term_l_sound_r. eassumption.
    - cbn in *. destruct inv. inv H3. eapply lift_term_l_sound_r.
      assert (Term.Invoke (inl ω0) op (lift_term_l arg) = lift_term_l (Term.Invoke ω0 op arg)) by reflexivity.
      erewrite <- H3.
      eassumption.
    - inv H3. econstructor.
  Qed.

  (* Definition lift_term_r (e : Term.t Π Ω) :  Term.t Π (Ω + Ω').
  Proof.
  Defined. *)

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
      Term.eval π ψ ϵ₂ e ϵ₂' v →
        Term.eval π ψ (disjoint_union ϵ₁ ϵ₂) (lift_term_r e) (disjoint_union ϵ₁ ϵ₂') v.
  Proof.
    induction e; intros; simpl in *; inv H3; try (econstructor; eauto).
    rewrite rebind_union_distr_r. econstructor.
      + eapply IHe. eauto.
      + inv H10. econstructor. unfold Map.lookup in *. simpl in *. assumption.
  Qed.

  Lemma lift_term_r_sound_r :
    ∀ e π ψ ϵ v ϵ',
      Term.eval π ψ ϵ (lift_term_r e) ϵ' v →
        Term.eval π ψ (πᵣ ϵ) e (πᵣ ϵ') v.
  Proof.
    induction e; intros; simpl in *; inv H3; try (econstructor; eauto).
    rewrite πᵣ_rebind_comm. econstructor.
    + apply IHe. eassumption.
    + inv H10. constructor. simpl in *.
      replace (Map.lookup ω0 (πᵣ ϵ0)) 
          with (Map.lookup (inr ω0) ϵ0) by reflexivity.
      assumption.
  Qed.

  Lemma lift_term_r_sound_l :
    ∀ e π ψ ϵ v ϵ',
      Term.eval π ψ ϵ (lift_term_r e) ϵ' v → πₗ ϵ = πₗ ϵ'.
  Proof.
    induction e; intros; simpl in *; inv H3; intuition.
    - apply IHe in H9. subst. simpl in *.
      replace (πₗ ϵ0) with (πₗ ϵ'0).
      + apply rebind_r_πₗ.
    - apply IHe1 in H7. apply IHe2 in H10. congruence.
    - inv H9. eauto.
    - apply IHe1 in H6. apply IHe2 in H9. congruence.
    - apply IHe in H5. assumption.
    - apply IHe in H5. assumption.
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
      Stmt.eval π ψ ϵ₂ s ψ' ϵ₂' sig →
        ∀ ϵ₁,
          Stmt.eval π ψ (disjoint_union ϵ₁ ϵ₂) (lift_stmt_r s) ψ' (disjoint_union ϵ₁ ϵ₂') sig.
  Proof.
    intros. generalize dependent ϵ₁. induction H3; intros.
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
    - econstructor. eapply lift_term_r_complete in H3. eauto.
    - econstructor. eapply lift_term_r_complete. eassumption.
  Qed.

  Lemma lift_stmt_r_sound_r :
    ∀ s π ψ ϵ sig ψ' ϵ',
      Stmt.eval π ψ ϵ (lift_stmt_r s) ψ' ϵ' sig →
        Stmt.eval π ψ (πᵣ ϵ) s ψ' (πᵣ ϵ') sig.
  Proof.
    induction s; intros.
    - inv H3; econstructor; eauto.
    - inv H3. econstructor. eapply lift_term_r_sound_r. eassumption.
    - inv H3.
      + econstructor.
        * eapply lift_term_r_sound_r. eassumption.
        * eauto.
      + eapply eval_if_false.
        * eapply lift_term_r_sound_r. eassumption.
        * eauto.
    - inv H3. econstructor.
    - inv H3. econstructor. eapply lift_term_r_sound_r. assumption.
    - simpl in *. destruct inv. inv H3. econstructor. eapply lift_term_r_sound_r. simpl. eassumption.
    - inv H3. econstructor.
  Qed.

  Lemma lift_stmt_r_sound_l :
    ∀ s π ψ ϵ sig ψ' ϵ',
      Stmt.eval π ψ ϵ (lift_stmt_r s) ψ' ϵ' sig → πₗ ϵ = πₗ ϵ'.
  Proof.
    induction s; intros.
    - inv H3.
      + eauto.
      + eauto.
      + etransitivity.
        * eapply IHs1. eauto.
        * eauto.
    - inv H3. reflexivity.
    - inv H3.
      + etransitivity.
        * eapply lift_term_r_sound_l. eassumption.
        * eauto.
      + etransitivity.
        * eapply lift_term_r_sound_l. eassumption.
        * eauto.
    - inv H3. econstructor.
    - inv H3. eapply lift_term_r_sound_l. eassumption.
    - cbn in *. destruct inv. inv H3. eapply lift_term_r_sound_l.
      assert (@Term.Invoke _ (Ω + Ω') _ _ (inr ω0) op (lift_term_r arg) = lift_term_r (Term.Invoke ω0 op arg)) by reflexivity.
      erewrite <- H3.
      eassumption.
    - inv H3. econstructor.
  Qed.

  Definition augment := zip_with (λ l l', Seq (lift_stmt_l l) (lift_stmt_r l')).

  Lemma behavior_augmentation r 
  
End Augmentation.
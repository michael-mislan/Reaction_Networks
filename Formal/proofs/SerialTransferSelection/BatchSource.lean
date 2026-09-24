import proofs.SerialTransferSelection.BatchDomain
import proofs.ResourceLimitedCompetition.StoppedPopulation

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

/-- Same physical event outcomes and rates; C3 stops at energy 8a and resource W0. -/
noncomputable def phaseEventReason (N W0 : ℕ) (zL zH : ℝ) {D : Finset PopulationState}
    (e : PopulationEvent D) : StopReason := by
  classical
  let s := e.1.val
  let c := selectedCell s e.2.1
  exact match e.2.2 with
  | .inl r =>
      if 8*innerEnergy ≤ cellEnergy zL zH ⟨c.high,nextCompartment c.compartment (.inl r)⟩
      then .outer else .active
  | .inr d =>
      let p := nextCompartment c.compartment (.inr ())
      if 8*innerEnergy ≤ cellEnergy zL zH ⟨c.high,p⟩ then .outer
      else if p.2=2*N then
        if 2*innerEnergy < cellEnergy zL zH ⟨c.high,p⟩ then .divisionEnergy
        else if ¬(cellEnergy zL zH ⟨c.high,(d.val,N)⟩ < 4*innerEnergy ∧
          cellEnergy zL zH ⟨c.high,((fun i => p.1 i-d.val i),N)⟩ < 4*innerEnergy)
          then .partition
        else if s.resource-1=W0 then .nutrient else .active
      else if s.resource-1=W0 then .nutrient else .active

/-- Terminal states retain the physical outcome via their event record. -/
noncomputable def phaseStoppedNext (N W0 : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (x : StoppedPopulation D) (e : PopulationEvent D) : StoppedPopulation D := by
  classical
  exact match x with
  | .inr _ => x
  | .inl s => if e.1=s then
      if phaseEventReason N W0 zL zH e=.active then
        if h : eventOutcome N e ∈ D then .inl ⟨eventOutcome N e,h⟩ else .inr e
      else .inr e
    else x

noncomputable def phaseStoppedModel (γ : ℝ) (hγ : 0 ≤ γ)
    (Ω N W0 : ℕ) (zL zH : ℝ) (D : Finset PopulationState) :
    FiniteJumpModel (StoppedPopulation D) (PopulationEvent D) := by
  classical
  exact {
    next := phaseStoppedNext N W0 zL zH D
    rate := fun x e => match x with
      | .inr _ => 0
      | .inl s => if e.1=s then eventRate γ Ω e else 0
    nonneg := by
      intro x e
      cases x with
      | inr e => exact le_rfl
      | inl s =>
        dsimp only
        split_ifs
        · exact event_rate_nonneg γ hγ Ω e
        · exact le_rfl }

theorem phase_terminal_generator (γ : ℝ) (hγ : 0 ≤ γ)
    (Ω N W0 : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (f : StoppedPopulation D → ℝ) (e : PopulationEvent D) :
    (phaseStoppedModel γ hγ Ω N W0 zL zH D).generator f (.inr e)=0 := by
  classical
  simp [FiniteJumpModel.generator,phaseStoppedModel]

theorem phase_active_generator (γ : ℝ) (hγ : 0 ≤ γ)
    (Ω N W0 : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (f : StoppedPopulation D → ℝ) (s : ActiveState D) :
    (phaseStoppedModel γ hγ Ω N W0 zL zH D).generator f (.inl s) =
      ∑ e : CellEvent s.val, eventRate γ Ω ⟨s,e⟩ *
        (f (phaseStoppedNext N W0 zL zH D (.inl s) ⟨s,e⟩)-f (.inl s)) := by
  classical
  unfold FiniteJumpModel.generator
  rw [Fintype.sum_sigma,Finset.sum_eq_single s]
  · simp [phaseStoppedModel]
  · intro b _ hbs
    simp [phaseStoppedModel,hbs]
  · simp

theorem phase_active_generator_le (γ : ℝ) (hγ : 0 ≤ γ)
    (Ω N W0 : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (f : StoppedPopulation D → ℝ) (s : ActiveState D)
    (v : CellEvent s.val → ℝ)
    (hnext : ∀ e, f (phaseStoppedNext N W0 zL zH D (.inl s) ⟨s,e⟩) ≤ v e) :
    (phaseStoppedModel γ hγ Ω N W0 zL zH D).generator f (.inl s) ≤
      ∑ e : CellEvent s.val, eventRate γ Ω ⟨s,e⟩*(v e-f (.inl s)) := by
  rw [phase_active_generator]
  exact Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left
    (sub_le_sub_right (hnext e) _) (event_rate_nonneg γ hγ Ω ⟨s,e⟩))


/-- Every chosen transition retains the actual compound physical outcome,
including a division simultaneous with the nutrient endpoint or a failure. -/
theorem phase_physical_next_chosen (N W0 : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (e : PopulationEvent D) :
    physicalState N (phaseStoppedNext N W0 zL zH D (.inl e.1) e)=eventOutcome N e := by
  classical
  unfold phaseStoppedNext
  dsimp only
  rw [if_pos rfl]
  split_ifs <;> rfl

end SerialTransferSelection

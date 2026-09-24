import proofs.ResourceLimitedCompetition.FinitePopulation

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy

abbrev ActiveState (D : Finset PopulationState) := {s : PopulationState // s ∈ D}

def selectedCell (s : PopulationState) (i : Fin s.live.length) : TaggedCell := s.live[i]

abbrev CellEvent (s : PopulationState) : Type :=
  Σ i : Fin s.live.length, Fin 13 ⊕
    {d : Counts // d ∈ daughterDraws (nextCompartment (selectedCell s i).compartment (.inr ())).1}

abbrev PopulationEvent (D : Finset PopulationState) := Σ s : ActiveState D, CellEvent s.val
abbrev StoppedPopulation (D : Finset PopulationState) := ActiveState D ⊕ PopulationEvent D

def eventOutcome (N : ℕ) {D : Finset PopulationState} (e : PopulationEvent D) : PopulationState :=
  let s := e.1.val
  let i := e.2.1
  let c := selectedCell s i
  let a := s.live.take i.val
  let b := s.live.drop (i.val+1)
  match e.2.2 with
  | .inl r => residentAt s.resource s.divisions a c b r
  | .inr d => growthAt N s.resource s.divisions a c b d.val

noncomputable def eventRate (γ : ℝ) (Ω : ℕ) {D : Finset PopulationState}
    (e : PopulationEvent D) : ℝ :=
  let s := e.1.val
  let c := selectedCell s e.2.1
  match e.2.2 with
  | .inl r => propensity (resourceCoefficient γ s.resource Ω) c.compartment (.inl r)
  | .inr d => propensity (resourceCoefficient γ s.resource Ω) c.compartment (.inr ()) *
      daughterWeight (nextCompartment c.compartment (.inr ())).1 d.val

theorem event_rate_nonneg (γ : ℝ) (hγ : 0 ≤ γ) (Ω : ℕ) {D : Finset PopulationState}
    (e : PopulationEvent D) : 0 ≤ eventRate γ Ω e := by
  have hb : 0 ≤ resourceCoefficient γ e.1.val.resource Ω := by
    unfold resourceCoefficient
    positivity
  unfold eventRate
  dsimp only
  split
  · exact propensity_nonneg _ hb _ _
  · exact mul_nonneg (propensity_nonneg _ hb _ _) (daughterWeight_nonneg _ _)

inductive StopReason where
  | active | outer | divisionEnergy | partition | nutrient
  deriving DecidableEq

/-- All flags are determined by count states and the actual compound transition. -/
noncomputable def eventReason (N M : ℕ) (zL zH : ℝ) {D : Finset PopulationState}
    (e : PopulationEvent D) : StopReason := by
  classical
  let s := e.1.val
  let c := selectedCell s e.2.1
  exact match e.2.2 with
  | .inl r =>
      if outerEnergy ≤ cellEnergy zL zH ⟨c.high,nextCompartment c.compartment (.inl r)⟩
      then .outer else .active
  | .inr d =>
      let p := nextCompartment c.compartment (.inr ())
      if outerEnergy ≤ cellEnergy zL zH ⟨c.high,p⟩ then .outer
      else if p.2=2*N then
        if 2*innerEnergy < cellEnergy zL zH ⟨c.high,p⟩ then .divisionEnergy
        else if ¬(cellEnergy zL zH ⟨c.high,(d.val,N)⟩ < 4*innerEnergy ∧
          cellEnergy zL zH ⟨c.high,((fun i => p.1 i-d.val i),N)⟩ < 4*innerEnergy)
          then .partition
        else if s.resource-1=N*M then .nutrient else .active
      else if s.resource-1=N*M then .nutrient else .active

/-- Terminal states retain the physical outcome via their event record. -/
noncomputable def stoppedNext (N M : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (x : StoppedPopulation D) (e : PopulationEvent D) : StoppedPopulation D := by
  classical
  exact match x with
  | .inr _ => x
  | .inl s => if e.1=s then
      if eventReason N M zL zH e=.active then
        if h : eventOutcome N e ∈ D then .inl ⟨eventOutcome N e,h⟩ else .inr e
      else .inr e
    else x

noncomputable def stoppedPopulationModel (γ : ℝ) (hγ : 0 ≤ γ)
    (Ω N M : ℕ) (zL zH : ℝ) (D : Finset PopulationState) :
    FiniteJumpModel (StoppedPopulation D) (PopulationEvent D) := by
  classical
  exact {
    next := stoppedNext N M zL zH D
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

def physicalState (N : ℕ) {D : Finset PopulationState} : StoppedPopulation D → PopulationState
  | .inl s => s.val
  | .inr e => eventOutcome N e

theorem terminal_generator (γ : ℝ) (hγ : 0 ≤ γ)
    (Ω N M : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (f : StoppedPopulation D → ℝ) (e : PopulationEvent D) :
    (stoppedPopulationModel γ hγ Ω N M zL zH D).generator f (.inr e)=0 := by
  classical
  simp [FiniteJumpModel.generator,stoppedPopulationModel]

theorem active_generator (γ : ℝ) (hγ : 0 ≤ γ)
    (Ω N M : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (f : StoppedPopulation D → ℝ) (s : ActiveState D) :
    (stoppedPopulationModel γ hγ Ω N M zL zH D).generator f (.inl s) =
      ∑ e : CellEvent s.val, eventRate γ Ω ⟨s,e⟩ *
        (f (stoppedNext N M zL zH D (.inl s) ⟨s,e⟩)-f (.inl s)) := by
  classical
  unfold FiniteJumpModel.generator
  rw [Fintype.sum_sigma,Finset.sum_eq_single s]
  · simp [stoppedPopulationModel]
  · intro b _ hbs
    simp [stoppedPopulationModel,hbs]
  · simp

theorem active_generator_le (γ : ℝ) (hγ : 0 ≤ γ)
    (Ω N M : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (f : StoppedPopulation D → ℝ) (s : ActiveState D)
    (v : CellEvent s.val → ℝ)
    (hnext : ∀ e, f (stoppedNext N M zL zH D (.inl s) ⟨s,e⟩) ≤ v e) :
    (stoppedPopulationModel γ hγ Ω N M zL zH D).generator f (.inl s) ≤
      ∑ e : CellEvent s.val, eventRate γ Ω ⟨s,e⟩*(v e-f (.inl s)) := by
  rw [active_generator]
  exact Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left
    (sub_le_sub_right (hnext e) _) (event_rate_nonneg γ hγ Ω ⟨s,e⟩))

end ResourceLimitedCompetition

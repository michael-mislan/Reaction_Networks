import proofs.ProductiveMemory.ExtractionCompartment
import proofs.ResourceLimitedCompetition.PopulationTransitions

namespace ProductiveMemory
open FiniteCopy HeritableCompositions ResourceLimitedCompetition
noncomputable section
set_option Elab.async false

structure ProductiveState where
  population : PopulationState
  collected : ℕ

abbrev ProductiveEvent (s : ProductiveState) := CellEvent s.population ⊕ Fin s.population.live.length

def extractionAt (Q D : ℕ) (a : List TaggedCell) (c : TaggedCell) (b : List TaggedCell) : PopulationState :=
  ⟨Q,a++⟨c.high,(channelNext c.compartment.1 (.inr ()),c.compartment.2)⟩::b,D⟩

def productiveOutcome (N : ℕ) (s : ProductiveState) : ProductiveEvent s → ProductiveState
  | .inl e =>
    let c := selectedCell s.population e.1
    let a := s.population.live.take e.1.val
    let b := s.population.live.drop (e.1.val+1)
    match e.2 with
    | .inl r => ⟨residentAt s.population.resource s.population.divisions a c b r,s.collected⟩
    | .inr d => ⟨growthAt N s.population.resource s.population.divisions a c b d.val,s.collected⟩
  | .inr i =>
    ⟨extractionAt s.population.resource s.population.divisions (s.population.live.take i.val)
      (selectedCell s.population i) (s.population.live.drop (i.val+1)),s.collected+1⟩

def productiveRate (rho γ : ℝ) (Ω : ℕ) (s : ProductiveState) : ProductiveEvent s → ℝ
  | .inl e =>
    let c := selectedCell s.population e.1
    match e.2 with
    | .inl r => propensity (resourceCoefficient γ s.population.resource Ω) c.compartment (.inl r)
    | .inr d => propensity (resourceCoefficient γ s.population.resource Ω) c.compartment (.inr ()) *
      daughterWeight (nextCompartment c.compartment (.inr ())).1 d.val
  | .inr i => rho*((selectedCell s.population i).compartment.1 2:ℝ)

theorem productive_rate_nonneg (rho γ : ℝ) (hr : 0 ≤ rho) (hg : 0 ≤ γ)
    (Ω : ℕ) (s : ProductiveState) (e : ProductiveEvent s) : 0 ≤ productiveRate rho γ Ω s e := by
  have hb : 0 ≤ resourceCoefficient γ s.population.resource Ω := by unfold resourceCoefficient; positivity
  cases e with
  | inl e =>
    rcases e with ⟨i,r | d⟩
    · exact propensity_nonneg _ hb (selectedCell s.population i).compartment (.inl r)
    · exact mul_nonneg (propensity_nonneg _ hb _ _) (daughterWeight_nonneg _ _)
  | inr i => dsimp [productiveRate]; positivity

theorem productive_legacy_outcome (N : ℕ) (E : ℕ) {D : Finset PopulationState}
    (e : PopulationEvent D) :
    productiveOutcome N ⟨e.1.val,E⟩ (.inl e.2) = ⟨eventOutcome N e,E⟩ := by
  rcases e with ⟨s,i,r | d⟩ <;> rfl

theorem productive_legacy_rate (rho γ : ℝ) (Ω E : ℕ) {D : Finset PopulationState}
    (e : PopulationEvent D) :
    productiveRate rho γ Ω ⟨e.1.val,E⟩ (.inl e.2) = eventRate γ Ω e := by
  rcases e with ⟨s,i,r | d⟩ <;> rfl

theorem extraction_membrane (Q D : ℕ) (a : List TaggedCell) (c : TaggedCell) (b : List TaggedCell) :
    membrane (extractionAt Q D a c b).live = membrane (sourceAt Q D a c b).live := by
  simp [extractionAt,sourceAt]

theorem productive_extraction_resource (N : ℕ) (s : ProductiveState) (i : Fin s.population.live.length) :
    (productiveOutcome N s (.inr i)).population.resource = s.population.resource := rfl

theorem productive_extraction_membrane (N : ℕ) (s : ProductiveState) (i : Fin s.population.live.length) :
    membrane (productiveOutcome N s (.inr i)).population.live = membrane s.population.live := by
  change membrane (extractionAt _ _ _ _ _).live = _
  rw [extraction_membrane]
  simp only [sourceAt,selected_decomposition]

def zInventory (cs : List TaggedCell) : ℕ := (cs.map (fun c => c.compartment.1 2)).sum

theorem extraction_z_balance (Q D : ℕ) (a : List TaggedCell) (c : TaggedCell) (b : List TaggedCell)
    (hc : 1 ≤ c.compartment.1 2) :
    zInventory (extractionAt Q D a c b).live+1 = zInventory (sourceAt Q D a c b).live := by
  simp [zInventory,extractionAt,sourceAt,channelNext,Matrix.cons_val_two]
  omega

theorem productive_extraction_z_account (N : ℕ) (s : ProductiveState) (i : Fin s.population.live.length)
    (hc : 1 ≤ (selectedCell s.population i).compartment.1 2) :
    zInventory (productiveOutcome N s (.inr i)).population.live+(productiveOutcome N s (.inr i)).collected =
      zInventory s.population.live+s.collected := by
  have h := extraction_z_balance s.population.resource s.population.divisions
    (s.population.live.take i.val) (selectedCell s.population i) (s.population.live.drop (i.val+1)) hc
  simp only [sourceAt,selected_decomposition] at h
  change zInventory (extractionAt _ _ _ _ _).live+(s.collected+1) = _
  omega

end
end ProductiveMemory

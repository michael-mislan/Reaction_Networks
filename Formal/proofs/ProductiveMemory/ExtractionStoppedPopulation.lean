import proofs.ProductiveMemory.ExtractionPopulationSource
import proofs.ProductiveMemory.ExtractionSelected

namespace ProductiveMemory
open FiniteCopy HeritableCompositions ResourceLimitedCompetition
noncomputable section
set_option Elab.async false

abbrev ProductiveActive (D : Finset ProductiveState) := {s : ProductiveState // s ∈ D}
abbrev ProductivePopulationEvent (D : Finset ProductiveState) := Σ s : ProductiveActive D, ProductiveEvent s.val
abbrev ProductiveStopped (D : Finset ProductiveState) := ProductiveActive D ⊕ ProductivePopulationEvent D

inductive ProductiveStop where
  | active | outer | divisionEnergy | partition | nutrient | collectionQuota
  deriving DecidableEq

def productiveReason (N W0 J : ℕ) (rho zL zH : ℝ) {D : Finset ProductiveState}
    (e : ProductivePopulationEvent D) : ProductiveStop := by
  classical
  let s := e.1.val
  exact match e.2 with
  | .inl ⟨i,.inl r⟩ =>
      let c := selectedCell s.population i
      if 8*readyLevel ≤ extractionCellEnergy rho zL zH ⟨c.high,nextCompartment c.compartment (.inl r)⟩
      then .outer else .active
  | .inl ⟨i,.inr d⟩ =>
      let c := selectedCell s.population i
      let p := nextCompartment c.compartment (.inr ())
      if 8*readyLevel ≤ extractionCellEnergy rho zL zH ⟨c.high,p⟩ then .outer
      else if p.2=2*N then
        if 2*readyLevel < extractionCellEnergy rho zL zH ⟨c.high,p⟩ then .divisionEnergy
        else if ¬(extractionCellEnergy rho zL zH ⟨c.high,(d.val,N)⟩ < 4*readyLevel ∧
          extractionCellEnergy rho zL zH ⟨c.high,((fun j => p.1 j-d.val j),N)⟩ < 4*readyLevel)
          then .partition
        else if s.population.resource-1=W0 then .nutrient else .active
      else if s.population.resource-1=W0 then .nutrient else .active
  | .inr i =>
      let c := selectedCell s.population i
      if 8*readyLevel ≤ extractionCellEnergy rho zL zH
        ⟨c.high,(channelNext c.compartment.1 (.inr ()),c.compartment.2)⟩ then .outer
      else if J ≤ s.collected+1 then .collectionQuota else .active

def productiveStoppedNext (N W0 J : ℕ) (rho zL zH : ℝ) (D : Finset ProductiveState)
    (x : ProductiveStopped D) (e : ProductivePopulationEvent D) : ProductiveStopped D := by
  classical
  exact match x with
  | .inr _ => x
  | .inl s => if e.1=s then
      if productiveReason N W0 J rho zL zH e=.active then
        if h : productiveOutcome N e.1.val e.2 ∈ D then .inl ⟨productiveOutcome N e.1.val e.2,h⟩ else .inr e
      else .inr e
    else x

def productiveStoppedModel (rho γ : ℝ) (hr : 0 ≤ rho) (hg : 0 ≤ γ)
    (Ω N W0 J : ℕ) (zL zH : ℝ) (D : Finset ProductiveState) :
    FiniteJumpModel (ProductiveStopped D) (ProductivePopulationEvent D) := by
  classical
  exact {
    next := productiveStoppedNext N W0 J rho zL zH D
    rate := fun x e => match x with
      | .inr _ => 0
      | .inl s => if e.1=s then productiveRate rho γ Ω e.1.val e.2 else 0
    nonneg := by
      intro x e
      cases x with
      | inr e => exact le_rfl
      | inl s =>
        dsimp only
        split_ifs
        · exact productive_rate_nonneg rho γ hr hg Ω e.1.val e.2
        · exact le_rfl }

def productivePhysical (N : ℕ) {D : Finset ProductiveState} : ProductiveStopped D → ProductiveState
  | .inl s => s.val
  | .inr e => productiveOutcome N e.1.val e.2

theorem productive_physical_chosen (N W0 J : ℕ) (rho zL zH : ℝ) (D : Finset ProductiveState)
    (e : ProductivePopulationEvent D) :
    productivePhysical N (productiveStoppedNext N W0 J rho zL zH D (.inl e.1) e) =
      productiveOutcome N e.1.val e.2 := by
  classical
  unfold productiveStoppedNext
  dsimp only
  rw [if_pos rfl]
  split_ifs <;> rfl

theorem productive_terminal_generator (rho γ : ℝ) (hr : 0 ≤ rho) (hg : 0 ≤ γ)
    (Ω N W0 J : ℕ) (zL zH : ℝ) (D : Finset ProductiveState)
    (f : ProductiveStopped D → ℝ) (e : ProductivePopulationEvent D) :
    (productiveStoppedModel rho γ hr hg Ω N W0 J zL zH D).generator f (.inr e) = 0 := by
  classical
  simp [FiniteJumpModel.generator,productiveStoppedModel]

theorem productive_active_generator (rho γ : ℝ) (hr : 0 ≤ rho) (hg : 0 ≤ γ)
    (Ω N W0 J : ℕ) (zL zH : ℝ) (D : Finset ProductiveState)
    (f : ProductiveStopped D → ℝ) (s : ProductiveActive D) :
    (productiveStoppedModel rho γ hr hg Ω N W0 J zL zH D).generator f (.inl s) =
      ∑ e : ProductiveEvent s.val, productiveRate rho γ Ω s.val e*
        (f (productiveStoppedNext N W0 J rho zL zH D (.inl s) ⟨s,e⟩)-f (.inl s)) := by
  classical
  unfold FiniteJumpModel.generator
  rw [Fintype.sum_sigma,Finset.sum_eq_single s]
  · simp [productiveStoppedModel]
  · intro b _ hbs
    simp [productiveStoppedModel,hbs]
  · simp

end
end ProductiveMemory

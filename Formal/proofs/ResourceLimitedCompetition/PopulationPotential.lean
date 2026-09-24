import proofs.ResourceLimitedCompetition.PopulationTransitions
import proofs.ResourceLimitedCompetition.SpatialReset

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy

noncomputable def potentialSum (F : TaggedCell → ℝ) (s : PopulationState) : ℝ :=
  (s.live.map F).sum

/-- Value after the raw unsplit cell reaction; useful as an upper bound for
the stopped, compound-division observable. -/
noncomputable def rawEventPotential (F : TaggedCell → ℝ) (s : PopulationState)
    (e : CellEvent s) : ℝ :=
  let c := selectedCell s e.1
  let r : Channel := match e.2 with
    | .inl r => .inl r
    | .inr _ => .inr ()
  potentialSum F s-F c+F ⟨c.high,nextCompartment c.compartment r⟩

theorem daughter_constant_sum (n : Counts) (a b : ℝ) :
    (∑ d : {d : Counts // d ∈ daughterDraws n}, a*daughterWeight n d.val*b)=a*b := by
  classical
  calc
    _ = (∑ d : {d : Counts // d ∈ daughterDraws n}, daughterWeight n d.val)*(a*b) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ = a*b := by rw [Finset.sum_coe_sort,daughterWeight_sum,one_mul]

theorem raw_event_generator_sum (γ : ℝ) (Ω : ℕ) (D : Finset PopulationState)
    (s : ActiveState D) (F : TaggedCell → ℝ) :
    (∑ e : CellEvent s.val, eventRate γ Ω ⟨s,e⟩*
      (rawEventPotential F s.val e-potentialSum F s.val)) =
      ∑ i : Fin s.val.live.length, compartmentGenerator
        (resourceCoefficient γ s.val.resource Ω)
        (fun c => F ⟨(selectedCell s.val i).high,c⟩) (selectedCell s.val i).compartment := by
  classical
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_sum_type]
  simp only [eventRate,rawEventPotential]
  have hdiff (x a b : ℝ) : x-a+b-x=b-a := by ring
  simp only [hdiff]
  rw [daughter_constant_sum]
  unfold compartmentGenerator
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_unique]

theorem population_potential_generator_le (γ : ℝ) (hγ : 0 ≤ γ)
    (Ω N M : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (f : StoppedPopulation D → ℝ) (s : ActiveState D) (F : TaggedCell → ℝ)
    (hstart : f (.inl s)=potentialSum F s.val)
    (hnext : ∀ e : CellEvent s.val,
      f (stoppedNext N M zL zH D (.inl s) ⟨s,e⟩) ≤ rawEventPotential F s.val e) :
    (stoppedPopulationModel γ hγ Ω N M zL zH D).generator f (.inl s) ≤
      ∑ i : Fin s.val.live.length, compartmentGenerator
        (resourceCoefficient γ s.val.resource Ω)
        (fun c => F ⟨(selectedCell s.val i).high,c⟩) (selectedCell s.val i).compartment := by
  have h := active_generator_le γ hγ Ω N M zL zH D f s (rawEventPotential F s.val) hnext
  rw [hstart,raw_event_generator_sum] at h
  exact h

end ResourceLimitedCompetition

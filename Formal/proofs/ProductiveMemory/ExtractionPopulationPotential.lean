import proofs.ProductiveMemory.ExtractionBatchDomain
import proofs.ResourceLimitedCompetition.PopulationPotential

namespace ProductiveMemory
open FiniteCopy HeritableCompositions ResourceLimitedCompetition
noncomputable section
set_option Elab.async false

def productiveRawPotential (F : TaggedCell → ℝ) (s : ProductiveState) : ProductiveEvent s → ℝ
  | .inl e => rawEventPotential F s.population e
  | .inr i =>
      let c := selectedCell s.population i
      potentialSum F s.population-F c+F ⟨c.high,(channelNext c.compartment.1 (.inr ()),c.compartment.2)⟩

theorem productive_raw_generator_sum (rho γ : ℝ) (Ω : ℕ) (s : ProductiveState) (F : TaggedCell → ℝ) :
    (∑ e : ProductiveEvent s, productiveRate rho γ Ω s e*
      (productiveRawPotential F s e-potentialSum F s.population)) =
      ∑ i : Fin s.population.live.length, growingCompartmentGenerator rho
        (resourceCoefficient γ s.population.resource Ω)
        (fun c => F ⟨(selectedCell s.population i).high,c⟩) (selectedCell s.population i).compartment := by
  classical
  rw [Fintype.sum_sum_type]
  have hlegacy := raw_event_generator_sum γ Ω {s.population}
    ⟨s.population,Finset.mem_singleton_self _⟩ F
  have heq : (∑ e : CellEvent s.population, productiveRate rho γ Ω s (.inl e)*
      (productiveRawPotential F s (.inl e)-potentialSum F s.population)) =
      ∑ i : Fin s.population.live.length, compartmentGenerator
        (resourceCoefficient γ s.population.resource Ω)
        (fun c => F ⟨(selectedCell s.population i).high,c⟩) (selectedCell s.population i).compartment := by
    convert hlegacy using 1
    apply Finset.sum_congr rfl
    intro e _
    rcases e with ⟨i,r | d⟩ <;> rfl
  rw [heq]
  simp only [growing_generator_split,Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  dsimp [productiveRate,productiveRawPotential]
  ring

theorem productive_potential_generator_le (rho γ : ℝ) (hr : 0 ≤ rho) (hg : 0 ≤ γ)
    (Ω N W0 J : ℕ) (zL zH : ℝ) (D : Finset ProductiveState)
    (f : ProductiveStopped D → ℝ) (s : ProductiveActive D) (F : TaggedCell → ℝ)
    (hstart : f (.inl s)=potentialSum F s.val.population)
    (hnext : ∀ e : ProductiveEvent s.val,
      f (productiveStoppedNext N W0 J rho zL zH D (.inl s) ⟨s,e⟩) ≤ productiveRawPotential F s.val e) :
    (productiveStoppedModel rho γ hr hg Ω N W0 J zL zH D).generator f (.inl s) ≤
      ∑ i : Fin s.val.population.live.length, growingCompartmentGenerator rho
        (resourceCoefficient γ s.val.population.resource Ω)
        (fun c => F ⟨(selectedCell s.val.population i).high,c⟩) (selectedCell s.val.population i).compartment := by
  rw [productive_active_generator,hstart,← productive_raw_generator_sum]
  exact Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left
    (sub_le_sub_right (hnext e) _) (productive_rate_nonneg rho γ hr hg Ω s.val e))

end
end ProductiveMemory

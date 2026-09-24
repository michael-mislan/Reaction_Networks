import proofs.RandomViability.OccupiedSourceBarrier
import proofs.RandomViability.JumpPositiveRate
import proofs.RandomViability.PhysicalTrajectory

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 30000

def boundedCatalyticFiring {n : ℕ} (k : ℕ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) : Prop :=
  ∃ i r x d, countMass (z i).1 ≤ k ∧
    (z (i+1)).2.1 = Sum.inr (.inr (.inr (r,x,d)))

variable {n : ℕ} [m : MeasurableSpace (PhysicalCountChannel n)]
  [s : MeasurableSingletonClass (PhysicalCountChannel n)]

/-- The occupied-source barrier holds on the actual unbounded reactor law,
simultaneously at every jump. No noise or cutoff error is introduced. -/
theorem physical_bounded_catalytic_firing_requires_source
    (hn : 2 ≤ n) (k : ℕ) (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (hV : 0 < (V : ℝ)) (hD : 0 < (D : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) :
    ∀ᵐ z ∂physicalTrajectoryLaw hn c V D hV hD basal cat N,
      boundedCatalyticFiring k z → ShortIncidence k c := by
  have hp := jumpTrajectory_positive_rate N unboundedPhysicalNext
    (unboundedPhysicalRate c V D basal cat) (unboundedPhysicalRate_nonneg c V D basal cat)
    (unbounded_total_pos hn c V D hV hD basal cat)
  filter_upwards [hp] with z hz
  rintro ⟨i,r,x,d,hM,htag⟩
  by_contra hgood
  obtain ⟨b,hb,hr⟩ := hz i
  have hbe : b = .inr (.inr (r,x,d)) := Sum.inr.inj (hb.symm.trans htag)
  rw [hbe, catalytic_rate_zero_outside_occupied_source c hgood V D basal cat (z i).1 hM r x d] at hr
  exact (lt_irrefl (0 : ℝ)) hr

theorem physical_bounded_catalytic_firing_zero
    (hn : 2 ≤ n) (k : ℕ) (c : SourceMoleculeFibreConfig n) (hgood : ¬ShortIncidence k c)
    (V D : NNReal) (hV : 0 < (V : ℝ)) (hD : 0 < (D : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) :
    physicalTrajectoryLaw hn c V D hV hD basal cat N {z | boundedCatalyticFiring k z} = 0 := by
  have hh : ∀ᵐ z ∂physicalTrajectoryLaw hn c V D hV hD basal cat N,
      ¬boundedCatalyticFiring k z := by
    filter_upwards [physical_bounded_catalytic_firing_requires_source hn k c V D hV hD basal cat N]
      with z hz
    exact fun h => hgood (hz h)
  simpa only [not_not] using ae_iff.mp hh

end
end RandomViability

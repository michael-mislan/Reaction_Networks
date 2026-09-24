import proofs.RandomViability.OccupiedSourceEvent
import proofs.RandomViability.SourceUptakeTail

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 30000

variable {n : ℕ} [m : MeasurableSpace (PhysicalCountChannel n)]
  [s : MeasurableSingletonClass (PhysicalCountChannel n)]

/-- Unconditional source-averaged upper bound on an actual bounded-mass
catalytic firing, at any jump time. There is no molecular-noise remainder. -/
theorem source_bounded_catalytic_firing_upper (hn : 4 ≤ n) (k : ℕ)
    (a : ℝ) (ha : 1 < a) (V D : NNReal) (hV : 0 < (V : ℝ)) (hD : 0 < (D : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) :
    sourceAverage a n (fun c =>
      (physicalTrajectoryLaw (by omega) c V D hV hD basal cat N
        {z | boundedCatalyticFiring k z}).toReal) ≤
      (Fintype.card (Molecule k)*Fintype.card (Reaction (k+2)) : ℕ)*
        (windowZipfMean a (sourceReactionCount n)/sourceReactionCount n) := by
  let f : SourceMoleculeFibreConfig n → ℝ := fun c =>
    (physicalTrajectoryLaw (by omega) c V D hV hD basal cat N
      {z | boundedCatalyticFiring k z}).toReal
  have hp : ∀ c, f c ≤ 1 := by
    intro c
    exact measureReal_le_one
  have hz : ∀ c, ¬ShortIncidence k c → f c ≤ 0 := by
    intro c hc
    dsimp [f]
    rw [physical_bounded_catalytic_firing_zero (by omega) k c hc V D hV hD basal cat N]
    exact le_rfl
  have hh := sourceAverage_le_bad_add a n ha hn (ShortIncidence k) f 0 (le_refl _) hp hz
  rw [add_zero] at hh
  exact hh.trans (shortIncidence_mass_le a n k ha hn)

end
end RandomViability

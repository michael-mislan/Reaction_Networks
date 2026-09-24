import proofs.RandomViability.ProductiveJointLimit
import proofs.RandomViability.ProductiveControl
import proofs.RandomViability.PassiveEquilibrium
import proofs.RandomViability.LiteralStartup

namespace RandomViability
open Filter Topology
noncomputable section

/-- The declared rare-event regime: fully averaged positive physical RAF
operation at a growing volume, explicit finite bounds, sharp logarithmic
rate, and the distinct zero-basal startup obstruction. This does not claim
the stronger high-volume conditional-reliability formulation. -/
theorem random_autocatalysis_rare_event_regime :
    Tendsto productiveVolume atTop atTop ∧
    (∀ n, 40 ≤ productiveVolume n) ∧
    (∀ᶠ n in atTop, 0 < productiveJointProbability n) ∧
    (∀ n, 4 ≤ n →
      productiveBeta (productiveVolume n)*productiveSourceIncidence n ≤ productiveJointProbability n ∧
      productiveJointProbability n ≤ productiveUpperCoefficient (productiveVolume n)*productiveSourceIncidence n) ∧
    Tendsto (fun n => Real.log (productiveJointProbability n)/(n : ℝ))
      atTop (𝓝 (-Real.log 2)) ∧
    Tendsto (fun n : ℕ => eventMass (2-2/(n : ℝ)) n FoodEscape) atTop (𝓝 0) := by
  exact ⟨productive_volume_tendsto,productive_volume_ge,productive_joint_probability_eventually_pos,
    productive_joint_probability_bounds,productive_joint_logarithmic_limit,literal_foodEscape_mass_tendsto_zero⟩

end
end RandomViability

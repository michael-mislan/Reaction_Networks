import proofs.RandomViability.JumpStateLaplace
import proofs.RandomViability.PhysicalFoodLaplace

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 30000

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem physical_food_multiplier_integral (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (hV : 0 < (V : ℝ)) (hD : 0 < (D : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) :
    ∫⁻ y, jumpMultiplier (fun ch => (2 : ℝ)^foodInputMass ch) (14*(D : ℝ)*V) y ∂
      jumpStateKernel unboundedPhysicalNext (unboundedPhysicalRate c V D basal cat)
        (unboundedPhysicalRate_nonneg c V D basal cat) (unbounded_total_pos hn c V D hV hD basal cat) N = 1 := by
  rw [jumpState_weight_laplace unboundedPhysicalNext (unboundedPhysicalRate c V D basal cat)
    (unboundedPhysicalRate_nonneg c V D basal cat) (unbounded_total_pos hn c V D hV hD basal cat)
    (fun ch => (2 : ℝ)^foodInputMass ch) (fun _ => by positivity) (14*(D : ℝ)*V) N
    (by have ht := unbounded_total_pos hn c V D hV hD basal cat N; positivity)]
  rw [physical_food_laplace_factor hn c V D hV hD basal cat N, ENNReal.ofReal_one]

end
end RandomViability

import proofs.LowFounderPrediction.MixedResolution
import proofs.LowFounderPrediction.Minimality
import proofs.LowFounderPrediction.ObservationAlgebra

namespace LowFounderPrediction
noncomputable section
open MeasureTheory

theorem robust_constant_above_95 :
    (19/20 : ℝ) < 57461421889141/60212040602000 := by norm_num

/-- At the same physical-time reference source, three is the smallest one-sided
95% endpoint. The uniform perturbed/observed result is robust_endpoint_three_mixed. -/
theorem reference_minimum_endpoint :
    (19/20 : ℝ) ≤ (oneFounder Minimality.reference (5/24)).real good ∧
    ∀ k : ℕ, k < 3 → (oneFounder Minimality.reference (5/24)).real {x | x.1+x.2 ≤ k} < 19/20 := by
  constructor
  · have h := one_founder_lower Minimality.reference Minimality.reference_admissible
      (5/24) (by norm_num) (by norm_num) (by norm_num)
    linarith [robust_constant_above_95]
  · intro k hk
    exact Minimality.no_lower_endpoint k (by omega)

end
end LowFounderPrediction

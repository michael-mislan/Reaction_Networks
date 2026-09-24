import proofs.TinyProgrammableChemicalFactory.Partition

namespace TinyProgrammableChemicalFactory

/-- Sign of the central-binomial derivative on the left half interval.
The finite-sum derivative identity and its global endpoint reduction remain C. -/
theorem central_derivative_nonneg (n : ℕ) (θ : ℝ) (h0 : 0≤θ) (hhalf : θ≤1/2) :
    0≤(n : ℝ)*((n-1).choose 7 : ℝ)*θ^7*(1-θ)^7*
      ((1-θ)^(n-15)-θ^(n-15)) := by
  have h : θ≤1-θ := by linarith
  have hp : θ^(n-15)≤(1-θ)^(n-15) := pow_le_pow_left₀ h0 h _
  have hn : 0≤1-θ := by linarith
  exact mul_nonneg (by positivity) (sub_nonneg.mpr hp)

theorem recovery_partition_product_mono (a b c d : ℝ)
    (ha : 0≤a) (hc : 0≤c) (hab : a≤b) (hcd : c≤d) : a*c≤b*d :=
  mul_le_mul hab hcd hc (ha.trans hab)

end TinyProgrammableChemicalFactory

import Mathlib
namespace PhenotypeMemory
/-- The conditional-covariance induction step for fair product bits. -/
theorem association_step (ef0 ef1 eg0 eg1 efg0 efg1 : ℝ)
    (h0 : ef0*eg0 ≤ efg0) (h1 : ef1*eg1 ≤ efg1)
    (hf : ef0 ≤ ef1) (hg : eg0 ≤ eg1) :
    ((ef0+ef1)/2)*((eg0+eg1)/2) ≤ (efg0+efg1)/2 := by
  have := mul_nonneg (sub_nonneg.mpr hf) (sub_nonneg.mpr hg)
  nlinarith
theorem opposite_association_step (ef0 ef1 eg0 eg1 efg0 efg1 : ℝ)
    (h0 : efg0 ≤ ef0*eg0) (h1 : efg1 ≤ ef1*eg1)
    (hf : ef0 ≤ ef1) (hg : eg1 ≤ eg0) :
    (efg0+efg1)/2 ≤ ((ef0+ef1)/2)*((eg0+eg1)/2) := by
  have := mul_nonneg (sub_nonneg.mpr hf) (sub_nonneg.mpr hg)
  nlinarith
theorem nonmonotone_obstruction :
    (1/2 : ℝ) - (1/2)^2 = 1/4 := by norm_num
end PhenotypeMemory

import Mathlib.Tactic

namespace AssayInformation

/-- Each term in the block cross-product comparison is positive. -/
theorem ordered_multiplier_term (u v early late : ℝ)
    (hu : 0 < u) (hv : 0 < v) (hm : late < early) :
    0 < u*v*(early-late) :=
  mul_pos (mul_pos hu hv) (sub_pos.mpr hm)

/-- Finite positive block sums inherit a strict ordering of multipliers. -/
theorem block_ratio_bound (u1 u2 v1 v2 m : ℝ)
    (hu1 : 0 < u1) (hu2 : 0 < u2) (hv1 : 0 < v1)
    (hu : m*u1 ≤ u2) (hv : v2 < m*v1) :
    v2/u2 < v1/u1 := by
  apply (div_lt_div_iff₀ hu2 hu1).2
  nlinarith

end AssayInformation

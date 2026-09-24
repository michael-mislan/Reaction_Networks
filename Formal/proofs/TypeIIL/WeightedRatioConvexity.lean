import Mathlib

namespace TypeIIL

/-- A stationary-current reconstruction with nonnegative routing weights is a
positive weighted-average identity.  At a global maximum of the routed
species ratios, the product-monomial ratio cannot lie strictly below the
reactant ratio. -/
theorem product_ratio_ge_at_routed_max
    {ι : Type*} [Fintype ι]
    {rhoR beta p q : ℝ} {h y rho : ι → ℝ}
    (hq : 0 < q) (hy : ∀ i, 0 < y i) (hh : ∀ i, 0 ≤ h i)
    (hbase : p = q + ∑ i, h i * y i)
    (hratio : rhoR * p = beta * q + ∑ i, h i * y i * rho i)
    (hmax : ∀ i, rho i ≤ rhoR) :
    rhoR ≤ beta := by
  have hsum : ∑ i, h i * y i * rho i ≤
      rhoR * ∑ i, h i * y i := by
    calc
      ∑ i, h i * y i * rho i ≤ ∑ i, h i * y i * rhoR := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hmax i)
          (mul_nonneg (hh i) (le_of_lt (hy i)))
      _ = rhoR * ∑ i, h i * y i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have hid : q * (beta - rhoR) =
      rhoR * ∑ i, h i * y i - ∑ i, h i * y i * rho i := by
    linear_combination rhoR * hbase - hratio
  by_contra hnot
  have hbeta : beta < rhoR := lt_of_not_ge hnot
  have hstrict : q * (beta - rhoR) < 0 :=
    mul_neg_of_pos_of_neg hq (sub_neg.mpr hbeta)
  linarith

/-- Dual extremal-selection lemma at a global minimum. -/
theorem product_ratio_le_at_routed_min
    {ι : Type*} [Fintype ι]
    {rhoR beta p q : ℝ} {h y rho : ι → ℝ}
    (hq : 0 < q) (hy : ∀ i, 0 < y i) (hh : ∀ i, 0 ≤ h i)
    (hbase : p = q + ∑ i, h i * y i)
    (hratio : rhoR * p = beta * q + ∑ i, h i * y i * rho i)
    (hmin : ∀ i, rhoR ≤ rho i) :
    beta ≤ rhoR := by
  have hsum : rhoR * ∑ i, h i * y i ≤
      ∑ i, h i * y i * rho i := by
    calc
      rhoR * ∑ i, h i * y i = ∑ i, h i * y i * rhoR := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ ∑ i, h i * y i * rho i := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hmin i)
          (mul_nonneg (hh i) (le_of_lt (hy i)))
  have hid : q * (beta - rhoR) =
      rhoR * ∑ i, h i * y i - ∑ i, h i * y i * rho i := by
    linear_combination rhoR * hbase - hratio
  by_contra hnot
  have hbeta : rhoR < beta := lt_of_not_ge hnot
  have hstrict : 0 < q * (beta - rhoR) :=
    mul_pos hq (sub_pos.mpr hbeta)
  linarith

end TypeIIL

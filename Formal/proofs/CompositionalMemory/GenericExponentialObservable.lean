import Mathlib

namespace CompositionalMemory

theorem exponential_observable_of_ratio {ι : Type*} [Fintype ι]
    (rate energy : ι → ℝ) (base a bound : ℝ)
    (h : ∑ j, rate j*(Real.exp (a*(energy j-base))-1) ≤ bound) :
    ∑ j, rate j*(Real.exp (a*energy j)-Real.exp (a*base)) ≤
      bound*Real.exp (a*base) := by
  have hid (j) : Real.exp (a*energy j)-Real.exp (a*base) =
      Real.exp (a*base)*(Real.exp (a*(energy j-base))-1) := by
    rw [mul_sub,mul_one,← Real.exp_add]
    congr 2
    ring
  simp_rw [hid]
  calc
    _ = Real.exp (a*base)*(∑ j, rate j*(Real.exp (a*(energy j-base))-1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ Real.exp (a*base)*bound := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = _ := by ring

end CompositionalMemory

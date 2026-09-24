import proofs.RandomViability.ProductiveWindows
import proofs.RandomViability.ProductiveCylinder

namespace RandomViability
open Classical
noncomputable section
set_option maxHeartbeats 30000

def productivePathBudget (V : ℝ) (m : ℕ) (eps : ℝ) : ℝ :=
  (eps*productiveWaitWidth m)^(3*m+1)*Real.exp (-4800000*V)

theorem productive_path_budget_pos (V : ℝ) (m : ℕ) (eps : ℝ)
    (hm : 0 < m) (heps : 0 < eps) : 0 < productivePathBudget V m eps := by
  unfold productivePathBudget
  exact mul_pos (pow_pos (mul_pos heps (productive_wait_width_pos m hm)) _) (Real.exp_pos _)

/-- A single explicit positive budget pays for the entire selected path and
all competing channels, including its terminal no-intervening-jump window. -/
theorem productive_window_product_lower (V : ℝ) (m : ℕ) (eps : ℝ)
    (hV : 0 ≤ V) (hm : 0 < m) (heps : 0 ≤ eps) :
    ENNReal.ofReal (productivePathBudget V m eps) ≤
      ∏ i : Fin (3*m+1), ENNReal.ofReal (eps*productiveWaitWidth m*
        Real.exp (-(24000*V)*(productiveWaitLower m i+productiveWaitWidth m))) := by
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ =>
    mul_nonneg (mul_nonneg heps (productive_wait_width_pos m hm).le) (Real.exp_pos _).le)]
  apply ENNReal.ofReal_le_ofReal
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Real.exp_sum, ← Finset.mul_sum]
  have hs : (∑ i : Fin (3*m+1), (productiveWaitLower m i+productiveWaitWidth m)) < 200 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => productiveWaitLower m i+productiveWaitWidth m) (3*m+1)]
    exact productive_wait_paid_upper m hm
  have he : Real.exp (-4800000*V) ≤ Real.exp (-(24000*V)*
      (∑ i : Fin (3*m+1), (productiveWaitLower m i+productiveWaitWidth m))) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact mul_le_mul_of_nonneg_left he (pow_nonneg (mul_nonneg heps (productive_wait_width_pos m hm).le) _)

end
end RandomViability

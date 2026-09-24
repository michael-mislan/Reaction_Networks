import proofs.RandomViability.BindingCountExponential

namespace RandomViability.Binding
noncomputable section
open scoped BigOperators

def returnPotential (N : Counts) : ℝ := Real.exp (-(2/25)*(weightedCount N-20000))
def returnSource : ℝ := 300000000000*Real.exp (-(799982:ℝ)/125)

theorem literalGenerator_scale (N : Counts) (V eps k r c : ℝ) (f : Counts → ℝ) :
    literalGenerator N V eps k r (fun X => c*f X) = c*literalGenerator N V eps k r f := by
  unfold literalGenerator
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem returnPotential_small (N : Counts) (h : 40000 ≤ weightedCount N) :
    returnPotential N ≤ Real.exp (-1600) := by
  apply Real.exp_le_exp.mpr
  linarith

theorem returnPotential_exit (N : Counts) (h : weightedCount N ≤ 20000) :
    1 ≤ returnPotential N := by
  apply Real.one_le_exp_iff.mpr
  linarith

theorem return_low_drift (N : Counts) (eps k r : ℝ)
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1/1000000) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 18 ≤ r) (hr1 : r ≤ 22) (h : resourceGood N 100000000)
    (hY : weightedCount N ≤ 100000) :
    literalGenerator N 100000000 eps k r returnPotential ≤ 0 := by
  have he : returnPotential = (fun X => Real.exp 1600*Real.exp (-(2/25)*weightedCount X)) := by
    funext X
    unfold returnPotential
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he,literalGenerator_scale]
  have hg := actual_entry_exponential N 100000000 eps k r (2/25) (by norm_num)
    heps heps1 hk hk1 hr hr1 h (by norm_num; exact hY) (by norm_num) (by norm_num)
  have hy := weightedCount_nonneg N
  have hn : -(3/10*(2/25)-3*(2/25)^2)*weightedCount N-(14/25)*eps*(100000000:ℝ)*(2/25) ≤ 0 := by
    nlinarith
  have hd := hg.trans (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hn)
  exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hd

theorem return_high_drift (N : Counts) (eps k r : ℝ)
    (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r)
    (hY : 100000 ≤ weightedCount N)
    (htotal : (∑ j,countRate N 100000000 eps k r j) ≤ 300000000000) :
    literalGenerator N 100000000 eps k r returnPotential ≤ returnSource := by
  have hm : literalGenerator N 100000000 eps k r returnPotential ≤
      (∑ j,countRate N 100000000 eps k r j)*Real.exp (-(799982:ℝ)/125) := by
    rw [literalGenerator,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    by_cases hz : countRate N 100000000 eps k r j = 0
    · simp [hz]
    · have hj := weighted_actual_jump N j (rate_support N 100000000 eps k r j hz)
      have hb := (abs_le.mp (weightedJump_bound j)).1
      have hnext : returnPotential (countNext N j) ≤ Real.exp (-(799982:ℝ)/125) := by
        apply Real.exp_le_exp.mpr
        linarith
      have hf : returnPotential (countNext N j)-returnPotential N ≤ Real.exp (-(799982:ℝ)/125) := by
        have hp : 0 ≤ returnPotential N := (Real.exp_pos _).le
        linarith
      exact mul_le_mul_of_nonneg_left hf (countRate_nonneg N 100000000 eps k r (by norm_num) heps hk hr j)
  exact hm.trans (mul_le_mul_of_nonneg_right htotal (Real.exp_pos _).le)

theorem return_foster (N : Counts) (eps k r : ℝ)
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1/1000000) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 18 ≤ r) (hr1 : r ≤ 22) (h : resourceGood N 100000000) :
    literalGenerator N 100000000 eps k r returnPotential ≤ returnSource := by
  by_cases hY : weightedCount N ≤ 100000
  · exact (return_low_drift N eps k r heps heps1 hk hk1 hr hr1 h hY).trans (by
      unfold returnSource
      positivity)
  · apply return_high_drift N eps k r heps hk (by linarith) (by linarith)
    have hb := total_rate_bound N 100000000 eps k r (by norm_num) heps (by linarith) hk hk1 (by linarith) hr1 (by
      intro i
      have hi := resource_count_cap N 100000000 h i
      norm_num at hi ⊢
      linarith)
    norm_num at hb
    exact hb

theorem evaluated_return_budget : Real.exp (-1600)+1000*returnSource < 1/10000 := by
  have h₁ := exp_neg_polynomial_upper 1600 (by norm_num) 2
  have h₂ := exp_neg_polynomial_upper (799982/125) (by norm_num) 6
  norm_num at h₁ h₂
  unfold returnSource
  linarith

end
end RandomViability.Binding

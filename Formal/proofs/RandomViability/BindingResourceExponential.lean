import proofs.RandomViability.BindingEntryExponential

namespace RandomViability.Binding
open scoped BigOperators

theorem moiety_exponential_tilt {ι : Type*} [Fintype ι]
    (rate jump : ι → ℝ) (V A θ : ℝ)
    (hr : ∀ j, 0 ≤ rate j) (hj : ∀ j, |jump j| ≤ 2)
    (hθ : |θ| ≤ 1/100) (hg : (∑ j,rate j*jump j) = V-A)
    (hq : (∑ j,rate j*(jump j)^2) ≤ V+2*A) :
    (∑ j,rate j*(Real.exp (θ*jump j)-1)) ≤
      θ*(V-A)+(3/5)*θ^2*(V+2*A) := by
  have he : (∑ j,rate j*(Real.exp (θ*jump j)-1)) ≤
      θ*(∑ j,rate j*jump j)+(3/5)*θ^2*(∑ j,rate j*(jump j)^2) := by
    calc
      _ ≤ ∑ j,rate j*(θ*jump j+(3/5)*θ^2*(jump j)^2) := by
        apply Finset.sum_le_sum
        intro j _
        have ha : |θ*jump j| ≤ 9/50 := by
          rw [abs_mul]
          exact (mul_le_mul hθ (hj j) (abs_nonneg _) (by norm_num)).trans (by norm_num)
        have h := exp_small_quadratic (θ*jump j) ha
        apply mul_le_mul_of_nonneg_left _ (hr j)
        nlinarith
      _ = _ := by
        simp only [Finset.mul_sum,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
  rw [hg] at he
  exact he.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hq (show 0 ≤ (3/5)*θ^2 by positivity)))

theorem upper_moiety_restoring (V A : ℝ) (hV : 0 ≤ V) (hA : (21/20)*V ≤ A) :
    (1/100)*(V-A)+(3/5)*(1/100)^2*(V+2*A) ≤ 0 := by linarith

theorem lower_moiety_restoring (V A : ℝ) (hV : 0 ≤ V) (hA : A ≤ (19/20)*V) :
    (-1/100)*(V-A)+(3/5)*(-1/100)^2*(V+2*A) ≤ 0 := by linarith

theorem exp_neg_polynomial_upper (x : ℝ) (hx : 0 < x) (n : ℕ) :
    Real.exp (-x) ≤ (n.factorial:ℝ)/x^n := by
  have h := Real.pow_div_factorial_le_exp x hx.le n
  have hf : 0 < (n.factorial:ℝ) := by positivity
  have hp := (div_le_iff₀ hf).mp h
  have hm := mul_le_mul_of_nonneg_left hp (Real.exp_pos (-x)).le
  have he : Real.exp (-x)*Real.exp x = 1 := by rw [← Real.exp_add]; simp
  apply (le_div_iff₀ (pow_pos hx n)).2
  nlinarith

/-- Evaluated resource budget; the generator-to-probability binding is separate. -/
theorem evaluated_resource_budget :
    (4:ℝ)*(Real.exp (-100000)+300000000000000*Real.exp (-50000+1/50)) < 1/10000 := by
  have h₁ := exp_neg_polynomial_upper 100000 (by norm_num) 5
  have h₂ := exp_neg_polynomial_upper (50000-1/50) (by norm_num) 5
  norm_num at h₁ h₂
  norm_num
  linarith

theorem final_error_budget (entry resource returned output clock : ℝ)
    (he : entry ≤ 1/12) (hr : resource ≤ 1/10000)
    (hb : returned ≤ 1/10000) (ho : output ≤ 1/10000)
    (hc : clock ≤ 1/600000000) :
    (9/10:ℝ) ≤ 1-entry-resource-returned-output-clock := by linarith

end RandomViability.Binding

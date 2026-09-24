import proofs.FiniteCopy.PoissonKernel
import proofs.RandomViability.BindingResourceExponential
import proofs.RandomViability.CopyNumberLogBound

namespace RandomViability.Binding
noncomputable section
open FiniteCopy
open scoped NNReal

theorem poissonized_after_cutoff {α : Type*} [Fintype α] (P : FiniteKernel α)
    (A : Set α) (x : α) (t : ℝ≥0) (N : ℕ) (a r : ℝ)
    (ha : 0 ≤ a) (hr : 0 < r) (hr1 : r ≤ 1)
    (h : ∀ n, N ≤ n → P.steps n (FiniteKernel.eventIndicator A) x ≤ a) :
    P.poissonized t (FiniteKernel.eventIndicator A) x ≤
      a+Real.exp (-(N:ℝ)*Real.log r+(t:ℝ)*(r-1)) := by
  have hb (n : ℕ) : P.steps n (FiniteKernel.eventIndicator A) x ≤
      a+Real.exp (-(N:ℝ)*Real.log r)*r^n := by
    by_cases hn : N ≤ n
    · exact (h n hn).trans (le_add_of_nonneg_right (by positivity))
    · have hnr : (n:ℝ) ≤ (N:ℝ) := by exact_mod_cast (le_of_lt (Nat.lt_of_not_ge hn))
      have hl : Real.log r ≤ 0 := Real.log_nonpos hr.le hr1
      have he : 1 ≤ Real.exp (-(N:ℝ)*Real.log r)*r^n := by
        rw [show r^n = Real.exp ((n:ℝ)*Real.log r) by rw [Real.exp_nat_mul,Real.exp_log hr],
          ← Real.exp_add]
        apply Real.one_le_exp_iff.mpr
        nlinarith
      have hp := (P.event_probability_bounds A n x).2
      linarith
  have hs : HasSum (fun n => poissonWeight t n*(a+Real.exp (-(N:ℝ)*Real.log r)*r^n))
      (a+Real.exp (-(N:ℝ)*Real.log r+(t:ℝ)*(r-1))) := by
    convert ((poissonWeight_sum t).mul_right a).add
      ((poissonWeight_geometric t r).mul_left (Real.exp (-(N:ℝ)*Real.log r))) using 1
    · funext n
      ring
    · rw [Real.exp_add]
      ring
  exact (Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hb n)
    (poissonWeight_nonneg t n)) (P.event_summable t A x) hs.summable).trans_eq hs.tsum_eq

theorem clock_exponent_bound (q : ℝ) (hq : 0 ≤ q) :
    -(499*q)*Real.log (999/1000)+(500*q)*((999/1000)-1) ≤ -q/500000 := by
  have h := log_one_add_lower (-1/1000) (by norm_num)
  norm_num at h
  have hm := mul_le_mul_of_nonneg_left h hq
  nlinarith

theorem evaluated_clock_error : Real.exp (-(300000000000:ℝ)/500000) < 1/600000000 := by
  have h := exp_neg_polynomial_upper 600000 (by norm_num) 2
  norm_num at h ⊢
  linarith

end
end RandomViability.Binding

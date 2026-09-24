import proofs.RandomViability.BindingPoissonDeadline

namespace FiniteCopyReactor
noncomputable section
open FiniteCopy Classical
open scoped NNReal

theorem poissonized_in_window {α : Type*} [Fintype α] (P : FiniteKernel α)
    (A : Set α) (x : α) (t : ℝ≥0) (L U : ℕ) (a r s : ℝ)
    (ha : 0 ≤ a) (hr : 0 < r) (hr1 : r ≤ 1) (hs : 1 ≤ s)
    (h : ∀ n, L ≤ n → n ≤ U → P.steps n (FiniteKernel.eventIndicator A) x ≤ a) :
    P.poissonized t (FiniteKernel.eventIndicator A) x ≤
      a+Real.exp (-(L:ℝ)*Real.log r+(t:ℝ)*(r-1))+
        Real.exp (-(U:ℝ)*Real.log s+(t:ℝ)*(s-1)) := by
  have hs0 : 0 < s := by linarith
  have hb (n) : P.steps n (FiniteKernel.eventIndicator A) x ≤
      a+Real.exp (-(L:ℝ)*Real.log r)*r^n+Real.exp (-(U:ℝ)*Real.log s)*s^n := by
    by_cases hl : L ≤ n
    · by_cases hu : n ≤ U
      · exact (h n hl hu).trans ((le_add_of_nonneg_right (by positivity)).trans
          (le_add_of_nonneg_right (by positivity)))
      · have hnr : (U:ℝ) ≤ n := by exact_mod_cast (le_of_lt (Nat.lt_of_not_ge hu))
        have hlog : 0 ≤ Real.log s := Real.log_nonneg hs
        have he : 1 ≤ Real.exp (-(U:ℝ)*Real.log s)*s^n := by
          rw [show s^n=Real.exp ((n:ℝ)*Real.log s) by rw [Real.exp_nat_mul,Real.exp_log hs0],← Real.exp_add]
          apply Real.one_le_exp_iff.mpr
          nlinarith
        have hp := (P.event_probability_bounds A n x).2
        have hz : 0 ≤ Real.exp (-(L:ℝ)*Real.log r)*r^n := by positivity
        linarith
    · have hnr : (n:ℝ) ≤ L := by exact_mod_cast (le_of_lt (Nat.lt_of_not_ge hl))
      have hlog : Real.log r ≤ 0 := Real.log_nonpos hr.le hr1
      have he : 1 ≤ Real.exp (-(L:ℝ)*Real.log r)*r^n := by
        rw [show r^n=Real.exp ((n:ℝ)*Real.log r) by rw [Real.exp_nat_mul,Real.exp_log hr],← Real.exp_add]
        apply Real.one_le_exp_iff.mpr
        nlinarith
      have hp := (P.event_probability_bounds A n x).2
      have hz : 0 ≤ Real.exp (-(U:ℝ)*Real.log s)*s^n := by positivity
      linarith
  have hsum : HasSum (fun n => poissonWeight t n*(a+
      Real.exp (-(L:ℝ)*Real.log r)*r^n+Real.exp (-(U:ℝ)*Real.log s)*s^n))
      (a+Real.exp (-(L:ℝ)*Real.log r+(t:ℝ)*(r-1))+
        Real.exp (-(U:ℝ)*Real.log s+(t:ℝ)*(s-1))) := by
    convert (((poissonWeight_sum t).mul_right a).add
      ((poissonWeight_geometric t r).mul_left (Real.exp (-(L:ℝ)*Real.log r)))).add
      ((poissonWeight_geometric t s).mul_left (Real.exp (-(U:ℝ)*Real.log s))) using 1
    · funext n
      ring
    · rw [Real.exp_add,Real.exp_add]
      ring
  exact (Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hb n)
    (poissonWeight_nonneg t n)) (P.event_summable t A x) hsum.summable).trans_eq hsum.tsum_eq

end
end FiniteCopyReactor

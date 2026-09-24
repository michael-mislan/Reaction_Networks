import proofs.RandomViability.BindingPoissonDeadline

namespace FiniteCopyReactor
noncomputable section
open FiniteCopy Classical
open scoped NNReal

theorem poisson_bounded_sequence (t : ℝ≥0) (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n ∧ u n ≤ 1) :
    Summable (fun n => poissonWeight t n*u n) :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (poissonWeight_nonneg t n) (hu n).1)
    (fun n => mul_le_of_le_one_right (poissonWeight_nonneg t n) (hu n).2) (poissonWeight_sum t).summable

theorem poisson_sequence_cutoff (t : ℝ≥0) (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n ∧ u n ≤ 1)
    (N : ℕ) (a r : ℝ) (ha : 0 ≤ a) (hr : 0 < r) (hr1 : r ≤ 1)
    (h : ∀ n, N ≤ n → u n ≤ a) :
    (∑' n,poissonWeight t n*u n) ≤ a+Real.exp (-(N:ℝ)*Real.log r+(t:ℝ)*(r-1)) := by
  have hb (n) : u n ≤ a+Real.exp (-(N:ℝ)*Real.log r)*r^n := by
    by_cases hn : N ≤ n
    · exact (h n hn).trans (le_add_of_nonneg_right (by positivity))
    · have hnr : (n:ℝ) ≤ N := by exact_mod_cast (le_of_lt (Nat.lt_of_not_ge hn))
      have hl : Real.log r ≤ 0 := Real.log_nonpos hr.le hr1
      have he : 1 ≤ Real.exp (-(N:ℝ)*Real.log r)*r^n := by
        rw [show r^n=Real.exp ((n:ℝ)*Real.log r) by rw [Real.exp_nat_mul,Real.exp_log hr],← Real.exp_add]
        apply Real.one_le_exp_iff.mpr
        nlinarith
      linarith [(hu n).2]
  have hs : HasSum (fun n => poissonWeight t n*(a+Real.exp (-(N:ℝ)*Real.log r)*r^n))
      (a+Real.exp (-(N:ℝ)*Real.log r+(t:ℝ)*(r-1))) := by
    convert ((poissonWeight_sum t).mul_right a).add
      ((poissonWeight_geometric t r).mul_left (Real.exp (-(N:ℝ)*Real.log r))) using 1
    · funext n
      ring
    · rw [Real.exp_add]
      ring
  exact (Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hb n) (poissonWeight_nonneg t n))
    (poisson_bounded_sequence t u hu) hs.summable).trans_eq hs.tsum_eq

end
end FiniteCopyReactor

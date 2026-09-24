import proofs.FiniteCopyReactor.ThreeClockBound

namespace FiniteCopyReactor
noncomputable section
open FiniteCopy Classical
open scoped NNReal

theorem finite_three_clock_cutoff {α : Type*} [Fintype α] (P Q R : FiniteKernel α)
    (t u v : NNReal) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (N : ℕ) (a r : ℝ) (ha : 0 ≤ a) (hr : 0 < r) (hr1 : r ≤ 1) (x : α)
    (h : ∀ n m k, N ≤ n+m+k → P.steps n (Q.steps m (R.steps k f)) x ≤ a) :
    P.poissonized t (fun y => Q.poissonized u (fun z => R.poissonized v f z) y) x ≤
      a+Real.exp (-(N:ℝ)*Real.log r+((t:ℝ)+(u:ℝ)+(v:ℝ))*(r-1)) := by
  have hb (n m k) : P.steps n (Q.steps m (R.steps k f)) x ≤
      a+Real.exp (-(N:ℝ)*Real.log r)*r^(n+m+k) := by
    by_cases hn : N ≤ n+m+k
    · exact (h n m k hn).trans (le_add_of_nonneg_right (by positivity))
    · have hs : (n+m+k:ℝ) ≤ N := by exact_mod_cast (le_of_lt (Nat.lt_of_not_ge hn))
      have hl : Real.log r ≤ 0 := Real.log_nonpos hr.le hr1
      have he : 1 ≤ Real.exp (-(N:ℝ)*Real.log r)*r^(n+m+k) := by
        rw [show r^(n+m+k)=Real.exp (((n+m+k:ℕ):ℝ)*Real.log r) by rw [Real.exp_nat_mul,Real.exp_log hr],← Real.exp_add]
        apply Real.one_le_exp_iff.mpr
        push_cast
        nlinarith
      have h1 : P.steps n (Q.steps m (R.steps k f)) x ≤ 1 :=
        P.steps_le_one n (fun y => Q.steps_le_one m (fun z => R.steps_le_one k (fun w => (hf w).2) z) y) x
      linarith
  have hh := finite_three_clock_geometric P Q R t u v f hf a (Real.exp (-(N:ℝ)*Real.log r)) r x hb
  simpa only [← Real.exp_add] using hh

end
end FiniteCopyReactor

import proofs.FiniteCopy.FiniteKernel

namespace FiniteCopy
open scoped NNReal

noncomputable def poissonWeight (t : ℝ≥0) (n : ℕ) : ℝ :=
  Real.exp (-(t : ℝ))*(t : ℝ)^n/(n.factorial : ℝ)

theorem poissonWeight_nonneg (t : ℝ≥0) (n : ℕ) : 0 ≤ poissonWeight t n := by
  unfold poissonWeight
  positivity

theorem poissonWeight_sum (t : ℝ≥0) : HasSum (poissonWeight t) 1 :=
  ProbabilityTheory.hasSum_one_poissonMeasure t

theorem poissonWeight_mean (t : ℝ≥0) :
    HasSum (fun n : ℕ => (n : ℝ)*poissonWeight t n) (t : ℝ) := by
  have he (n : ℕ) : ((n+1 : ℕ) : ℝ)*poissonWeight t (n+1) =
      (t : ℝ)*poissonWeight t n := by
    unfold poissonWeight
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    have hn : (n : ℝ)+1 ≠ 0 := by positivity
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  have hs : HasSum (fun n => ((n+1 : ℕ) : ℝ)*poissonWeight t (n+1)) (t : ℝ) := by
    simp_rw [he]
    simpa using (poissonWeight_sum t).mul_left (t : ℝ)
  have h := (hasSum_nat_add_iff (f := fun n : ℕ => (n : ℝ)*poissonWeight t n) 1).mp hs
  simpa only [Finset.sum_range_one, Nat.cast_zero, zero_mul, add_zero] using h

theorem poissonWeight_geometric (t : ℝ≥0) (r : ℝ) :
    HasSum (fun n => poissonWeight t n*r^n) (Real.exp ((t : ℝ)*(r-1))) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp ((t : ℝ)*r)).mul_left
    (Real.exp (-(t : ℝ)))
  convert h using 1
  · funext n
    simp only [poissonWeight, mul_pow]
    ring
  · rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]
    congr 1
    ring

namespace FiniteKernel
variable {α : Type*} [Fintype α] (P : FiniteKernel α)

noncomputable def poissonized (t : ℝ≥0) (f : α → ℝ) (x : α) : ℝ :=
  ∑' n, poissonWeight t n*P.steps n f x

theorem event_summable (t : ℝ≥0) (A : Set α) (x : α) :
    Summable (fun n => poissonWeight t n*P.steps n (eventIndicator A) x) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (poissonWeight_nonneg t n) (P.event_probability_bounds A n x).1)
    (fun n => ?_) (poissonWeight_sum t).summable
  exact mul_le_of_le_one_right (poissonWeight_nonneg t n) (P.event_probability_bounds A n x).2

theorem poissonized_event_bounds (t : ℝ≥0) (A : Set α) (x : α) :
    0 ≤ P.poissonized t (eventIndicator A) x ∧ P.poissonized t (eventIndicator A) x ≤ 1 := by
  constructor
  · exact tsum_nonneg (fun n => mul_nonneg (poissonWeight_nonneg t n)
      (P.event_probability_bounds A n x).1)
  · rw [← (poissonWeight_sum t).tsum_eq]
    exact Summable.tsum_le_tsum (fun n => mul_le_of_le_one_right (poissonWeight_nonneg t n)
      (P.event_probability_bounds A n x).2) (P.event_summable t A x) (poissonWeight_sum t).summable

/-- The finite generator drift bound implies a continuous-time event bound for
the actual Poisson mixture, without an assumed Dynkin or stopping theorem. -/
theorem poissonized_event_drift_bound (t : ℝ≥0) (A : Set α) (V : α → ℝ) (a b : ℝ)
    (hV : ∀ x, 0 ≤ V x) (hA : ∀ x ∈ A, a ≤ V x)
    (h : ∀ x, P.step V x ≤ V x+b) (x : α) :
    a*P.poissonized t (eventIndicator A) x ≤ V x+(t : ℝ)*b := by
  have hsR : HasSum (fun n => poissonWeight t n*(V x+(n : ℝ)*b)) (V x+(t : ℝ)*b) := by
    convert ((poissonWeight_sum t).mul_right (V x)).add ((poissonWeight_mean t).mul_right b) using 1
    · funext n; ring
    · ring
  have hsL : Summable (fun n => poissonWeight t n*(a*P.steps n (eventIndicator A) x)) := by
    convert (P.event_summable t A x).mul_left a using 1
    funext n; ring
  calc
    a*P.poissonized t (eventIndicator A) x =
        ∑' n, poissonWeight t n*(a*P.steps n (eventIndicator A) x) := by
      rw [poissonized, ← tsum_mul_left]
      congr 1
      funext n; ring
    _ ≤ ∑' n, poissonWeight t n*(V x+(n : ℝ)*b) :=
      Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left
        (P.event_drift_bound A V a b hV hA h n x) (poissonWeight_nonneg t n)) hsL hsR.summable
    _ = V x+(t : ℝ)*b := hsR.tsum_eq

theorem poissonized_decay_bound (t : ℝ≥0) (W : α → ℝ) (hW : ∀ x, 0 ≤ W x)
    (r : ℝ) (hr : 0 ≤ r) (h : ∀ x, P.step W x ≤ r*W x) (x : α) :
    P.poissonized t W x ≤ Real.exp ((t : ℝ)*(r-1))*W x := by
  have hsR : HasSum (fun n => poissonWeight t n*(r^n*W x))
      (Real.exp ((t : ℝ)*(r-1))*W x) := by
    convert (poissonWeight_geometric t r).mul_right (W x) using 1
    funext n; ring
  have hm (n : ℕ) : poissonWeight t n*P.steps n W x ≤ poissonWeight t n*(r^n*W x) :=
    mul_le_mul_of_nonneg_left (P.steps_decay_bound W r hr h n x) (poissonWeight_nonneg t n)
  have hsL : Summable (fun n => poissonWeight t n*P.steps n W x) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (poissonWeight_nonneg t n)
      (P.steps_nonneg n hW x)) hm hsR.summable
  exact (Summable.tsum_le_tsum hm hsL hsR.summable).trans_eq hsR.tsum_eq

end FiniteKernel
end FiniteCopy

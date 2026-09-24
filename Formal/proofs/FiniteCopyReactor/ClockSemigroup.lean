import proofs.FiniteCopyReactor.ClockEndpoint
import Mathlib.Probability.Distributions.Poisson.Basic

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability FiniteCopy
open scoped ENNReal BigOperators

variable {α β : Type*} [Fintype β]

theorem tick_value_add (P : MarkedKernel α β) (n m : ℕ) (f : α → ℝ≥0∞) (x : α) :
    tickValue P (n+m) f x=tickValue P n (fun y => tickValue P m f y) x := by
  induction n generalizing x with
  | zero => simp only [Nat.zero_add,tickValue]
  | succ n ih =>
    simp only [Nat.succ_add,tickValue,ih]

theorem tick_value_lintegral (P : MarkedKernel α β) (n : ℕ) (μ : Measure ℕ)
    (g : ℕ → α → ℝ≥0∞) (x : α) :
    tickValue P n (fun y => ∫⁻ k,g k y ∂μ) x=∫⁻ k,tickValue P n (g k) x ∂μ := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [tickValue,ih]
    rw [lintegral_finsetSum Finset.univ (fun _ _ => measurable_of_countable _)]
    apply Finset.sum_congr rfl
    intro b _
    exact (lintegral_const_mul _ (measurable_of_countable _)).symm

theorem clock_endpoint_poisson (P : MarkedKernel α β) (q t : NNReal) (f : α → ℝ≥0∞) (x : α) :
    clockEndpoint P q t f x=∫⁻ n,tickValue P n f x ∂poissonMeasure (q*t) := by
  rw [lintegral_countable']
  unfold clockEndpoint
  apply tsum_congr
  intro n
  rw [poissonMeasure_singleton,clockWeight_eq_poisson]
  simp only [poissonWeight]
  exact mul_comm _ _

theorem clock_endpoint_lintegral (P : MarkedKernel α β) (q t : NNReal) (μ : Measure ℕ)
    [SFinite μ] (g : ℕ → α → ℝ≥0∞) (x : α) :
    clockEndpoint P q t (fun y => ∫⁻ k,g k y ∂μ) x=
      ∫⁻ k,clockEndpoint P q t (g k) x ∂μ := by
  simp_rw [clock_endpoint_poisson,tick_value_lintegral]
  exact lintegral_lintegral_swap (measurable_of_countable _).aemeasurable

/-- Splitting a homogeneous bounded clock at a fixed physical time preserves its law. -/
theorem clock_endpoint_semigroup (P : MarkedKernel α β) (q t u : NNReal)
    (f : α → ℝ≥0∞) (x : α) :
    clockEndpoint P q (t+u) f x=
      clockEndpoint P q t (fun y => clockEndpoint P q u f y) x := by
  change clockEndpoint P q ((t+u:NNReal):ℝ) f x = _
  rw [clock_endpoint_poisson P q (t+u) f x]
  rw [mul_add,← poissonMeasure_conv_poissonMeasure,Measure.lintegral_conv (measurable_of_countable _)]
  simp_rw [tick_value_add]
  have hi : (fun y => clockEndpoint P q u f y)=(fun y => ∫⁻ m,tickValue P m f y ∂poissonMeasure (q*u)) := by
    funext y
    exact clock_endpoint_poisson P q u f y
  rw [hi,clock_endpoint_poisson]
  simp_rw [tick_value_lintegral]

end
end FiniteCopyReactor

import proofs.CompositionalMemory.BinomialAllocationMeasure
import proofs.CompositionalMemory.PoissonAllocationMoments
import Mathlib.MeasureTheory.Integral.Prod

namespace CompositionalMemory
open MeasureTheory ProbabilityTheory FiniteCopy

noncomputable def binomialCentralMoment (n p : ℕ) : ℝ :=
  match p with
  | 0 => 1
  | 1 => 0
  | 2 => n/4
  | 3 => 0
  | 4 => (3*(n : ℝ)^2-2*n)/16
  | _ => 0

noncomputable def poissonCentralMoment (t : NNReal) (p : ℕ) : ℝ :=
  match p with
  | 0 => 1
  | 1 => 0
  | 2 => t
  | 3 => t
  | 4 => 3*(t : ℝ)^2+t
  | _ => 0

theorem binomial_integral_power (n p : ℕ) (hp : p ≤ 4) :
    (∫ k,((k : ℝ)-(n : ℝ)/2)^p ∂fairAllocationMeasure n)=binomialCentralMoment n p := by
  have hm := binomial_actual_centered_moments n
  interval_cases p
  · simp [binomialCentralMoment]
  · simpa [binomialCentralMoment] using hm.1
  · exact hm.2.1
  · exact hm.2.2.1
  · exact hm.2.2.2

theorem poisson_hasSum_power (t : NNReal) (p : ℕ) (hp : p ≤ 4) :
    HasSum (fun k : ℕ => ((k : ℝ)-t)^p*poissonWeight t k) (poissonCentralMoment t p) := by
  interval_cases p
  · simpa [poissonCentralMoment] using poissonWeight_sum t
  · simpa [poissonCentralMoment] using poisson_centered_mean t
  · exact poisson_centered_second t
  · exact poisson_centered_third t
  · exact poisson_centered_fourth t

noncomputable def refillAllocationMeasure (n : ℕ) (t : NNReal) : Measure (ℕ × ℕ) :=
  (fairAllocationMeasure n).prod (poissonMeasure t)

noncomputable def refillCentered (n : ℕ) (t : NNReal) (z : ℕ × ℕ) : ℝ :=
  ((z.1 : ℝ)-(n : ℝ)/2)+((z.2 : ℝ)-t)

theorem refill_power_integrable (n : ℕ) (t : NNReal) (p : ℕ) (hp : p ≤ 4) :
    Integrable (fun z => refillCentered n t z^p) (refillAllocationMeasure n t) := by
  unfold refillCentered refillAllocationMeasure
  simp_rw [add_pow]
  apply integrable_finsetSum
  intro k hk
  have hi := (fairAllocationMeasure_integrable n (fun x => ((x : ℝ)-(n : ℝ)/2)^k)).mul_prod
    (poisson_integrable_of_hasSum t _ _ (poisson_hasSum_power t (p-k) (by omega)))
  exact hi.mul_const (p.choose k : ℝ)

theorem refill_integral_power (n : ℕ) (t : NNReal) (p : ℕ) (hp : p ≤ 4) :
    (∫ z,refillCentered n t z^p ∂refillAllocationMeasure n t)=
      ∑ k ∈ Finset.range (p+1),binomialCentralMoment n k*poissonCentralMoment t (p-k)*(p.choose k : ℝ) := by
  unfold refillCentered refillAllocationMeasure
  simp_rw [add_pow]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [integral_mul_const,integral_prod_mul (fun a : ℕ => ((a : ℝ)-(n : ℝ)/2)^k)
      (fun b : ℕ => ((b : ℝ)-t)^(p-k)),binomial_integral_power n k (by simp only [Finset.mem_range] at hk; omega),
      poisson_integral_of_hasSum t _ _ (poisson_hasSum_power t (p-k) (by omega))]
  · intro k hk
    exact ((fairAllocationMeasure_integrable n (fun x => ((x : ℝ)-(n : ℝ)/2)^k)).mul_prod
      (poisson_integrable_of_hasSum t _ _ (poisson_hasSum_power t (p-k) (by omega)))).mul_const _

/-- These are moments of an actual binomial partition followed by independent
Poisson refill for one species; no relation between different species is used. -/
theorem refill_actual_moments (n : ℕ) (t : NNReal) :
    (∫ z,refillCentered n t z ∂refillAllocationMeasure n t)=0 ∧
    (∫ z,refillCentered n t z^2 ∂refillAllocationMeasure n t)=(n : ℝ)/4+t ∧
    (∫ z,refillCentered n t z^4 ∂refillAllocationMeasure n t)=
      3*((n : ℝ)/4+t)^2+t-(n : ℝ)/8 := by
  have h1 := refill_integral_power n t 1 (by omega)
  have h2 := refill_integral_power n t 2 (by omega)
  have h4 := refill_integral_power n t 4 (by omega)
  norm_num [Finset.sum_range_succ,binomialCentralMoment,poissonCentralMoment,Nat.choose] at h1 h2 h4
  refine ⟨h1,by simpa only [add_comm] using h2,?_⟩
  rw [h4]
  ring

end CompositionalMemory

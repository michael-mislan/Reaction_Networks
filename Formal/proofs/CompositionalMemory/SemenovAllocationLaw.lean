import proofs.CompositionalMemory.RefilledAllocationMoments
import proofs.CompositionalMemory.MarginalNoiseMoments
import Mathlib.MeasureTheory.Integral.Pi

namespace CompositionalMemory.Semenov
open MeasureTheory ProbabilityTheory

abbrev RawAllocation := Fin 8 → ℕ × ℕ

instance refillAllocation_probability (n : ℕ) (t : NNReal) :
    IsProbabilityMeasure (refillAllocationMeasure n t) := by
  unfold refillAllocationMeasure
  infer_instance

/-- A concrete raw daughter law: fair partition and Poisson replenishment,
independent over coordinates. Subsequent bounds use only its marginals. -/
noncomputable def allocationLaw (n : Fin 8 → ℕ) (t : Fin 8 → NNReal) : Measure RawAllocation :=
  Measure.pi (fun j => refillAllocationMeasure (n j) (t j))

instance allocationLaw_probability (n : Fin 8 → ℕ) (t : Fin 8 → NNReal) :
    IsProbabilityMeasure (allocationLaw n t) := by
  unfold allocationLaw
  infer_instance

noncomputable def allocationNoise (n : Fin 8 → ℕ) (t : Fin 8 → NNReal)
    (j : Fin 8) (z : RawAllocation) : ℝ := refillCentered (n j) (t j) (z j)

def refilledCounts (z : RawAllocation) (j : Fin 8) : ℕ := (z j).1+(z j).2

theorem allocationNoise_count_identity (n : Fin 8 → ℕ) (t : Fin 8 → NNReal)
    (j : Fin 8) (z : RawAllocation) :
    allocationNoise n t j z=(refilledCounts z j : ℝ)-((n j : ℝ)/2+t j) := by
  simp only [allocationNoise,refillCentered,refilledCounts,Nat.cast_add]
  ring

theorem allocation_noise_integrable (n : Fin 8 → ℕ) (t : Fin 8 → NNReal)
    (j : Fin 8) (p : ℕ) (hp : p ≤ 4) :
    Integrable (fun z => allocationNoise n t j z^p) (allocationLaw n t) := by
  exact integrable_comp_eval (μ := fun j => refillAllocationMeasure (n j) (t j)) (i := j)
    (refill_power_integrable (n j) (t j) p hp)

theorem allocation_noise_moment (n : Fin 8 → ℕ) (t : Fin 8 → NNReal)
    (j : Fin 8) (p : ℕ) (hp : p ≤ 4) :
    (∫ z,allocationNoise n t j z^p ∂allocationLaw n t)=
      ∫ z,refillCentered (n j) (t j) z^p ∂refillAllocationMeasure (n j) (t j) := by
  exact integral_comp_eval (μ := fun j => refillAllocationMeasure (n j) (t j)) (i := j)
    (refill_power_integrable (n j) (t j) p hp).aestronglyMeasurable

theorem allocation_noise_moments (n : Fin 8 → ℕ) (t : Fin 8 → NNReal) (j : Fin 8) :
    (∫ z,allocationNoise n t j z ∂allocationLaw n t)=0 ∧
    (∫ z,allocationNoise n t j z^2 ∂allocationLaw n t)=(n j : ℝ)/4+t j ∧
    (∫ z,allocationNoise n t j z^4 ∂allocationLaw n t) ≤
      3*((n j : ℝ)/4+t j)^2+((n j : ℝ)/4+t j) := by
  have h1 := allocation_noise_moment n t j 1 (by omega)
  have h2 := allocation_noise_moment n t j 2 (by omega)
  have h4 := allocation_noise_moment n t j 4 (by omega)
  have hm := refill_actual_moments (n j) (t j)
  simp only [pow_one] at h1
  refine ⟨h1.trans hm.1,h2.trans hm.2.1,?_⟩
  rw [h4,hm.2.2]
  have hn : (0 : ℝ) ≤ n j := Nat.cast_nonneg _
  linarith only [hn]

/-- Initial quadratic noise moments now follow from the concrete offspring
measure, with no assumed variance or fourth-moment premises. -/
theorem allocation_quadratic_moments (n : Fin 8 → ℕ) (t : Fin 8 → NNReal)
    (Q : RawAllocation → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hQ : AEStronglyMeasurable Q (allocationLaw n t))
    (hpoint : ∀ z,0 ≤ Q z ∧ Q z ≤ C*∑ j,allocationNoise n t j z^2) :
    Integrable Q (allocationLaw n t) ∧ Integrable (fun z => Q z^2) (allocationLaw n t) ∧
    (∫ z,Q z ∂allocationLaw n t) ≤ C*∑ j,((n j : ℝ)/4+t j) ∧
    (∫ z,Q z^2 ∂allocationLaw n t) ≤
      C^2*8*(3*(∑ j,((n j : ℝ)/4+t j))^2+∑ j,((n j : ℝ)/4+t j)) := by
  apply marginal_quadratic_moments (allocationLaw n t) (allocationNoise n t) Q C
    (fun j => (n j : ℝ)/4+t j) hC (fun j => by positivity) hQ hpoint
  · intro j
    exact allocation_noise_integrable n t j 2 (by omega)
  · intro j
    exact allocation_noise_integrable n t j 4 (by omega)
  · intro j
    exact (allocation_noise_moments n t j).2.1.le
  · intro j
    exact (allocation_noise_moments n t j).2.2

end CompositionalMemory.Semenov

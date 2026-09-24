import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace CompositionalMemory
open MeasureTheory

theorem coordinate_fourth_bound {N : ℕ} (z : Fin N → ℝ) :
    (∑ i,z i^2)^2 ≤ (N : ℝ)*∑ i,z i^4 := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin N => (1 : ℝ)) (fun i => z i^2)
  simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,← pow_mul] using hh

/-- Marginal fourth moments suffice. No independence or zero covariance
between different chemical species is assumed. -/
theorem marginal_quadratic_moments {α : Type*} [MeasurableSpace α] {N : ℕ}
    (μ : Measure α) (X : Fin N → α → ℝ) (Q : α → ℝ) (C : ℝ) (v : Fin N → ℝ)
    (hC : 0 ≤ C) (hv : ∀ i,0 ≤ v i) (hQ : AEStronglyMeasurable Q μ)
    (hpoint : ∀ z,0 ≤ Q z ∧ Q z ≤ C*∑ i,X i z^2)
    (hi2 : ∀ i,Integrable (fun z => X i z^2) μ)
    (hi4 : ∀ i,Integrable (fun z => X i z^4) μ)
    (hm2 : ∀ i,(∫ z,X i z^2 ∂μ) ≤ v i)
    (hm4 : ∀ i,(∫ z,X i z^4 ∂μ) ≤ 3*(v i)^2+v i) :
    Integrable Q μ ∧ Integrable (fun z => Q z^2) μ ∧
    (∫ z,Q z ∂μ) ≤ C*∑ i,v i ∧
    (∫ z,Q z^2 ∂μ) ≤ C^2*(N : ℝ)*(3*(∑ i,v i)^2+∑ i,v i) := by
  have hS2 := integrable_finsetSum Finset.univ (fun i _ => hi2 i)
  have hS4 := integrable_finsetSum Finset.univ (fun i _ => hi4 i)
  have hB2 : Integrable (fun z => C*∑ i,X i z^2) μ := hS2.const_mul C
  have hB4 : Integrable (fun z => (C^2*(N : ℝ))*∑ i,X i z^4) μ := hS4.const_mul _
  have hpoint2 (z : α) : Q z^2 ≤ (C^2*(N : ℝ))*∑ i,X i z^4 := by
    have hsq := pow_le_pow_left₀ (hpoint z).1 (hpoint z).2 2
    have hs := mul_le_mul_of_nonneg_left (coordinate_fourth_bound (fun i => X i z)) (sq_nonneg C)
    nlinarith only [hsq,hs]
  have hiQ : Integrable Q μ := hB2.mono_nonneg hQ
    (Filter.Eventually.of_forall (fun z => (hpoint z).1))
    (Filter.Eventually.of_forall (fun z => (hpoint z).2))
  have hmQ2 : AEStronglyMeasurable (fun z => Q z^2) μ := by
    simpa only [pow_two] using hQ.mul hQ
  have hiQ2 := hB4.mono_nonneg hmQ2 (Filter.Eventually.of_forall (fun z => sq_nonneg (Q z)))
    (Filter.Eventually.of_forall hpoint2)
  refine ⟨hiQ,hiQ2,?_,?_⟩
  · calc
      _ ≤ ∫ z,C*∑ i,X i z^2 ∂μ := integral_mono hiQ hB2 (fun z => (hpoint z).2)
      _ = C*∑ i,(∫ z,X i z^2 ∂μ) := by rw [integral_const_mul,integral_finsetSum _ (fun i _ => hi2 i)]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hm2 i)) hC
  · have hsum : (∑ i,(∫ z,X i z^4 ∂μ)) ≤ 3*(∑ i,v i)^2+∑ i,v i := by
      have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hm4 i)
      rw [Finset.sum_add_distrib,← Finset.mul_sum] at hh
      have hs := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (fun i _ => hv i)
      linarith only [hh,hs]
    calc
      _ ≤ ∫ z,(C^2*(N : ℝ))*∑ i,X i z^4 ∂μ := integral_mono hiQ2 hB4 hpoint2
      _ = (C^2*(N : ℝ))*∑ i,(∫ z,X i z^4 ∂μ) := by rw [integral_const_mul,integral_finsetSum _ (fun i _ => hi4 i)]
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

end CompositionalMemory

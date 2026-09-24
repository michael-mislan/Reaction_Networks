import proofs.CompositionalMemory.SemenovAllocationLaw
import proofs.CompositionalMemory.MatrixBilinearEnergy
import proofs.CompositionalMemory.SixthCapInitialExpectation

namespace CompositionalMemory.Semenov
open MeasureTheory Matrix Set

theorem allocation_linear_centered (n : Fin 8 → ℕ) (t : Fin 8 → NNReal) (a : Fin 8 → ℝ) :
    Integrable (fun z => ∑ j,a j*allocationNoise n t j z) (allocationLaw n t) ∧
    (∫ z,(∑ j,a j*allocationNoise n t j z) ∂allocationLaw n t)=0 := by
  have hi (j : Fin 8) : Integrable (allocationNoise n t j) (allocationLaw n t) := by
    simpa only [pow_one] using allocation_noise_integrable n t j 1 (by omega)
  constructor
  · exact integrable_finsetSum _ (fun j _ => (hi j).const_mul (a j))
  · rw [integral_finsetSum _ (fun j _ => (hi j).const_mul (a j))]
    simp only [integral_const_mul,(allocation_noise_moments n t _).1,mul_zero,Finset.sum_const_zero]

theorem allocation_bilinear_centered (n : Fin 8 → ℕ) (t : Fin 8 → NNReal)
    (P : Matrix (Fin 8) (Fin 8) ℝ) (base : Fin 8 → ℝ) (scale : ℝ) :
    Integrable (fun z => P.toBilin' base (fun j => allocationNoise n t j z)/scale) (allocationLaw n t) ∧
    (∫ z,P.toBilin' base (fun j => allocationNoise n t j z)/scale ∂allocationLaw n t)=0 := by
  have he (z : RawAllocation) : P.toBilin' base (fun j => allocationNoise n t j z)/scale=
      ∑ j,((∑ i,base i*P i j)/scale)*allocationNoise n t j z := by
    rw [Matrix.toBilin'_apply,Finset.sum_comm,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_mul]
    ring
  simp_rw [he]
  exact allocation_linear_centered n t (fun j => (∑ i,base i*P i j)/scale)

/-- Initial cap bound with all probabilistic moment hypotheses discharged
by the concrete partition/refill law. The remaining premises are deterministic
matrix and parent-region bounds. -/
theorem allocation_energy_initial_bound (n : Fin 8 → ℕ) (t : Fin 8 → NNReal)
    (P : Matrix (Fin 8) (Fin 8) ℝ) (base : Fin 8 → ℝ) (scale L : ℝ)
    (hscale : 0 < scale) (hL : 0 ≤ L) (hsym : ∀ i j,P i j=P j i)
    (hpos : ∀ x,0 ≤ matrixEnergy P x)
    (hupper : ∀ x,matrixEnergy P x ≤ L*vectorSquares x)
    (hu : matrixEnergy P base/scale ≤ 1) :
    (∫ z,smoothQuadraticCap ((matrixEnergy P (base+(fun j => allocationNoise n t j z))/scale)^6) ∂allocationLaw n t) ≤
      smoothQuadraticCap ((matrixEnergy P base/scale)^6)+
        (4+48*(matrixEnergy P base/scale))*(L/scale*∑ j,((n j : ℝ)/4+t j))+
        12*((L/scale)^2*8*(3*(∑ j,((n j : ℝ)/4+t j))^2+(∑ j,((n j : ℝ)/4+t j)))) := by
  let q : RawAllocation → ℝ := fun z => matrixEnergy P (fun j => allocationNoise n t j z)/scale
  let s : RawAllocation → ℝ := fun z => P.toBilin' base (fun j => allocationNoise n t j z)/scale
  let u := matrixEnergy P base/scale
  have hq : AEStronglyMeasurable q (allocationLaw n t) := (measurable_of_countable q).aestronglyMeasurable
  have hpoint (z : RawAllocation) : 0 ≤ q z ∧ q z ≤ (L/scale)*∑ j,allocationNoise n t j z^2 := by
    constructor
    · exact div_nonneg (hpos _) hscale.le
    · have hh := div_le_div_of_nonneg_right (hupper (fun j => allocationNoise n t j z)) hscale.le
      convert hh using 1
      unfold vectorSquares
      ring
  have hm := allocation_quadratic_moments n t q (L/scale) (div_nonneg hL hscale.le) hq hpoint
  have hs := allocation_bilinear_centered n t P base scale
  have hu0 : 0 ≤ u := div_nonneg (hpos base) hscale.le
  have he (z : RawAllocation) : u+2*s z+q z=matrixEnergy P (base+(fun j => allocationNoise n t j z))/scale := by
    rw [matrix_energy_add P hsym]
    dsimp [u,s,q]
    ring
  have hc (z : RawAllocation) : s z^2 ≤ u*q z := by
    have hh := div_le_div_of_nonneg_right (matrix_bilinear_cauchy P hsym hpos base (fun j => allocationNoise n t j z)) (sq_nonneg scale)
    dsimp [s,u,q]
    simpa only [div_pow,mul_div_mul_comm,pow_two] using hh
  have hh := sixth_cap_initial_expectation (allocationLaw n t) s q u _ _ ⟨hu0,hu⟩
    hs.1 hm.1 hm.2.1 hs.2 hm.2.2.1 hm.2.2.2 (by positivity)
    (fun z => by rw [he]; exact div_nonneg (hpos _) hscale.le) hc
  simp_rw [he] at hh
  exact hh

end CompositionalMemory.Semenov

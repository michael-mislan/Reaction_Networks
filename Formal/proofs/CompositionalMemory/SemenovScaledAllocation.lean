import proofs.CompositionalMemory.SemenovAllocationEnergy
import proofs.CompositionalMemory.SemenovAllocationCap

namespace CompositionalMemory.Semenov
open MeasureTheory Matrix

theorem matrix_energy_smul {N : ℕ} (P : Matrix (Fin N) (Fin N) ℝ) (c : ℝ) (v : Fin N → ℝ) :
    matrixEnergy P (c • v)=c^2*matrixEnergy P v := by
  simp only [matrixEnergy_toBilin,map_smul,LinearMap.smul_apply,smul_eq_mul]
  ring

noncomputable def allocationBase (n : Fin 8 → ℕ) (t : Fin 8 → NNReal)
    (volume : ℝ) (center : Fin 8 → ℝ) : Fin 8 → ℝ :=
  fun j => (n j : ℝ)/2+t j-volume*center j

theorem allocation_concentration_energy (n : Fin 8 → ℕ) (t : Fin 8 → NNReal)
    (P : Matrix (Fin 8) (Fin 8) ℝ) (center : Fin 8 → ℝ) (volume eta : ℝ)
    (hv : volume ≠ 0) (he : eta ≠ 0) (z : RawAllocation) :
    matrixEnergy P ((fun j => (refilledCounts z j : ℝ)/volume)-center)/eta=
      matrixEnergy P (allocationBase n t volume center+(fun j => allocationNoise n t j z))/(volume^2*eta) := by
  have hh : ((fun j => (refilledCounts z j : ℝ)/volume)-center)=
      (1/volume) • (allocationBase n t volume center+(fun j => allocationNoise n t j z)) := by
    funext j
    simp only [Pi.sub_apply,Pi.smul_apply,Pi.add_apply,smul_eq_mul,allocationBase,allocationNoise_count_identity]
    field_simp
    ring
  rw [hh,matrix_energy_smul]
  field_simp

theorem allocation_base_refill_identity (n : Fin 8 → ℕ) (t : Fin 8 → NNReal)
    (volume : ℝ) (hv : volume ≠ 0) (initial parent feed : Fin 8 → ℝ)
    (ht : ∀ j,(t j : ℝ)=volume*feed j/2) (hz : ∀ j,initial j=(parent j+feed j)/2) :
    allocationBase n t volume initial=
      volume • ((1/2 : ℝ) • ((fun j => (n j : ℝ)/volume)-parent)) := by
  funext j
  simp only [allocationBase,Pi.smul_apply,Pi.sub_apply,smul_eq_mul,ht,hz]
  field_simp
  ring

theorem allocation_energy_uniform_bound (n : Fin 8 → ℕ) (t : Fin 8 → NNReal)
    (P : Matrix (Fin 8) (Fin 8) ℝ) (base : Fin 8 → ℝ) (scale L r m1 m2 : ℝ)
    (hscale : 0 < scale) (hL : 0 ≤ L) (hsym : ∀ i j,P i j=P j i)
    (hpos : ∀ x,0 ≤ matrixEnergy P x)
    (hupper : ∀ x,matrixEnergy P x ≤ L*vectorSquares x)
    (hu : matrixEnergy P base/scale ≤ r) (hr : r ≤ 1)
    (hm1 : L/scale*(∑ j,((n j : ℝ)/4+t j)) ≤ m1)
    (hm2 : (L/scale)^2*8*(3*(∑ j,((n j : ℝ)/4+t j))^2+
      (∑ j,((n j : ℝ)/4+t j))) ≤ m2) :
    (∫ z,smoothQuadraticCap ((matrixEnergy P (base+(fun j => allocationNoise n t j z))/scale)^6) ∂allocationLaw n t) ≤
      smoothQuadraticCap (r^6)+(4+48*r)*m1+12*m2 := by
  have hu0 : 0 ≤ matrixEnergy P base/scale := div_nonneg (hpos _) hscale.le
  have hv0 : 0 ≤ L/scale*(∑ j,((n j : ℝ)/4+t j)) := by positivity
  have hcap := smooth_cap_monotone (pow_le_pow_left₀ hu0 hu 6)
  have hprod : (4+48*(matrixEnergy P base/scale))*(L/scale*∑ j,((n j : ℝ)/4+t j)) ≤
      (4+48*r)*m1 :=
    mul_le_mul (by linarith only [hu]) hm1 hv0 (by linarith only [hu0,hu])
  have hh := allocation_energy_initial_bound n t P base scale L hscale hL hsym hpos hupper (hu.trans hr)
  exact hh.trans (add_le_add (add_le_add hcap hprod) (mul_le_mul_of_nonneg_left hm2 (by norm_num)))

end CompositionalMemory.Semenov

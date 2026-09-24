import proofs.CompositionalMemory.CoupledCounts

namespace CompositionalMemory
open FiniteCopy

noncomputable def localMoleculeCount (n : Counts) : ℝ := ∑ a, (n a : ℝ)

theorem local_molecule_increment (n : Counts) (r : Fin 13) (hr : reactants n r) :
    localMoleculeCount (nextCounts n r)-localMoleculeCount n = ∑ a, jump r a := by
  unfold localMoleculeCount
  simp_rw [nextCounts_cast n r hr]
  rw [Finset.sum_add_distrib]
  ring

theorem local_molecule_rate_increment (v : ℝ) (n : Counts) (r : Fin 13) :
    v*densityRates (1/100000) (1/v) (effectiveConcentration v n) r*
      (localMoleculeCount (nextCounts n r)-localMoleculeCount n) =
    v*densityRates (1/100000) (1/v) (effectiveConcentration v n) r*(∑ a, jump r a) := by
  by_cases hr : reactants n r
  · rw [local_molecule_increment n r hr]
  · rw [effective_disabled_density (1/100000) v n r hr]
    simp

theorem local_count_growth (v : ℝ) (hv : 0 < v) (n : Counts) :
    (∑ r : Fin 13, v*densityRates (1/100000) (1/v) (effectiveConcentration v n) r*
      (localMoleculeCount (nextCounts n r)-localMoleculeCount n)) ≤
        33*v+localMoleculeCount n := by
  let ρ := densityRates (1/100000) (1/v) (effectiveConcentration v n)
  have hρ (r) : 0 ≤ ρ r := effective_rates_nonneg _ (by norm_num) _ hv.le n r
  simp_rw [local_molecule_rate_increment]
  have he : (∑ r : Fin 13, ρ r*(∑ a, jump r a)) =
      ρ 0-ρ 1+ρ 4-ρ 5+ρ 6-ρ 7+ρ 8-ρ 9+ρ 10-ρ 11-ρ 12 := by
    norm_num [Fin.sum_univ_succ,jump]
    change (ρ 0+(-ρ 1+(ρ 4+(-ρ 5+(ρ 6+(-ρ 7+(ρ 8+(-ρ 9+(ρ 10+(-ρ 11+-ρ 12)))))))))) = _
    ring
  have hsum : (∑ r : Fin 13, ρ r*(∑ a, jump r a)) ≤ ρ 0+ρ 4+ρ 6+ρ 8+ρ 10 := by
    rw [he]
    linarith only [hρ 1,hρ 5,hρ 7,hρ 9,hρ 11,hρ 12]
  have hpos : v*(ρ 0+ρ 4+ρ 6+ρ 8+ρ 10) =
      (n 0 : ℝ)+(n 3 : ℝ)+33*v+(n 1 : ℝ)/100000 := by
    dsimp [ρ,densityRates,effectiveConcentration]
    field_simp
    ring
  have hbound : v*(ρ 0+ρ 4+ρ 6+ρ 8+ρ 10) ≤ 33*v+localMoleculeCount n := by
    rw [hpos]
    norm_num [localMoleculeCount,Fin.sum_univ_succ]
    change (n 0 : ℝ)+(n 3 : ℝ)+33*v+(n 1 : ℝ)/100000 ≤
      33*v+((n 0 : ℝ)+((n 1 : ℝ)+((n 2 : ℝ)+(n 3 : ℝ))))
    linarith only [(show (0 : ℝ) ≤ (n 1 : ℝ) from Nat.cast_nonneg _),
      (show (0 : ℝ) ≤ (n 2 : ℝ) from Nat.cast_nonneg _)]
  have h := (mul_le_mul_of_nonneg_left hsum hv.le).trans hbound
  convert h using 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

end CompositionalMemory

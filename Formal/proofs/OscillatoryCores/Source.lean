import proofs.DUnstableCores.ClassicalMassAction.Rate

namespace OscillatoryCores

open DUnstableCores
open scoped BigOperators

def source : SourceNetwork (Fin 4) (Fin 5) where
  reactant := !![1, 0, 0, 0, 0; 0, 4, 0, 0, 0;
                 0, 2, 375, 0, 0; 400, 0, 0, 2, 0]
  product := !![0, 0, 0, 1, 0; 0, 0, 0, 6, 0;
                4, 0, 371, 1, 2; 398, 0, 2, 0, 2]
  catalyst := 0
  catalyst_le_reactant := by intros; simp
  catalyst_le_product := by intros; simp

def flux : Fin 5 → ℝ := ![2, 3, 2, 2, 2]

theorem flux_pos (r : Fin 5) : 0 < flux r := by
  fin_cases r <;> norm_num [flux]

theorem stoich_eq_base : source.stoich = classicalBaseCounterexampleSource.stoich := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [source, classicalBaseCounterexampleSource, SourceNetwork.stoich]

theorem reactant_iff_base (i : Fin 4) (j : Fin 5) :
    source.Reactant i j ↔ classicalBaseCounterexampleSource.Reactant i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [source, classicalBaseCounterexampleSource, SourceNetwork.Reactant]

theorem balanced (i : Fin 4) : ∑ j, (source.stoich i j : ℝ) * flux j = 0 := by
  fin_cases i <;> norm_num [source, SourceNetwork.stoich, flux, Fin.sum_univ_succ]

noncomputable def equilibrium (t : ℝ) : Fin 4 → ℝ := ![2, 600, 1500, 8 / t]

theorem equilibrium_pos {t : ℝ} (ht : 0 < t) (i : Fin 4) :
    0 < equilibrium t i := by
  fin_cases i <;> norm_num [equilibrium]
  positivity

noncomputable def rates (t : ℝ) : Fin 5 → ℝ :=
  reconstructedRate source (equilibrium t) flux

theorem rates_pos {t : ℝ} (ht : 0 < t) (j : Fin 5) : 0 < rates t j :=
  reconstructedRate_pos source (equilibrium t) flux (equilibrium_pos ht) flux_pos j

theorem equilibrium_flux {t : ℝ} (ht : 0 < t) (j : Fin 5) :
    rates t j * massActionMonomial source (equilibrium t) j = flux j :=
  reconstructedRate_mul_monomial source (equilibrium t) flux (equilibrium_pos ht) j

theorem equilibrium_stationary {t : ℝ} (ht : 0 < t) (i : Fin 4) :
    ∑ j, (source.stoich i j : ℝ) *
      (rates t j * massActionMonomial source (equilibrium t) j) = 0 := by
  simp_rw [equilibrium_flux ht]
  exact balanced i

end OscillatoryCores

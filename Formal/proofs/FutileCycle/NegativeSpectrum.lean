import proofs.FutileCycle.ReciprocalInstability
import proofs.FutileCycle.NegativeWitness
import proofs.DUnstableCores.DScaling

namespace FutileCycle
noncomputable section
open Polynomial DUnstableCores

def negativeQuintic : ℂ[X] := X^5 + C 5 * X^4 + C 8 * X^3 + C 4 * X^2 + 1

theorem negativeQuintic_rhp : ∃ z : ℂ, negativeQuintic.IsRoot z ∧ 0 < z.re := by
  apply exists_rhp_root_of_reciprocal_sum
  · norm_num [negativeQuintic]
  · norm_num [negativeQuintic, derivative_add, derivative_pow, derivative_mul]
  · have hn : negativeQuintic.natDegree = 5 := by
      unfold negativeQuintic
      compute_degree <;> norm_num
    have hm : negativeQuintic.Monic := by
      apply monic_of_natDegree_le_of_coeff_eq_one 5 (by omega)
      norm_num [negativeQuintic, coeff_add, coeff_C_mul, coeff_X_pow, coeff_one]
    have hh := (IsAlgClosed.splits negativeQuintic).nextCoeff_eq_neg_sum_roots_of_monic hm
    have hc : negativeQuintic.nextCoeff = 5 := by
      rw [nextCoeff, hn]
      norm_num [negativeQuintic, coeff_add, coeff_C_mul, coeff_X_pow, coeff_one]
    rw [hc] at hh
    have hre := congrArg Complex.re hh
    norm_num at hre
    linarith

def negativeRealMatrix : Matrix (Fin 6) (Fin 6) ℝ := negativeMatrix.map Int.cast

def negativeEigenvector (z : ℂ) : Fin 6 → ℂ :=
  ![-1, 1-(z+1)^2, (z+1)^2*(1-(z+1)^2), z+1, (z+1)*(1-(z+1)^2), 1]

theorem negativeEigenvector_nonzero (z : ℂ) : negativeEigenvector z ≠ 0 := by
  intro h
  have hh := congrFun h 5
  change (1 : ℂ) = 0 at hh
  exact one_ne_zero hh

theorem negative_eigenpair (z : ℂ) (hz : negativeQuintic.IsRoot z) :
    HasEigenpair negativeRealMatrix z (negativeEigenvector z) := by
  refine ⟨negativeEigenvector_nonzero z, ?_⟩
  have hq : z^5+5*z^4+8*z^3+4*z^2+1=0 := by
    simpa [negativeQuintic] using hz.eq_zero
  intro i
  fin_cases i <;>
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, complexify,
      negativeRealMatrix, negativeMatrix, negativeEigenvector] <;>
    first | (ring_nf; done) | linear_combination hq

theorem negative_unstable : HurwitzUnstable negativeRealMatrix := by
  obtain ⟨z,hz,hpos⟩ := negativeQuintic_rhp
  exact ⟨z,negativeEigenvector z,hpos,negative_eigenpair z hz⟩

end
end FutileCycle

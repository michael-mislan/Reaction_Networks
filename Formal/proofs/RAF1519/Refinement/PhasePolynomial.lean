import proofs.RAF1519.Refinement.PhaseCoefficients

namespace RAF1519.Refinement
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 40000

def phasePoly (p : Fin 4) (r : ℝ) : ℝ :=
  ∑ j : Fin 5, phaseCoeff j p*r^(j:ℕ)/Nat.factorial (j:ℕ)
def phasePolyDerivative (p : Fin 4) (r : ℝ) : ℝ :=
  ∑ j : Fin 4, phaseCoeff j.succ p*r^(j:ℕ)/Nat.factorial (j:ℕ)

theorem phasePoly_derivative (p : Fin 4) (r : ℝ) :
    HasDerivAt (phasePoly p) (phasePolyDerivative p r) r := by
  have hd : HasDerivAt (phasePoly p)
      (∑ j : Fin 5, phaseCoeff j p*(j:ℕ)*r^((j:ℕ)-1)/Nat.factorial (j:ℕ)) r := by
    unfold phasePoly
    apply HasDerivAt.fun_sum
    intro j _
    convert ((hasDerivAt_pow (j:ℕ) r).const_mul (phaseCoeff j p)).div_const (Nat.factorial (j:ℕ):ℝ) using 1
    ring
  convert hd using 1
  fin_cases p <;> norm_num [phasePolyDerivative,phaseCoeff,Fin.sum_univ_succ,Fin.succ] <;> ring

theorem phasePoly_nonnegative (p : Fin 4) (r : ℝ) (hr : 0 ≤ r) : 0 ≤ phasePoly p r := by
  apply Finset.sum_nonneg
  intro j _
  exact div_nonneg (mul_nonneg (phaseCoeff_nonnegative j p) (pow_nonneg hr _)) (Nat.cast_nonneg _)

theorem phasePolyDerivative_nonnegative (p : Fin 4) (r : ℝ) (hr : 0 ≤ r) :
    0 ≤ phasePolyDerivative p r := by
  apply Finset.sum_nonneg
  intro j _
  exact div_nonneg (mul_nonneg (phaseCoeff_nonnegative j.succ p) (pow_nonneg hr _)) (Nat.cast_nonneg _)

/-- The truncated adjoint has a nonnegative remainder, not a hidden equality
    with the full matrix exponential. -/
theorem phasePoly_residual (p : Fin 4) (r : ℝ) :
    (∑ q, phasePoly q r*phaseH q p)-phasePolyDerivative p r =
      (r^4/24)*(∑ q, phaseCoeff 4 q*phaseH q p) := by
  fin_cases p <;>
    norm_num [phasePoly,phasePolyDerivative,phaseCoeff,phaseH,Fin.sum_univ_succ,Fin.succ] <;> ring

theorem phasePoly_residual_nonnegative (p : Fin 4) (r : ℝ) :
    phasePolyDerivative p r ≤ ∑ q, phasePoly q r*phaseH q p := by
  have hp : 0 ≤ (r^4/24)*(∑ q, phaseCoeff 4 q*phaseH q p) := by
    apply mul_nonneg
    · positivity
    · exact Finset.sum_nonneg (fun q _ => mul_nonneg (phaseCoeff_nonnegative 4 q) (phaseH_nonnegative q p))
  linarith [phasePoly_residual p r]

end
end RAF1519.Refinement

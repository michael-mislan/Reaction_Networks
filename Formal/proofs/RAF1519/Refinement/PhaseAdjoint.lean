import proofs.RAF1519.Refinement.PhasePolynomialBounds
import proofs.RAF1519.Refinement.PhaseExponentialMargin

namespace RAF1519.Refinement
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 40000

def phaseM (q p : Fin 4) : ℝ := phaseH q p-if q=p then 48 else 0
def phaseAdjoint (h : ℝ) (p : Fin 4) (s : ℝ) : ℝ :=
  Real.exp (-(48*(h-s)))*phasePoly p (h-s)
def phaseAdjointDerivative (h : ℝ) (p : Fin 4) (s : ℝ) : ℝ :=
  Real.exp (-(48*(h-s)))*(48*phasePoly p (h-s)-phasePolyDerivative p (h-s))

theorem phaseAdjoint_derivative (h : ℝ) (p : Fin 4) (s : ℝ) :
    HasDerivAt (phaseAdjoint h p) (phaseAdjointDerivative h p s) s := by
  have hshift : HasDerivAt (fun u : ℝ => h-u) (-1) s := (hasDerivAt_id s).const_sub h
  have he : HasDerivAt (fun u => Real.exp (-(48*(h-u))))
      (48*Real.exp (-(48*(h-s)))) s := by
    simpa [mul_comm] using ((hshift.const_mul 48).neg).exp
  have hp := (phasePoly_derivative p (h-s)).comp s hshift
  convert he.mul hp using 1
  dsimp [phaseAdjointDerivative]
  ring

theorem phaseAdjoint_nonnegative (h s : ℝ) (hs : s ≤ h) (p : Fin 4) :
    0 ≤ phaseAdjoint h p s :=
  mul_nonneg (Real.exp_pos _).le (phasePoly_nonnegative p _ (sub_nonneg.mpr hs))

theorem phaseM_left_action (x : Fin 4 → ℝ) (p : Fin 4) :
    (∑ q, x q*phaseM q p) = (∑ q, x q*phaseH q p)-48*x p := by
  unfold phaseM
  simp_rw [mul_sub,mul_ite,mul_zero]
  rw [Finset.sum_sub_distrib]
  simp [mul_comm]

theorem phaseAdjoint_residual (h s : ℝ) (p : Fin 4) :
    0 ≤ phaseAdjointDerivative h p s+∑ q, phaseAdjoint h q s*phaseM q p := by
  rw [phaseM_left_action]
  have he : (∑ q, phaseAdjoint h q s*phaseH q p) =
      Real.exp (-(48*(h-s)))*(∑ q, phasePoly q (h-s)*phaseH q p) := by
    simp only [phaseAdjoint,Finset.mul_sum,mul_assoc]
  rw [he]
  have hp := mul_le_mul_of_nonneg_left (phasePoly_residual_nonnegative p (h-s))
    (Real.exp_pos (-(48*(h-s)))).le
  dsimp [phaseAdjointDerivative,phaseAdjoint]
  nlinarith

theorem phaseAdjoint_sum_bound (h s : ℝ) (hs : s ≤ h) :
    (∑ p, phaseAdjoint h p s) ≤ 3/2 := by
  have hp := mul_le_mul_of_nonneg_left (phasePoly_sum_bound (h-s) (sub_nonneg.mpr hs))
    (Real.exp_pos (-(48*(h-s)))).le
  have he : Real.exp (-(48*(h-s)))*Real.exp (48*(h-s)) = 1 := by
    rw [← Real.exp_add]
    simp
  unfold phaseAdjoint
  rw [← Finset.mul_sum]
  nlinarith

theorem phaseAdjoint_derivative_sum_bound (h s : ℝ) (hs : s ≤ h) :
    (∑ p, |phaseAdjointDerivative h p s|) ≤ 132 := by
  have he : Real.exp (-(48*(h-s)))*Real.exp (48*(h-s)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hp := phaseAdjoint_sum_bound h s hs
  have hd := mul_le_mul_of_nonneg_left (phasePolyDerivative_sum_bound (h-s) (sub_nonneg.mpr hs))
    (Real.exp_pos (-(48*(h-s)))).le
  have hlocal : ∀ p, |phaseAdjointDerivative h p s| ≤
      48*phaseAdjoint h p s+Real.exp (-(48*(h-s)))*phasePolyDerivative p (h-s) := by
    intro p
    unfold phaseAdjointDerivative phaseAdjoint
    rw [abs_mul,abs_of_pos (Real.exp_pos _)]
    have hh := abs_sub (48*phasePoly p (h-s)) (phasePolyDerivative p (h-s))
    rw [abs_of_nonneg (mul_nonneg (by norm_num) (phasePoly_nonnegative p _ (sub_nonneg.mpr hs))),
      abs_of_nonneg (phasePolyDerivative_nonnegative p _ (sub_nonneg.mpr hs))] at hh
    nlinarith [Real.exp_pos (-(48*(h-s)))]
  have hsum := Finset.sum_le_sum (fun p (_ : p ∈ Finset.univ) => hlocal p)
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum] at hsum
  nlinarith

theorem phaseAdjoint_terminal (h : ℝ) (p : Fin 4) :
    phaseAdjoint h p h = if p=0 then 1 else 0 := by
  fin_cases p <;> norm_num [phaseAdjoint,phasePoly,phaseCoeff,Fin.sum_univ_succ]

theorem phaseAdjoint_initial (p : Fin 4) : phaseWeight p/8 ≤ phaseAdjoint (1/28) p 0 := by
  simpa only [phaseAdjoint,sub_zero,phasePoly] using phase_initial_weight_bound p

end
end RAF1519.Refinement

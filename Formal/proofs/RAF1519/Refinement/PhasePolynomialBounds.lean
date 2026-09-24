import proofs.RAF1519.Refinement.PhasePolynomial

namespace RAF1519.Refinement
noncomputable section
open scoped BigOperators

theorem finite_exp_sum_le (N : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (∑ j : Fin N, x^(j:ℕ)/Nat.factorial (j:ℕ)) ≤ Real.exp x := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => x^j/Nat.factorial j) N]
  exact Real.sum_le_exp_of_nonneg hx N

theorem phasePoly_sum_bound (r : ℝ) (hr : 0 ≤ r) :
    (∑ p, phasePoly p r) ≤ (3/2)*Real.exp (48*r) := by
  calc
    _ = ∑ j : Fin 5, (∑ p, phaseCoeff j p)*r^(j:ℕ)/Nat.factorial (j:ℕ) := by
      unfold phasePoly
      rw [Finset.sum_comm]
      simp only [Finset.sum_div,Finset.sum_mul]
    _ ≤ ∑ j : Fin 5, ((3/2)*48^(j:ℕ))*r^(j:ℕ)/Nat.factorial (j:ℕ) := by
      apply Finset.sum_le_sum
      intro j _
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (phaseCoeff_weight_bound j) (pow_nonneg hr _)) (Nat.cast_nonneg _)
    _ = (3/2)*(∑ j : Fin 5, (48*r)^(j:ℕ)/Nat.factorial (j:ℕ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (finite_exp_sum_le 5 (48*r) (by linarith)) (by norm_num)

theorem phasePolyDerivative_sum_bound (r : ℝ) (hr : 0 ≤ r) :
    (∑ p, phasePolyDerivative p r) ≤ 60*Real.exp (48*r) := by
  calc
    _ = ∑ j : Fin 4, (∑ p, phaseCoeff j.succ p)*r^(j:ℕ)/Nat.factorial (j:ℕ) := by
      unfold phasePolyDerivative
      rw [Finset.sum_comm]
      simp only [Finset.sum_div,Finset.sum_mul]
    _ ≤ ∑ j : Fin 4, (60*48^(j:ℕ))*r^(j:ℕ)/Nat.factorial (j:ℕ) := by
      apply Finset.sum_le_sum
      intro j _
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (phaseCoeff_derivative_bound j) (pow_nonneg hr _)) (Nat.cast_nonneg _)
    _ = 60*(∑ j : Fin 4, (48*r)^(j:ℕ)/Nat.factorial (j:ℕ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (finite_exp_sum_le 4 (48*r) (by linarith)) (by norm_num)

end
end RAF1519.Refinement

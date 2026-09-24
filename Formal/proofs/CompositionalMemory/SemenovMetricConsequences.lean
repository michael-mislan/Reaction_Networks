import proofs.CompositionalMemory.SemenovMetricEnclosure

namespace CompositionalMemory.Semenov
open Matrix

theorem geometry_metric_bounds
    (zc : Fin 8 → Fin 17 → ℚ) (pc wc : Fin 8 → Fin 8 → Fin 17 → ℚ)
    (A : Fin 8 → Fin 8 → ℚ) (nr : Fin 11 → ℚ) (eta radius margin L Q H : ℚ)
    (hg : MetricGeometryChecks zc pc wc A nr eta radius margin L Q H)
    (t : ℝ) (hl : -1 ≤ t) (hu : t ≤ 1)
    (hw : coefficientMatrix wc t = rationalMatrix A * coefficientMatrix pc t * (rationalMatrix A).transpose)
    (hp : ∀ i j,coefficientValue (pc i j) t=coefficientValue (pc j i) t)
    (x : Fin 8 → ℝ) :
    0 ≤ matrixEnergy (coefficientMatrix pc t) x ∧
    matrixEnergy (coefficientMatrix pc t) x ≤ (L : ℝ)*vectorSquares x := by
  rcases hg with ⟨hpos,htri,hdiag,hmargin,hnr,hcurv,heta,hL,hH,hJ,hQ⟩
  have hdet : (rationalMatrix A).det ≠ 0 := by
    apply lower_triangular_det_ne_zero
    · intro i j hij
      change (A i j : ℝ)=0
      exact_mod_cast htri i j hij
    · intro i
      change (0 : ℝ) < (A i i : ℝ)
      exact_mod_cast hdiag i
  have hmargin0 : (0 : ℝ) < margin := by exact_mod_cast hpos.2.2.1
  have hnorm : 0 < frobeniusSquared (rationalMatrix A) := by
    unfold frobeniusSquared rationalMatrix
    have hh := hpos.2.2.2
    unfold whiteningNormSquared at hh
    exact_mod_cast hh
  have hc := whitened_metric_coercivity (coefficientMatrix pc t) (rationalMatrix A) hdet
    (margin : ℝ) hmargin0.le (by
      intro y
      rw [← hw]
      exact matrix_energy_diagonal_lower _ (coefficient_congruence_symmetric pc wc A t hw hp)
        (margin : ℝ) (coefficient_matrix_diagonal_bound wc margin hmargin t hl hu) y) x
  constructor
  · exact (mul_nonneg_iff_of_pos_left hnorm).mp
      ((mul_nonneg hmargin0.le (vectorSquares_nonneg x)).trans hc)
  · exact (le_abs_self _).trans (matrix_energy_norm_bound _ hp (L : ℝ)
      (coefficient_matrix_row_bound pc L hL t hl hu) x)

theorem metric_jump_value (pc : Fin 8 → Fin 8 → Fin 17 → ℚ) (r : Fin 11) (i : Fin 8) (t : ℝ) :
    coefficientValue (metricJumpCoefficients pc r i) t=
      (coefficientMatrix pc t).mulVec (fun j => (stoich r j : ℝ)) i := by
  change coefficientValue (fun k => ∑ j,(stoich r j : ℚ)*pc i j k) t = _
  rw [coefficientValue_linear]
  simp only [Matrix.mulVec,dotProduct,coefficientMatrix]
  apply Finset.sum_congr rfl
  intro j _
  norm_num only [Rat.cast_intCast]
  ring

theorem metric_jump_norm_bound (pc : Fin 8 → Fin 8 → Fin 17 → ℚ) (nr : Fin 11 → ℚ)
    (hcheck : ∀ r,(∑ i,(coefficientNorm (metricJumpCoefficients pc r i))^2) ≤ (nr r)^2)
    (t : ℝ) (hl : -1 ≤ t) (hu : t ≤ 1) (r : Fin 11) :
    vectorSquares ((coefficientMatrix pc t).mulVec (fun j => (stoich r j : ℝ))) ≤ (nr r : ℝ)^2 := by
  unfold vectorSquares
  calc
    _ ≤ ∑ i,(coefficientNorm (metricJumpCoefficients pc r i) : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [← metric_jump_value]
      have hh := pow_le_pow_left₀ (abs_nonneg _) (coefficientValue_abs (metricJumpCoefficients pc r i) t hl hu) 2
      simpa only [sq_abs] using hh
    _ ≤ _ := by exact_mod_cast hcheck r

end CompositionalMemory.Semenov

import proofs.SmallCusp.Normalization.TraceFreeCertificate

/-!
# Coefficientwise-positive determinant obstructions

The finite checker only needs to establish one polynomial identity.  On the
positive flux cone, a nonzero quadratic with nonnegative monomial
coefficients is strictly positive.  Equilibrium-row multiples vanish, so such
an identity excludes a singular Jacobian and hence excludes a cusp.
-/

open scoped BigOperators

namespace SmallCusp

def unitJacobianDet {m : ℕ} (Q : SmallPlanarNetwork m)
    (v : Fin m → ℝ) : ℝ :=
  Q.jacobian v unitState 0 0 * Q.jacobian v unitState 1 1 -
    Q.jacobian v unitState 0 1 * Q.jacobian v unitState 1 0

theorem unitJacobianDet_eq_zero_of_rightKernel {m : ℕ}
    (Q : SmallPlanarNetwork m) (v : Fin m → ℝ) (q : Species → ℝ)
    (hq : q ≠ 0)
    (hkernel : ∀ i, Q.jacobianApply v unitState q i = 0) :
    unitJacobianDet Q v = 0 := by
  have h0 := hkernel 0
  have h1 := hkernel 1
  simp only [SmallPlanarNetwork.jacobianApply, Fin.sum_univ_two] at h0 h1
  have hcomponent : q 0 ≠ 0 ∨ q 1 ≠ 0 := by
    by_cases hq0 : q 0 = 0
    · right
      intro hq1
      apply hq
      funext i
      fin_cases i
      · exact hq0
      · exact hq1
    · exact Or.inl hq0
  rcases hcomponent with hq0 | hq1
  · have hmul : unitJacobianDet Q v * q 0 = 0 := by
      calc
        unitJacobianDet Q v * q 0 =
            Q.jacobian v unitState 1 1 *
                (Q.jacobian v unitState 0 0 * q 0 +
                  Q.jacobian v unitState 0 1 * q 1) -
              Q.jacobian v unitState 0 1 *
                (Q.jacobian v unitState 1 0 * q 0 +
                  Q.jacobian v unitState 1 1 * q 1) := by
              simp [unitJacobianDet]
              ring
        _ = 0 := by rw [h0, h1]; ring
    exact (mul_eq_zero.mp hmul).resolve_right hq0
  · have hmul : unitJacobianDet Q v * q 1 = 0 := by
      calc
        unitJacobianDet Q v * q 1 =
            Q.jacobian v unitState 0 0 *
                (Q.jacobian v unitState 1 0 * q 0 +
                  Q.jacobian v unitState 1 1 * q 1) -
              Q.jacobian v unitState 1 0 *
                (Q.jacobian v unitState 0 0 * q 0 +
                  Q.jacobian v unitState 0 1 * q 1) := by
              simp [unitJacobianDet]
              ring
        _ = 0 := by rw [h0, h1]; ring
    exact (mul_eq_zero.mp hmul).resolve_right hq1

private theorem positive_quadratic_sum {m : ℕ}
    (coeff : Fin m → Fin m → ℝ) (v : Fin m → ℝ)
    (hc : ∀ i j, 0 ≤ coeff i j) (hv : PositiveVector v)
    (hw : ∃ i j, 0 < coeff i j) :
    0 < ∑ i : Fin m, ∑ j : Fin m, coeff i j * v i * v j := by
  rcases hw with ⟨wi, wj, hw⟩
  have hterm : ∀ i j, 0 ≤ coeff i j * v i * v j := by
    intro i j
    exact mul_nonneg (mul_nonneg (hc i j) (le_of_lt (hv i))) (le_of_lt (hv j))
  have hinner_nonneg : ∀ i, 0 ≤ ∑ j : Fin m, coeff i j * v i * v j := by
    intro i
    exact Finset.sum_nonneg fun j _ => hterm i j
  apply (Finset.sum_pos_iff_of_nonneg fun i _ => hinner_nonneg i).2
  refine ⟨wi, Finset.mem_univ _, ?_⟩
  apply (Finset.sum_pos_iff_of_nonneg fun j _ => hterm wi j).2
  refine ⟨wj, Finset.mem_univ _, ?_⟩
  exact mul_pos (mul_pos hw (hv wi)) (hv wj)

theorem conicDeterminantCertificate_excludes_cusp {m : ℕ}
    (Q : SmallPlanarNetwork m)
    (sign : ℝ) (coeff : Fin m → Fin m → ℝ)
    (multiplier : Species → Fin m → ℝ)
    (hc : ∀ i j, 0 ≤ coeff i j)
    (hw : ∃ i j, 0 < coeff i j)
    (hidentity : ∀ v : Fin m → ℝ,
      sign * unitJacobianDet Q v =
        (∑ i : Fin m, ∑ j : Fin m, coeff i j * v i * v j) +
        ∑ s : Species,
          (∑ r : Fin m, multiplier s r * v r) *
            Q.massAction v unitState s) :
    ¬ AdmitsTransverseCusp Q := by
  intro hcusp
  obtain ⟨D, hD⟩ := admitsTransverseCusp_implies_traceFreeNormalized Q hcusp
  rcases hD with ⟨hstate, hv, heq, hright, _hleft, hq, _hp,
    _hfold, _hcenter, _hcubic, _hunfold⟩
  have hdet : unitJacobianDet Q D.rates = 0 := by
    apply unitJacobianDet_eq_zero_of_rightKernel Q D.rates D.rightKernel hq
    intro i
    simpa [hstate] using hright i
  have hpositive := positive_quadratic_sum coeff D.rates hc hv hw
  have hid := hidentity D.rates
  have heqUnit : ∀ s, Q.massAction D.rates unitState s = 0 := by
    intro s
    simpa [hstate] using heq s
  simp_rw [heqUnit, mul_zero, Finset.sum_const_zero, add_zero] at hid
  rw [hdet, mul_zero] at hid
  linarith

end SmallCusp

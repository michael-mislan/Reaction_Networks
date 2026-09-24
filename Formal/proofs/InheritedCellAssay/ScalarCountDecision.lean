import proofs.InheritedCellAssay.ScalarCountIntegral

namespace InheritedCellAssay.ScalarCount

/-- Parameter proposed by the scalar birth/death calculation. The source-law
    identification is a separate obligation, not a premise hidden here. -/
noncomputable def geometricParameter : ℝ := 128 / (33 * varianceIntegral + 97)

noncomputable def scalarTail (k : ℕ) : ℝ :=
  (33/64) * geometricParameter * (1-geometricParameter)^k

theorem geometricParameter_bounds :
    512/685 ≤ geometricParameter ∧ geometricParameter ≤ 64/65 := by
  obtain ⟨hl, hu⟩ := varianceIntegral_bounds
  have hd : 0 < 33 * varianceIntegral + 97 := by linarith
  constructor
  · unfold geometricParameter
    apply (le_div_iff₀ hd).mpr
    linarith
  · unfold geometricParameter
    apply (div_le_iff₀ hd).mpr
    linarith

theorem scalar_two_tail_small : scalarTail 2 < 1/40 := by
  obtain ⟨hl, hu⟩ := geometricParameter_bounds
  let r := 1-geometricParameter
  let R : ℝ := 173/685
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hR : r ≤ R := by dsimp [r, R]; linarith
  have hsq : r^2 ≤ R^2 := by nlinarith
  have hcross : R*r ≤ R^2 := by dsimp [R] at *; nlinarith
  have hb : 0 ≤ R+r-R^2-R*r-r^2 := by dsimp [R] at *; nlinarith
  have hm := mul_nonneg (sub_nonneg.mpr hR) hb
  have hc : r^2-r^3 ≤ R^2-R^3 := by nlinarith [hm]
  unfold scalarTail
  change (33/64) * geometricParameter * r^2 < 1/40
  have hp : geometricParameter = 1-r := by dsimp [r]; ring
  rw [hp]
  dsimp [R] at hc
  nlinarith

/-- Exact arithmetic for the proposed source tail and its one-cell repair.
    This theorem deliberately does not assert a stochastic source bridge. -/
theorem proposed_source_decision :
    1 - (5/24 : ℝ) * (1/2)^2 = 91/96 ∧
    (91/96 : ℝ) < 19/20 ∧
    1 - (5/24 : ℝ) * (1/2)^3 = 187/192 ∧
    (19/20 : ℝ) < 187/192 := by norm_num

end InheritedCellAssay.ScalarCount

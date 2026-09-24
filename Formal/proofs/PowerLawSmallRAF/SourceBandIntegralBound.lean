import proofs.PowerLawSmallRAF.SourceDegreeBandConcentration

namespace PowerLawSmallRAF

open scoped BigOperators
set_option maxHeartbeats 100000
noncomputable section

/-- A finite additive error, uniform in both moving band endpoints. Unlike
a fixed-width limit, this remains useful after division by a shrinking
logarithmic window whose unnormalized width tends to infinity. -/
theorem sourceTruncatedBandMean_integral_error
    (a : ℝ) (n L U : Nat) (ha : 1 < a) (hn : 2 ≤ n)
    (hL : 1 ≤ L) (hLU : L ≤ U) (hUR : U < sourceReactionCount n) :
    |sourceTruncatedBandMean a n L U * zipfNormalizer a -
      ((∫ x in (1 : ℝ)..((U + 1 : Nat) : ℝ), x ^ (-(a-1))) -
       (∫ x in (1 : ℝ)..((L + 1 : Nat) : ℝ), x ^ (-(a-1))))| ≤
      1 + zipfNormalizer a := by
  have hzpos : 0 < zipfNormalizer a := by
    rw [zipfNormalizer_eq_prefix_add_tail ha 2, zipfPrefix_two ha]
    nlinarith [rpowTail_nonneg a 2]
  have hm : sourceTruncatedBandMean a n L U * zipfNormalizer a =
      windowPartialNumerator a (U+1) - windowPartialNumerator a (L+1) := by
    rw [sourceTruncatedBandMean_eq_highNumerator_sub a n L U hn hL hLU hUR,
      div_mul_cancel₀ _ hzpos.ne']
    unfold windowHighNumerator
    ring
  rw [windowPartialNumerator_eq a (U+1) (by omega),
    windowPartialNumerator_eq a (L+1) (by omega)] at hm
  have hupper := tiltedHarmonic_integral_bounds (a-1) (by linarith) (U+1) (by omega)
  have hlower := tiltedHarmonic_integral_bounds (a-1) (by linarith) (L+1) (by omega)
  have hu0 := windowInterior_nonneg a (U+1)
  have hu1 := windowInterior_le_normalizer a ha (U+1)
  have hl0 := windowInterior_nonneg a (L+1)
  have hl1 := windowInterior_le_normalizer a ha (L+1)
  rw [abs_le]
  constructor <;> linarith only [hm, hupper.1, hupper.2, hlower.1, hlower.2,
    hu0, hu1, hl0, hl1]

theorem sourceTruncatedBandMean_unshifted_integral_error
    (a : ℝ) (n L U : Nat) (ha : 1 < a) (hn : 2 ≤ n)
    (hL : 2 ≤ L) (hLU : L ≤ U) (hUR : U < sourceReactionCount n) :
    |sourceTruncatedBandMean a n L U * zipfNormalizer a -
      ((∫ x in (1 : ℝ)..(U : ℝ), x ^ (-(a-1))) -
       (∫ x in (1 : ℝ)..(L : ℝ), x ^ (-(a-1))))| ≤
      2 + zipfNormalizer a := by
  have hzpos : 0 < zipfNormalizer a := by
    rw [zipfNormalizer_eq_prefix_add_tail ha 2, zipfPrefix_two ha]
    nlinarith [rpowTail_nonneg a 2]
  have hm : sourceTruncatedBandMean a n L U * zipfNormalizer a =
      windowPartialNumerator a (U+1) - windowPartialNumerator a (L+1) := by
    rw [sourceTruncatedBandMean_eq_highNumerator_sub a n L U hn (by omega) hLU hUR,
      div_mul_cancel₀ _ hzpos.ne']
    unfold windowHighNumerator
    ring
  rw [windowPartialNumerator_eq a (U+1) (by omega),
    windowPartialNumerator_eq a (L+1) (by omega)] at hm
  have hstep (M : Nat) (hM : 2 ≤ M) :
      tiltedHarmonic (a-1) (M+1) = tiltedHarmonic (a-1) M + (M : ℝ)^(-(a-1)) := by
    unfold tiltedHarmonic
    exact Finset.sum_Ico_succ_top (by omega : 1 ≤ M) _
  rw [hstep U (by omega), hstep L hL] at hm
  have hp (M : Nat) (hM : 2 ≤ M) :
      0 ≤ (M : ℝ)^(-(a-1)) ∧ (M : ℝ)^(-(a-1)) ≤ 1 := by
    exact ⟨Real.rpow_nonneg (by positivity) _,
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (show 1 ≤ M by omega))
        (by linarith)⟩
  have hupper := tiltedHarmonic_integral_bounds (a-1) (by linarith) U (by omega)
  have hlower := tiltedHarmonic_integral_bounds (a-1) (by linarith) L hL
  have hu0 := windowInterior_nonneg a (U+1)
  have hu1 := windowInterior_le_normalizer a ha (U+1)
  have hl0 := windowInterior_nonneg a (L+1)
  have hl1 := windowInterior_le_normalizer a ha (L+1)
  have hpU := hp U (by omega)
  have hpL := hp L hL
  rw [abs_le]
  constructor <;> linarith only [hm, hupper.1, hupper.2, hlower.1, hlower.2,
    hu0, hu1, hl0, hl1, hpU.1, hpU.2, hpL.1, hpL.2]

end
end PowerLawSmallRAF

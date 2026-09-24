import proofs.PowerLawSmallRAF.CalibratedGatewayHighTail
import proofs.PowerLawSmallRAF.SeedClosed

namespace PowerLawSmallRAF

open Filter Topology

/-- Degree law after conditioning on one specified catalytic edge. -/
noncomputable def specifiedEdgeDegreeMass (a : ℝ) (R d : Nat) : ℝ :=
  (d : ℝ) * cappedZipfDegreeMass a R d / windowZipfMean a R

theorem specifiedEdgeDegreeMass_sum_eq_one
    (a : ℝ) (R : Nat) (hR : 2 ≤ R) (hmean : windowZipfMean a R ≠ 0) :
    ∑ d ∈ Finset.range R, specifiedEdgeDegreeMass a R d = 1 := by
  simp_rw [specifiedEdgeDegreeMass]
  rw [← Finset.sum_div]
  have hfirst := cappedZipfDegreeFirstMoment_eq a R hR
  rw [show (∑ d ∈ Finset.range R,
      (d : ℝ) * cappedZipfDegreeMass a R d) = windowZipfMean a R by
    simpa only [mul_comm] using hfirst]
  exact div_self hmean

theorem specifiedEdgeDegreeMass_nonneg
    (a : ℝ) (R d : Nat) (hz : 0 < zipfNormalizer a)
    (hmean : 0 < windowZipfMean a R) :
    0 ≤ specifiedEdgeDegreeMass a R d := by
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg d)
    (cappedZipfDegreeMass_nonneg a R d hz)) hmean.le

/-- The exact finite CDF identity behind the high/low degree split.  The cap
does not enter below `M <= R`, so changing variables `k=d+1` recovers the
partial size-biased numerator literally. -/
theorem specifiedEdgeDegreeMass_sum_range_eq_sizeBiasedLogCdf
    (a : ℝ) (R M : Nat) (hM : 2 ≤ M) (hMR : M ≤ R)
    (hz : zipfNormalizer a ≠ 0)
    (hdirect : windowDirectNumerator a R ≠ 0) :
    (∑ d ∈ Finset.range (M - 1), specifiedEdgeDegreeMass a R d) =
      sizeBiasedLogCdf a R M := by
  have hMsplit : M - 1 = (M - 2) + 1 := by omega
  rw [hMsplit, Finset.sum_range_succ']
  rw [show specifiedEdgeDegreeMass a R 0 = 0 by
    simp [specifiedEdgeDegreeMass], add_zero]
  have hinterior : ∀ i ∈ Finset.range (M - 2),
      specifiedEdgeDegreeMass a R (i + 1) =
        (((i + 1 : Nat) : ℝ) * ((i + 2 : Nat) : ℝ) ^ (-a)) /
          windowDirectNumerator a R := by
    intro i hi
    have hiM : i + 2 < M := by
      have := Finset.mem_range.mp hi
      omega
    have hiR : i + 2 < R := hiM.trans_le hMR
    rw [specifiedEdgeDegreeMass, cappedZipfDegreeMass, if_pos hiR,
      windowZipfMean]
    have hcast : ((i + 1 : Nat) : ℝ) + 1 = ((i + 2 : Nat) : ℝ) := by
      exact_mod_cast (by omega : i + 1 + 1 = i + 2)
    rw [show i + 1 + 1 = i + 2 by omega, hcast]
    field_simp [hz, hdirect]
  rw [Finset.sum_congr rfl hinterior]
  dsimp [sizeBiasedLogCdf, windowPartialNumerator]
  rw [Finset.sum_Ico_eq_sum_range, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show 2 + i = i + 2 by omega, show i + 2 - 1 = i + 1 by omega]

/-- An abstract finite-mixture inequality.  It is stated independently of the
chemistry so the only source-specific work is supplying a low-degree event
bound and the exact conditioned degree weights. -/
theorem weighted_probability_le_lowBound_add_highMass
    {R M : Nat} (w p : Nat → ℝ) (B : ℝ)
    (hw0 : ∀ d ∈ Finset.range R, 0 ≤ w d)
    (hp1 : ∀ d ∈ Finset.range R, p d ≤ 1)
    (hlow : ∀ d ∈ Finset.range M, p d ≤ B)
    (hB0 : 0 ≤ B)
    (hMR : M ≤ R)
    (hsum : ∑ d ∈ Finset.range R, w d = 1) :
    ∑ d ∈ Finset.range R, w d * p d ≤
      B + (1 - ∑ d ∈ Finset.range M, w d) := by
  have hsplit : (∑ d ∈ Finset.range R, w d * p d) =
      (∑ d ∈ Finset.range M, w d * p d) +
        ∑ d ∈ Finset.Ico M R, w d * p d := by
    exact (Finset.sum_range_add_sum_Ico _ hMR).symm
  rw [hsplit]
  have hlowSum : (∑ d ∈ Finset.range M, w d * p d) ≤
      B * ∑ d ∈ Finset.range M, w d := by
    calc
      (∑ d ∈ Finset.range M, w d * p d) ≤
          ∑ d ∈ Finset.range M, w d * B := by
        apply Finset.sum_le_sum
        intro d hd
        exact mul_le_mul_of_nonneg_left (hlow d hd)
          (hw0 d (Finset.mem_range.mpr
            ((Finset.mem_range.mp hd).trans_le hMR)))
      _ = B * ∑ d ∈ Finset.range M, w d := by
        rw [← Finset.sum_mul]
        ring
  have hhighSum : (∑ d ∈ Finset.Ico M R, w d * p d) ≤
      ∑ d ∈ Finset.Ico M R, w d := by
    apply Finset.sum_le_sum
    intro d hd
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (hp1 d (Finset.mem_range.mpr (Finset.mem_Ico.mp hd).2))
      (hw0 d (Finset.mem_range.mpr (Finset.mem_Ico.mp hd).2))
  have hweightSplit : (∑ d ∈ Finset.range M, w d) +
      ∑ d ∈ Finset.Ico M R, w d = 1 := by
    simpa only [hsum] using Finset.sum_range_add_sum_Ico w hMR
  have hlowWeight : ∑ d ∈ Finset.range M, w d ≤ 1 := by
    have hhighWeight : 0 ≤ ∑ d ∈ Finset.Ico M R, w d :=
      Finset.sum_nonneg fun d hd =>
        hw0 d (Finset.mem_range.mpr (Finset.mem_Ico.mp hd).2)
    nlinarith
  nlinarith

end PowerLawSmallRAF

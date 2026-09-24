import proofs.PowerLawSmallRAF.SourceSplitBlockProbability
import proofs.PowerLawSmallRAF.SourcePolynomialCutoff
import proofs.PowerLawSmallRAF.ReversibleCloudAsymptotics

namespace PowerLawSmallRAF

open Filter Topology

theorem hypergeometricGatewayMiss_nonneg_le_one
    (R M d : Nat) (hdR : d < R) :
    0 ≤ hypergeometricGatewayMiss R M d ∧
      hypergeometricGatewayMiss R M d ≤ 1 := by
  have hdenNat : 0 < Nat.choose R d := Nat.choose_pos hdR.le
  have hden : (0 : ℝ) < Nat.choose R d := by exact_mod_cast hdenNat
  constructor
  · dsimp [hypergeometricGatewayMiss]
    positivity
  · rw [hypergeometricGatewayMiss]
    apply (div_le_one hden).2
    exact_mod_cast Nat.choose_le_choose d (Nat.sub_le R M)

theorem powerLawMoleculeGatewayHit_nonneg_le_one
    (a : ℝ) (R M : Nat) (ha : 1 < a) (hR : 2 ≤ R) :
    0 ≤ powerLawMoleculeGatewayHit a R M ∧
      powerLawMoleculeGatewayHit a R M ≤ 1 := by
  have hzpos : 0 < zipfNormalizer a := by
    rw [zipfNormalizer_eq_prefix_add_tail ha 2, zipfPrefix_two ha]
    nlinarith [rpowTail_nonneg a 2]
  rw [powerLawMoleculeGatewayHit_eq_sum a R M ha hR]
  constructor
  · apply Finset.sum_nonneg
    intro d hd
    exact mul_nonneg (cappedZipfDegreeMass_nonneg a R d hzpos)
      (sub_nonneg.mpr (hypergeometricGatewayMiss_nonneg_le_one
        R M d (Finset.mem_range.mp hd)).2)
  · calc
      (∑ d ∈ Finset.range R, cappedZipfDegreeMass a R d *
          (1 - hypergeometricGatewayMiss R M d)) ≤
          ∑ d ∈ Finset.range R, cappedZipfDegreeMass a R d := by
        apply Finset.sum_le_sum
        intro d hd
        have hmass := cappedZipfDegreeMass_nonneg a R d hzpos
        have hmiss := (hypergeometricGatewayMiss_nonneg_le_one
          R M d (Finset.mem_range.mp hd)).1
        nlinarith
      _ = 1 := cappedZipfDegreeMass_sum_eq_one a R ha hR

theorem one_sub_pow_le_exp_neg_mul
    (p : ℝ) (X : Nat) (hp1 : p ≤ 1) :
    (1 - p) ^ X ≤ Real.exp ((X : ℝ) * (-p)) := by
  have hbase : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  calc
    (1 - p) ^ X ≤ (Real.exp (-p)) ^ X :=
      pow_le_pow_left₀ hbase (Real.one_sub_le_exp_neg p) X
    _ = Real.exp ((X : ℝ) * (-p)) := by rw [← Real.exp_nat_mul]

/-- A degree truncation replaces the global second moment by a multiple of
the retained first moment.  This is the finite inequality needed uniformly
for all split-block sizes `M ≤ n`. -/
theorem powerLawMoleculeGatewayHit_ge_truncatedFirstMoment
    (a : ℝ) (R M L : Nat) (ha : 1 < a) (hR : 2 ≤ R)
    (hM0 : 0 < M) (hMR : M ≤ R) (hLR : L ≤ R) :
    ((M : ℝ) / (R : ℝ) -
        ((M : ℝ) / ((R - M + 1 : Nat) : ℝ)) ^ 2 * (L : ℝ)) *
        (∑ d ∈ Finset.range L,
          cappedZipfDegreeMass a R d * (d : ℝ)) ≤
      powerLawMoleculeGatewayHit a R M := by
  have hzpos : 0 < zipfNormalizer a := by
    rw [zipfNormalizer_eq_prefix_add_tail ha 2, zipfPrefix_two ha]
    nlinarith [rpowTail_nonneg a 2]
  have hpoint : ∀ d ∈ Finset.range L,
      ((M : ℝ) / (R : ℝ) -
          ((M : ℝ) / ((R - M + 1 : Nat) : ℝ)) ^ 2 * (L : ℝ)) *
          (cappedZipfDegreeMass a R d * (d : ℝ)) ≤
        cappedZipfDegreeMass a R d *
          (1 - hypergeometricGatewayMiss R M d) := by
    intro d hd
    have hdL : d ≤ L := (Finset.mem_range.mp hd).le
    have hdR : d < R := (Finset.mem_range.mp hd).trans_le hLR
    have hmass : 0 ≤ cappedZipfDegreeMass a R d :=
      cappedZipfDegreeMass_nonneg a R d hzpos
    have henv := (hypergeometricGatewayHit_envelope R M d hM0 hMR hdR).1
    have hd0 : (0 : ℝ) ≤ d := by positivity
    have hdLreal : (d : ℝ) ≤ L := by exact_mod_cast hdL
    have hsq : (d : ℝ) ^ 2 ≤ (L : ℝ) * (d : ℝ) := by nlinarith
    have hden0 : (0 : ℝ) < ((R - M + 1 : Nat) : ℝ) := by positivity
    have hinner :
        ((M : ℝ) / (R : ℝ) -
            ((M : ℝ) / ((R - M + 1 : Nat) : ℝ)) ^ 2 * (L : ℝ)) *
            (d : ℝ) ≤
          (M : ℝ) * (d : ℝ) / (R : ℝ) -
            ((M : ℝ) * (d : ℝ) /
              ((R - M + 1 : Nat) : ℝ)) ^ 2 := by
      have hq : 0 ≤ ((M : ℝ) /
          ((R - M + 1 : Nat) : ℝ)) ^ 2 := sq_nonneg _
      calc
        ((M : ℝ) / (R : ℝ) -
            ((M : ℝ) / ((R - M + 1 : Nat) : ℝ)) ^ 2 * (L : ℝ)) *
            (d : ℝ) =
          (M : ℝ) * (d : ℝ) / (R : ℝ) -
            ((M : ℝ) / ((R - M + 1 : Nat) : ℝ)) ^ 2 *
              ((L : ℝ) * (d : ℝ)) := by ring
        _ ≤ (M : ℝ) * (d : ℝ) / (R : ℝ) -
            ((M : ℝ) / ((R - M + 1 : Nat) : ℝ)) ^ 2 *
              (d : ℝ) ^ 2 := by nlinarith
        _ = (M : ℝ) * (d : ℝ) / (R : ℝ) -
            ((M : ℝ) * (d : ℝ) /
              ((R - M + 1 : Nat) : ℝ)) ^ 2 := by ring
    calc
      ((M : ℝ) / (R : ℝ) -
          ((M : ℝ) / ((R - M + 1 : Nat) : ℝ)) ^ 2 * (L : ℝ)) *
          (cappedZipfDegreeMass a R d * (d : ℝ)) =
        cappedZipfDegreeMass a R d *
          (((M : ℝ) / (R : ℝ) -
            ((M : ℝ) / ((R - M + 1 : Nat) : ℝ)) ^ 2 * (L : ℝ)) *
            (d : ℝ)) := by ring
      _ ≤ cappedZipfDegreeMass a R d *
          ((M : ℝ) * (d : ℝ) / (R : ℝ) -
            ((M : ℝ) * (d : ℝ) /
              ((R - M + 1 : Nat) : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_left hinner hmass
      _ ≤ cappedZipfDegreeMass a R d *
          (1 - hypergeometricGatewayMiss R M d) :=
        mul_le_mul_of_nonneg_left henv hmass
  have htrunc := Finset.sum_le_sum hpoint
  rw [← Finset.mul_sum] at htrunc
  have hsubset : Finset.range L ⊆ Finset.range R :=
    Finset.range_mono hLR
  have hnonneg : ∀ d ∈ Finset.range R,
      0 ≤ cappedZipfDegreeMass a R d *
        (1 - hypergeometricGatewayMiss R M d) := by
    intro d hd
    exact mul_nonneg (cappedZipfDegreeMass_nonneg a R d hzpos)
      (sub_nonneg.mpr (hypergeometricGatewayMiss_nonneg_le_one
        R M d (Finset.mem_range.mp hd)).2)
  have hsum :
      (∑ d ∈ Finset.range L, cappedZipfDegreeMass a R d *
          (1 - hypergeometricGatewayMiss R M d)) ≤
        ∑ d ∈ Finset.range R, cappedZipfDegreeMass a R d *
          (1 - hypergeometricGatewayMiss R M d) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun d hdR hdL => hnonneg d hdR)
  rw [powerLawMoleculeGatewayHit_eq_sum a R M ha hR]
  exact htrunc.trans hsum

theorem cappedZipf_truncatedFirstMoment_eq_mean_mul_cdf
    (a : ℝ) (R L : Nat) (hL : 1 ≤ L) (hLR : L + 1 ≤ R)
    (hz : zipfNormalizer a ≠ 0)
    (hmean : windowZipfMean a R ≠ 0)
    (hdirect : windowDirectNumerator a R ≠ 0) :
    (∑ d ∈ Finset.range L,
      cappedZipfDegreeMass a R d * (d : ℝ)) =
      windowZipfMean a R * sizeBiasedLogCdf a R (L + 1) := by
  have hspec := specifiedEdgeDegreeMass_sum_range_eq_sizeBiasedLogCdf
    a R (L + 1) (by omega) hLR hz hdirect
  have hdiv :
      (∑ d ∈ Finset.range L,
        cappedZipfDegreeMass a R d * (d : ℝ)) /
          windowZipfMean a R =
        sizeBiasedLogCdf a R (L + 1) := by
    rw [show L + 1 - 1 = L by omega] at hspec
    rw [← hspec]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    dsimp [specifiedEdgeDegreeMass]
    ring
  apply (div_eq_iff hmean).mp at hdiv
  nlinarith

/-- The catalogue grows exponentially faster than the largest split block that
can occur at word length `n`.  This is the first half of the uniform-error
estimate; unlike a fixed-`M` limit it remains valid simultaneously for every
`M ≤ n`. -/
theorem nat_div_sourceReactionCount_tendsto_zero :
    Tendsto (fun n : Nat => (n : ℝ) / (sourceReactionCount n : ℝ))
      atTop (𝓝 0) := by
  have hupper := tendsto_pow_const_div_const_pow_of_one_lt 1
    (by norm_num : (1 : ℝ) < 2)
  have hupper' : Tendsto (fun n : Nat =>
      (n : ℝ) / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [pow_one] using hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ℝ)) atTop (𝓝 0))
    hupper'
  · filter_upwards with n
    positivity
  · filter_upwards [eventually_ge_atTop 4] with n hn
    have hpowNat : 2 ^ n ≤ sourceReactionCount n :=
      (sourceReactionCount_bounds hn).1
    have hpow : (2 : ℝ) ^ n ≤ (sourceReactionCount n : ℝ) := by
      exact_mod_cast hpowNat
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hpow

/-- A convenient real envelope for the finite-population quadratic error. -/
noncomputable def sourceSplitUniformErrorEnvelope (n : Nat) : ℝ :=
  4 * (((n : ℝ) ^ 2)⁻¹ +
    (n : ℝ) / (sourceReactionCount n : ℝ))

theorem sourceSplitUniformErrorEnvelope_tendsto_zero :
    Tendsto sourceSplitUniformErrorEnvelope atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : Nat => (1 : ℝ) / (n : ℝ))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hinvSq : Tendsto (fun n : Nat => (1 : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 0) := by
    have h := hinv.mul hinv
    simpa only [zero_mul, one_div] using h.congr' (by
      filter_upwards [eventually_ge_atTop 1] with n hn
      field_simp)
  have hsum := hinvSq.add nat_div_sourceReactionCount_tendsto_zero
  simpa [sourceSplitUniformErrorEnvelope] using hsum.const_mul 4

/-- Real-arithmetic core of the uniform finite-population estimate.  The
denominator hypothesis says that deleting any admissible block still leaves
at least half of the catalogue. -/
theorem quadraticRelativeError_le_envelope
    (R M L n D : ℝ) (hR : 0 < R) (hn : 0 < n)
    (hM0 : 0 ≤ M) (hMn : M ≤ n) (hL0 : 0 ≤ L)
    (hL : L ≤ R / n ^ 3 + 1) (hD : R / 2 ≤ D) :
    M * R * L / D ^ 2 ≤ 4 * (1 / n ^ 2 + n / R) := by
  have hD0 : 0 < D := lt_of_lt_of_le (half_pos hR) hD
  have hhalf0 : 0 < R / 2 := half_pos hR
  calc
    M * R * L / D ^ 2 ≤ M * R * L / (R / 2) ^ 2 := by
      apply div_le_div_of_nonneg_left
      · positivity
      · positivity
      · exact pow_le_pow_left₀ hhalf0.le hD 2
    _ ≤ n * R * (R / n ^ 3 + 1) / (R / 2) ^ 2 := by
      gcongr
    _ = 4 * (1 / n ^ 2 + n / R) := by
      field_simp
      all_goals ring

theorem source_split_relative_error_le_envelope
    {n M : Nat} (hn : 16 ≤ n) (hM0 : 0 < M) (hMn : M ≤ n) :
    (M : ℝ) * (sourceReactionCount n : ℝ) *
          (sourcePolynomialCutoff n - 1 : Nat) /
        ((sourceReactionCount n - M + 1 : Nat) : ℝ) ^ 2 ≤
      sourceSplitUniformErrorEnvelope n := by
  let R := sourceReactionCount n
  have hn0 : 0 < n := by omega
  have hRpoly : n ^ 4 ≤ R := by
    exact (fourth_pow_le_two_pow hn).trans
      (sourceReactionCount_bounds (by omega)).1
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity : 0 < n ^ 4) hRpoly
  have htwoM : 2 * M ≤ R := by
    have hn4 : 2 * n ≤ n ^ 4 := by
      have hcube : 2 ≤ n ^ 3 := by
        exact (by omega : 2 ≤ n).trans (by
          simpa only [pow_one] using
            (Nat.pow_le_pow_right (by omega : 0 < n) (by omega : 1 ≤ 3)))
      calc
        2 * n = n * 2 := by omega
        _ ≤ n * n ^ 3 := Nat.mul_le_mul_left n hcube
        _ = n ^ 4 := by ring
    omega
  have hD : (R : ℝ) / 2 ≤ ((R - M + 1 : Nat) : ℝ) := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    exact_mod_cast (show R ≤ (R - M + 1) * 2 by omega)
  have hL : ((sourcePolynomialCutoff n - 1 : Nat) : ℝ) ≤
      (R : ℝ) / (n : ℝ) ^ 3 + 1 := by
    have hdiv := Nat.cast_div_le (α := ℝ) (m := R) (n := n ^ 3)
    dsimp [sourcePolynomialCutoff, R] at hdiv ⊢
    norm_num at hdiv ⊢
    exact hdiv
  simpa [sourceSplitUniformErrorEnvelope, R] using
    quadraticRelativeError_le_envelope
      (R : ℝ) (M : ℝ) ((sourcePolynomialCutoff n - 1 : Nat) : ℝ)
      (n : ℝ) ((R - M + 1 : Nat) : ℝ)
      (by exact_mod_cast hR0) (by exact_mod_cast hn0) (by positivity)
      (by exact_mod_cast hMn) (by positivity) hL hD

/-- The worst-case retained linear hit rate after both truncations. -/
noncomputable def sourceSplitRetainedRate
    (lam : ℝ) (hlam : 0 < lam) (n : Nat) : ℝ :=
  ((sourceMoleculeCount n : ℝ) *
      windowZipfMean (calibrationExponent lam hlam n)
        (sourceReactionCount n) /
      (sourceReactionCount n : ℝ)) *
    sizeBiasedLogCdf (calibrationExponent lam hlam n)
      (sourceReactionCount n) (sourcePolynomialCutoff n) *
    (1 - sourceSplitUniformErrorEnvelope n)

theorem calibrated_sourceSplitRetainedRate_tendsto
    (lam : ℝ) (hlam : 0 < lam) :
    Tendsto (sourceSplitRetainedRate lam hlam) atTop (𝓝 lam) := by
  have hfirst := calibratedFirstMoment_scaled_tendsto lam hlam
  have htail := calibrated_sourcePolynomialCutoff_highTail lam hlam
  have hcdf : Tendsto (fun n : Nat =>
      sizeBiasedLogCdf (calibrationExponent lam hlam n)
        (sourceReactionCount n) (sourcePolynomialCutoff n)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : Nat => (1 : ℝ))
      atTop (𝓝 1)).sub htail
    simpa only [sub_zero, sub_sub_cancel] using h
  have hone : Tendsto (fun n : Nat =>
      1 - sourceSplitUniformErrorEnvelope n) atTop (𝓝 1) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : Nat => (1 : ℝ))
        atTop (𝓝 1)).sub sourceSplitUniformErrorEnvelope_tendsto_zero
  simpa [sourceSplitRetainedRate] using (hfirst.mul hcdf).mul hone

/-- The asymptotic retained rate is already a valid finite lower bound for
every split block of size at most `n`. -/
theorem source_truncated_hit_uniform_lower
    (a : ℝ) {n M : Nat} (hn : 16 ≤ n) (ha : 1 < a)
    (hM0 : 0 < M) (hMn : M ≤ n)
    (hmean : 0 < windowZipfMean a (sourceReactionCount n)) :
    ((M : ℝ) / (sourceReactionCount n : ℝ)) *
        (1 - sourceSplitUniformErrorEnvelope n) *
        (windowZipfMean a (sourceReactionCount n) *
          sizeBiasedLogCdf a (sourceReactionCount n)
            (sourcePolynomialCutoff n)) ≤
      powerLawMoleculeGatewayHit a (sourceReactionCount n) M := by
  let R := sourceReactionCount n
  let L := sourcePolynomialCutoff n - 1
  have hR2 : 2 ≤ R := by
    have hpow : 2 ≤ 2 ^ n := by
      exact (by norm_num : 2 ≤ 2 ^ 1).trans
        (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : 1 ≤ n))
    exact hpow.trans (sourceReactionCount_bounds (by omega)).1
  have hMR : M ≤ R := by
    have hpoly : n ^ 4 ≤ R :=
      (fourth_pow_le_two_pow hn).trans
        (sourceReactionCount_bounds (by omega)).1
    exact hMn.trans (by
      have : n ≤ n ^ 4 := by
        simpa only [pow_one] using
          (Nat.pow_le_pow_right (by omega : 0 < n) (by omega : 1 ≤ 4))
      exact this.trans hpoly)
  have hcut : sourcePolynomialCutoff n ≤ R :=
    sourcePolynomialCutoff_le_sourceReactionCount (by omega)
  have hLR : L ≤ R := by omega
  have hzpos : 0 < zipfNormalizer a := by
    rw [zipfNormalizer_eq_prefix_add_tail ha 2, zipfPrefix_two ha]
    nlinarith [rpowTail_nonneg a 2]
  have hdirect : windowDirectNumerator a R ≠ 0 := by
    intro hd
    have := hmean
    simp [windowZipfMean, R, hd] at this
  have hsumEq := cappedZipf_truncatedFirstMoment_eq_mean_mul_cdf
    a R L (by simp [L, sourcePolynomialCutoff]) (by simpa [L] using hcut)
    hzpos.ne' hmean.ne' hdirect
  have hsum0 : 0 ≤ ∑ d ∈ Finset.range L,
      cappedZipfDegreeMass a R d * (d : ℝ) := by
    apply Finset.sum_nonneg
    intro d hd
    exact mul_nonneg (cappedZipfDegreeMass_nonneg a R d hzpos)
      (by positivity)
  have herr := source_split_relative_error_le_envelope hn hM0 hMn
  have hfinite := powerLawMoleculeGatewayHit_ge_truncatedFirstMoment
    a R M L ha hR2 hM0 hMR hLR
  have hR0 : (0 : ℝ) < R := by positivity
  have hD0 : (0 : ℝ) < ((R - M + 1 : Nat) : ℝ) := by positivity
  calc
    ((M : ℝ) / (sourceReactionCount n : ℝ)) *
        (1 - sourceSplitUniformErrorEnvelope n) *
        (windowZipfMean a (sourceReactionCount n) *
          sizeBiasedLogCdf a (sourceReactionCount n)
            (sourcePolynomialCutoff n)) =
      ((M : ℝ) / (R : ℝ)) *
        (1 - sourceSplitUniformErrorEnvelope n) *
        (∑ d ∈ Finset.range L,
          cappedZipfDegreeMass a R d * (d : ℝ)) := by
            rw [hsumEq]
            rfl
    _ ≤ ((M : ℝ) / (R : ℝ)) *
        (1 - ((M : ℝ) * (R : ℝ) * (L : ℝ) /
          ((R - M + 1 : Nat) : ℝ) ^ 2)) *
        (∑ d ∈ Finset.range L,
          cappedZipfDegreeMass a R d * (d : ℝ)) := by
            have hfac : 0 ≤ (M : ℝ) / (R : ℝ) := by positivity
            gcongr
    _ = ((M : ℝ) / (R : ℝ) -
        ((M : ℝ) / ((R - M + 1 : Nat) : ℝ)) ^ 2 * (L : ℝ)) *
        (∑ d ∈ Finset.range L,
          cappedZipfDegreeMass a R d * (d : ℝ)) := by
            field_simp
    _ ≤ powerLawMoleculeGatewayHit a R M := hfinite

theorem sourceSplitRetainedRate_mul_card_le_scaled_hit
    (lam : ℝ) (hlam : 0 < lam) {n M : Nat} (hn : 16 ≤ n)
    (ha : 1 < calibrationExponent lam hlam n)
    (hM0 : 0 < M) (hMn : M ≤ n)
    (hmean : 0 < windowZipfMean (calibrationExponent lam hlam n)
      (sourceReactionCount n)) :
    (M : ℝ) * sourceSplitRetainedRate lam hlam n ≤
      (sourceMoleculeCount n : ℝ) *
        powerLawMoleculeGatewayHit (calibrationExponent lam hlam n)
          (sourceReactionCount n) M := by
  have h := source_truncated_hit_uniform_lower
    (calibrationExponent lam hlam n) hn ha hM0 hMn hmean
  have hX : (0 : ℝ) ≤ sourceMoleculeCount n := by positivity
  calc
    (M : ℝ) * sourceSplitRetainedRate lam hlam n =
        (sourceMoleculeCount n : ℝ) *
          (((M : ℝ) / (sourceReactionCount n : ℝ)) *
            (1 - sourceSplitUniformErrorEnvelope n) *
            (windowZipfMean (calibrationExponent lam hlam n)
                (sourceReactionCount n) *
              sizeBiasedLogCdf (calibrationExponent lam hlam n)
                (sourceReactionCount n) (sourcePolynomialCutoff n))) := by
      dsimp [sourceSplitRetainedRate]
      ring
    _ ≤ (sourceMoleculeCount n : ℝ) *
        powerLawMoleculeGatewayHit (calibrationExponent lam hlam n)
          (sourceReactionCount n) M := mul_le_mul_of_nonneg_left h hX

theorem eventually_calibrated_scaled_gatewayHit_ge_linear
    (lam c : ℝ) (hlam : 0 < lam) (hc : c < lam) :
    ∀ᶠ n : Nat in atTop, ∀ M : Nat, 0 < M → M ≤ n →
      c * (M : ℝ) ≤
        (sourceMoleculeCount n : ℝ) *
          powerLawMoleculeGatewayHit (calibrationExponent lam hlam n)
            (sourceReactionCount n) M := by
  have hrate : ∀ᶠ n : Nat in atTop, c < sourceSplitRetainedRate lam hlam n :=
    (calibrated_sourceSplitRetainedRate_tendsto lam hlam)
      (Ioi_mem_nhds hc)
  have ha : ∀ᶠ n : Nat in atTop, 1 < calibrationExponent lam hlam n :=
    (calibrationExponent_tendsto_two lam hlam) (Ioi_mem_nhds one_lt_two)
  filter_upwards [eventually_ge_atTop 16, hrate, ha,
    eventually_calibrationExponent_exact lam hlam] with n hn hcn han hex
  intro M hM0 hMn
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hmean : 0 < windowZipfMean (calibrationExponent lam hlam n)
      (sourceReactionCount n) := by
    have heq := (div_eq_iff hnreal.ne').mp hex
    rw [heq]
    positivity
  calc
    c * (M : ℝ) ≤ sourceSplitRetainedRate lam hlam n * (M : ℝ) :=
      mul_le_mul_of_nonneg_right hcn.le (by positivity)
    _ = (M : ℝ) * sourceSplitRetainedRate lam hlam n := by ring
    _ ≤ (sourceMoleculeCount n : ℝ) *
          powerLawMoleculeGatewayHit (calibrationExponent lam hlam n)
            (sourceReactionCount n) M :=
      sourceSplitRetainedRate_mul_card_le_scaled_hit
        lam hlam hn han hM0 hMn hmean

theorem eventually_calibrated_splitBlockMiss_le_exp
    (lam c : ℝ) (hlam : 0 < lam) (hc : c < lam) :
    ∀ᶠ n : Nat in atTop, ∀ M : Nat, 0 < M → M ≤ n →
      (coverageMissProfile
          (cappedZipfDegreeMass (calibrationExponent lam hlam n)
            (sourceReactionCount n))
          (sourceReactionCount n) M) ^ sourceMoleculeCount n ≤
        Real.exp (-c * (M : ℝ)) := by
  have hscaled := eventually_calibrated_scaled_gatewayHit_ge_linear
    lam c hlam hc
  have ha : ∀ᶠ n : Nat in atTop, 1 < calibrationExponent lam hlam n :=
    (calibrationExponent_tendsto_two lam hlam) (Ioi_mem_nhds one_lt_two)
  filter_upwards [eventually_ge_atTop 16, hscaled, ha] with n hn hlin han
  intro M hM0 hMn
  let p := powerLawMoleculeGatewayHit (calibrationExponent lam hlam n)
    (sourceReactionCount n) M
  have hR2 : 2 ≤ sourceReactionCount n := by
    have hpow : 2 ≤ 2 ^ n := by
      exact (by norm_num : 2 ≤ 2 ^ 1).trans
        (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : 1 ≤ n))
    exact hpow.trans (sourceReactionCount_bounds (by omega)).1
  have hp := powerLawMoleculeGatewayHit_nonneg_le_one
    (calibrationExponent lam hlam n) (sourceReactionCount n) M han hR2
  have hpow := one_sub_pow_le_exp_neg_mul p (sourceMoleculeCount n) hp.2
  have hexp : Real.exp ((sourceMoleculeCount n : ℝ) * (-p)) ≤
      Real.exp (-c * (M : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have := hlin M hM0 hMn
    dsimp [p] at this ⊢
    linarith
  rw [powerLawCoverageMissProfile_eq]
  have hmiss : powerLawMoleculeGatewayMiss (calibrationExponent lam hlam n)
      (sourceReactionCount n) M = 1 - p := by
    dsimp [p, powerLawMoleculeGatewayHit]
    ring
  rw [hmiss]
  exact hpow.trans hexp

end PowerLawSmallRAF

import proofs.PowerLawSmallRAF.GatewayHighTail

namespace PowerLawSmallRAF

open Filter Topology

/-- The tilted-harmonic mass of the half-open mark band `[m,R)`. -/
noncomputable def tiltedHarmonicBand
    (p : ℝ) (m R : Nat) : ℝ :=
  ∑ k ∈ Finset.Ico m R, (k : ℝ) ^ (-p)

theorem tiltedHarmonicBand_eq_sub (p : ℝ) (m R : Nat)
    (hm : 1 ≤ m) (hmR : m ≤ R) :
    tiltedHarmonicBand p m R =
      tiltedHarmonic p R - tiltedHarmonic p m := by
  rw [tiltedHarmonicBand, tiltedHarmonic, tiltedHarmonic,
    ← Finset.sum_Ico_consecutive (fun k : Nat => (k : ℝ) ^ (-p)) hm hmR]
  ring_nf

/-- Every band whose two endpoints have the source exponential rate has
vanishing normalized mass in a fixed nonzero critical window. -/
theorem explicitWindow_endpointBand_normalized
    (m : Nat → Nat) (B : ℝ) (hB : 0 < B)
    (hlog : Tendsto (fun n : Nat => Real.log (m n : ℝ) / (n : ℝ))
      atTop (𝓝 (Real.log 2)))
    (hm : Tendsto m atTop atTop)
    (hmR : ∀ᶠ n : Nat in atTop, m n ≤ sourceReactionCount n) :
    Tendsto (fun n : Nat =>
      tiltedHarmonicBand (1 - B / (n : ℝ)) (m n)
        (sourceReactionCount n) / (n : ℝ)) atTop (𝓝 0) := by
  have hsource := movingTiltedHarmonic_window_normalized_of_ne_zero
    sourceReactionCount (-B) (Real.log 2) (neg_ne_zero.mpr (ne_of_gt hB))
    log_sourceReactionCount_normalized sourceReactionCount_tendsto_atTop
  have hmoving := movingTiltedHarmonic_window_normalized_of_ne_zero
    m (-B) (Real.log 2) (neg_ne_zero.mpr (ne_of_gt hB)) hlog hm
  have hdiff := hsource.sub hmoving
  have hzero :
      (1 - Real.exp (-(-B) * Real.log 2)) / (-B) -
        (1 - Real.exp (-(-B) * Real.log 2)) / (-B) = 0 := by ring
  have hlimit : Tendsto (fun n : Nat =>
      tiltedHarmonic (1 + (-B) / (n : ℝ)) (sourceReactionCount n) /
          (n : ℝ) -
        tiltedHarmonic (1 + (-B) / (n : ℝ)) (m n) / (n : ℝ))
      atTop (𝓝 0) := by
    simpa only [hzero] using hdiff
  apply hlimit.congr'
  filter_upwards [eventually_ge_atTop 1,
    hm.eventually (eventually_ge_atTop 1), hmR] with n hn hmn hle
  rw [tiltedHarmonicBand_eq_sub (1 - B / (n : ℝ)) (m n)
    (sourceReactionCount n) hmn hle]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hn0]
  ring_nf

/-- The exact calibrated tilted band is dominated by one fixed explicit
window because the calibrated window coordinate is uniformly bounded. -/
theorem calibrated_endpointBand_normalized
    (lam : ℝ) (hlam : 0 < lam) (m : Nat → Nat)
    (hlog : Tendsto (fun n : Nat => Real.log (m n : ℝ) / (n : ℝ))
      atTop (𝓝 (Real.log 2)))
    (hm : Tendsto m atTop atTop)
    (hmR : ∀ᶠ n : Nat in atTop, m n ≤ sourceReactionCount n) :
    Tendsto (fun n : Nat =>
      tiltedHarmonicBand (calibrationExponent lam hlam n - 1) (m n)
        (sourceReactionCount n) / (n : ℝ)) atTop (𝓝 0) := by
  let B : ℝ :=
    |criticalLambdaInv (⟨lam, hlam⟩ : Set.Ioi (0 : ℝ))| + 1
  have hB : 0 < B := by
    have habs : 0 ≤
        |criticalLambdaInv (⟨lam, hlam⟩ : Set.Ioi (0 : ℝ))| := abs_nonneg _
    dsimp [B]
    linarith
  have hupper := explicitWindow_endpointBand_normalized m B hB hlog hm hmR
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ℝ)) atTop (𝓝 0)) hupper
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_nonneg (Finset.sum_nonneg fun _ _ =>
      Real.rpow_nonneg (by positivity) _) (by positivity)
  · filter_upwards [eventually_ge_atTop 1,
      hm.eventually (eventually_ge_atTop 1)] with n hn hmn
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply Finset.sum_le_sum
    intro k hk
    have hkone : (1 : ℝ) ≤ (k : ℝ) := by
      have hkm := (Finset.mem_Ico.mp hk).1
      exact_mod_cast hmn.trans hkm
    apply Real.rpow_le_rpow_of_exponent_le hkone
    have hcoord : |calibrationB lam hlam n| ≤ B := by
      simpa only [B] using calibrationB_abs_le lam hlam n
    have hlower : -B ≤ calibrationB lam hlam n := by
      linarith [neg_abs_le (calibrationB lam hlam n)]
    dsimp [calibrationExponent]
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hdiv := div_le_div_of_nonneg_right hlower hnreal.le
    have hneg := neg_le_neg hdiv
    have hadd := add_le_add_left hneg (-1)
    convert hadd using 1 <;> ring_nf

/-- Unnormalised conditional degree mass at marks at least `m`. -/
noncomputable def windowHighNumerator (a : ℝ) (R m : Nat) : ℝ :=
  windowDirectNumerator a R - windowPartialNumerator a m

theorem windowHighNumerator_eq (a : ℝ) (R m : Nat)
    (hm : 2 ≤ m) (hmR : m ≤ R) :
    windowHighNumerator a R m =
      (∑ k ∈ Finset.Ico m R,
        (((k - 1 : Nat) : ℝ) * (k : ℝ) ^ (-a))) +
        cappedRpowTail a R := by
  rw [windowHighNumerator, windowDirectNumerator, windowPartialNumerator,
    ← Finset.sum_Ico_consecutive
      (fun k : Nat => (((k - 1 : Nat) : ℝ) * (k : ℝ) ^ (-a))) hm hmR]
  ring

theorem windowHighNumerator_nonneg (a : ℝ) (R m : Nat)
    (hm : 2 ≤ m) (hmR : m ≤ R) :
    0 ≤ windowHighNumerator a R m := by
  rw [windowHighNumerator_eq a R m hm hmR]
  exact add_nonneg (Finset.sum_nonneg fun k _ =>
    mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _))
    (cappedRpowTail_nonneg a R)

theorem windowHighNumerator_le_band_add_cap (a : ℝ) (R m : Nat)
    (hm : 2 ≤ m) (hmR : m ≤ R) :
    windowHighNumerator a R m ≤
      tiltedHarmonicBand (a - 1) m R + cappedRpowTail a R := by
  rw [windowHighNumerator_eq a R m hm hmR, tiltedHarmonicBand]
  have hsum :
      (∑ k ∈ Finset.Ico m R,
        (((k - 1 : Nat) : ℝ) * (k : ℝ) ^ (-a))) ≤
      ∑ k ∈ Finset.Ico m R, (k : ℝ) ^ (-(a - 1)) := by
    apply Finset.sum_le_sum
    intro k hk
    have hk1 : 1 ≤ k := by
      have hmk := (Finset.mem_Ico.mp hk).1
      omega
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hk1)
    have hmul : (k : ℝ) * (k : ℝ) ^ (-a) =
        (k : ℝ) ^ (-(a - 1)) := by
      calc
        (k : ℝ) * (k : ℝ) ^ (-a) =
            (k : ℝ) ^ (1 : ℝ) * (k : ℝ) ^ (-a) := by rw [Real.rpow_one]
        _ = (k : ℝ) ^ ((1 : ℝ) + (-a)) :=
          (Real.rpow_add hkpos 1 (-a)).symm
        _ = (k : ℝ) ^ (-(a - 1)) := by ring_nf
    calc
      ((k - 1 : Nat) : ℝ) * (k : ℝ) ^ (-a) ≤
          (k : ℝ) * (k : ℝ) ^ (-a) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast Nat.sub_le k 1
        · exact Real.rpow_nonneg (by positivity) _
      _ = (k : ℝ) ^ (-(a - 1)) := hmul
  linarith

/-- The capped endpoint atom is negligible on the `n` scale under exact
finite calibration. -/
theorem calibrated_cappedRpowTail_normalized
    (lam : ℝ) (hlam : 0 < lam) :
    Tendsto (fun n : Nat =>
      cappedRpowTail (calibrationExponent lam hlam n)
        (sourceReactionCount n) / (n : ℝ)) atTop (𝓝 0) := by
  let b₀ := criticalLambdaInv (⟨lam, hlam⟩ : Set.Ioi (0 : ℝ))
  have hb : Tendsto (fun n : Nat =>
      (n : ℝ) * (calibrationExponent lam hlam n - 2)) atTop (𝓝 b₀) := by
    apply (calibrationB_tendsto_inverse lam hlam).congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    dsimp [calibrationExponent]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    field_simp [hn0]
    ring
  have htail := movingRpowTail (calibrationExponent lam hlam)
    sourceReactionCount b₀ (Real.log 2)
    (calibrationExponent_tendsto_two lam hlam) hb
    log_sourceReactionCount_normalized sourceReactionCount_tendsto_atTop
  have hupper := htail.div_atTop
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ℝ)) atTop (𝓝 0)) hupper
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_nonneg (cappedRpowTail_nonneg _ _) (by positivity)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    apply div_le_div_of_nonneg_right _ (by positivity)
    dsimp [cappedRpowTail]
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast Nat.sub_le (sourceReactionCount n) 1
    · exact rpowTail_nonneg _ _

/-- The actual unnormalised size-biased endpoint tail is negligible at exact
finite calibration. -/
theorem calibrated_windowHighNumerator_normalized
    (lam : ℝ) (hlam : 0 < lam) (m : Nat → Nat)
    (hlog : Tendsto (fun n : Nat => Real.log (m n : ℝ) / (n : ℝ))
      atTop (𝓝 (Real.log 2)))
    (hm : Tendsto m atTop atTop)
    (hmR : ∀ᶠ n : Nat in atTop, m n ≤ sourceReactionCount n) :
    Tendsto (fun n : Nat =>
      windowHighNumerator (calibrationExponent lam hlam n)
        (sourceReactionCount n) (m n) / (n : ℝ)) atTop (𝓝 0) := by
  have hband := calibrated_endpointBand_normalized lam hlam m hlog hm hmR
  have hcap := calibrated_cappedRpowTail_normalized lam hlam
  have hupper : Tendsto (fun n : Nat =>
      tiltedHarmonicBand (calibrationExponent lam hlam n - 1) (m n)
          (sourceReactionCount n) / (n : ℝ) +
        cappedRpowTail (calibrationExponent lam hlam n)
          (sourceReactionCount n) / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [add_zero] using hband.add hcap
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ℝ)) atTop (𝓝 0)) hupper
  · filter_upwards [eventually_ge_atTop 1,
      hm.eventually (eventually_ge_atTop 2), hmR] with n hn hmn hle
    exact div_nonneg
      (windowHighNumerator_nonneg _ _ _ hmn hle) (by positivity)
  · filter_upwards [eventually_ge_atTop 1,
      hm.eventually (eventually_ge_atTop 2), hmR] with n hn hmn hle
    calc
      windowHighNumerator (calibrationExponent lam hlam n)
          (sourceReactionCount n) (m n) / (n : ℝ) ≤
          (tiltedHarmonicBand (calibrationExponent lam hlam n - 1) (m n)
            (sourceReactionCount n) +
            cappedRpowTail (calibrationExponent lam hlam n)
              (sourceReactionCount n)) / (n : ℝ) :=
        div_le_div_of_nonneg_right
          (windowHighNumerator_le_band_add_cap _ _ _ hmn hle) (by positivity)
      _ = tiltedHarmonicBand (calibrationExponent lam hlam n - 1) (m n)
            (sourceReactionCount n) / (n : ℝ) +
          cappedRpowTail (calibrationExponent lam hlam n)
            (sourceReactionCount n) / (n : ℝ) := by ring

/-- Exact finite calibration makes the total size-biased numerator linear in
`n`, with a strictly positive limit. -/
theorem calibrated_windowDirectNumerator_normalized
    (lam : ℝ) (hlam : 0 < lam) :
    Tendsto (fun n : Nat =>
      windowDirectNumerator (calibrationExponent lam hlam n)
        (sourceReactionCount n) / (n : ℝ)) atTop
      (𝓝 (lam * (Real.pi ^ 2 / 6))) := by
  have hmean : Tendsto (fun n : Nat =>
      windowZipfMean (calibrationExponent lam hlam n)
        (sourceReactionCount n) / (n : ℝ)) atTop (𝓝 lam) := by
    apply (tendsto_const_nhds : Tendsto (fun _ : Nat => lam) atTop (𝓝 lam)).congr'
    filter_upwards [eventually_calibrationExponent_exact lam hlam] with n hn
    exact hn.symm
  have hnormalizer : Tendsto (fun n : Nat =>
      zipfNormalizer (calibrationExponent lam hlam n)) atTop
      (𝓝 (Real.pi ^ 2 / 6)) := by
    have h := (continuousAt_zipfNormalizer one_lt_two).tendsto.comp
      (calibrationExponent_tendsto_two lam hlam)
    simpa only [zipfNormalizer_two] using h
  have hproduct := hmean.mul hnormalizer
  apply hproduct.congr'
  have hdenpos : ∀ᶠ n : Nat in atTop,
      0 < zipfNormalizer (calibrationExponent lam hlam n) :=
    hnormalizer (Ioi_mem_nhds (by positivity : 0 < Real.pi ^ 2 / 6))
  filter_upwards [eventually_ge_atTop 1, hdenpos] with n hn hden
  dsimp [windowZipfMean]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hn0, ne_of_gt hden]

/-- Under the exact source calibration, conditioning on one specified
catalytic edge still puts asymptotically zero mass above every threshold whose
logarithm has the catalogue endpoint rate. -/
theorem calibrated_sizeBiasedHighTail
    (lam : ℝ) (hlam : 0 < lam) (m : Nat → Nat)
    (hlog : Tendsto (fun n : Nat => Real.log (m n : ℝ) / (n : ℝ))
      atTop (𝓝 (Real.log 2)))
    (hm : Tendsto m atTop atTop)
    (hmR : ∀ᶠ n : Nat in atTop, m n ≤ sourceReactionCount n) :
    Tendsto (fun n : Nat => 1 -
      sizeBiasedLogCdf (calibrationExponent lam hlam n)
        (sourceReactionCount n) (m n)) atTop (𝓝 0) := by
  have hhigh := calibrated_windowHighNumerator_normalized
    lam hlam m hlog hm hmR
  have htotal := calibrated_windowDirectNumerator_normalized lam hlam
  have hlimitne : lam * (Real.pi ^ 2 / 6) ≠ 0 := by positivity
  have hquot := hhigh.div htotal hlimitne
  have hquot0 : Tendsto
      ((fun n : Nat => windowHighNumerator (calibrationExponent lam hlam n)
          (sourceReactionCount n) (m n) / (n : ℝ)) /
        (fun n : Nat => windowDirectNumerator (calibrationExponent lam hlam n)
          (sourceReactionCount n) / (n : ℝ))) atTop (𝓝 0) := by
    simpa only [zero_div] using hquot
  apply hquot0.congr'
  have htotalpos : ∀ᶠ n : Nat in atTop,
      0 < windowDirectNumerator (calibrationExponent lam hlam n)
        (sourceReactionCount n) / (n : ℝ) :=
    htotal (Ioi_mem_nhds (mul_pos hlam (by positivity)))
  filter_upwards [eventually_ge_atTop 1, htotalpos] with n hn hpos
  dsimp [sizeBiasedLogCdf, windowHighNumerator]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have htotalne : windowDirectNumerator (calibrationExponent lam hlam n)
      (sourceReactionCount n) ≠ 0 := by
    intro hzero
    rw [hzero, zero_div] at hpos
    exact (lt_irrefl 0) hpos
  field_simp [hn0, htotalne]

end PowerLawSmallRAF

import proofs.PowerLawSmallRAF.FiniteCalibration

namespace PowerLawSmallRAF

open Filter Topology

/-- The lower half of the integral sandwich for a moving power-law tail. -/
theorem rpowTail_ge_integral (a : ℝ) (ha : 1 < a) (R : Nat) (hR : 1 ≤ R) :
    (R : ℝ) ^ (1 - a) / (a - 1) ≤ rpowTail a R := by
  have hs : Summable (fun j : Nat => (((j + R : Nat) : ℝ) ^ (-a))) := by
    exact (summable_nat_add_iff R).2
      (Real.summable_nat_rpow.mpr (by linarith : -a < -1))
  have hfinite : ∀ B : Nat, R ≤ B →
      (∫ x in (R : ℝ)..(B : ℝ), x ^ (-a)) ≤ rpowTail a R := by
    intro B hRB
    have hf : AntitoneOn (fun x : ℝ => x ^ (-a))
        (Set.Icc (R : ℝ) (B : ℝ)) := by
      apply (Real.strictAntiOn_rpow_Ioi_of_exponent_neg (by linarith)).antitoneOn.mono
      intro x hx
      have hRpos : (0 : ℝ) < R := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR)
      exact Set.mem_Ioi.mpr (hRpos.trans_le hx.1)
    have hint := hf.integral_le_sum_Ico hRB
    have hsum :
        (∑ j ∈ Finset.Ico R B, (j : ℝ) ^ (-a)) ≤ rpowTail a R := by
      rw [rpowTail]
      have hreindex :
          (∑ j ∈ Finset.Ico R B, (j : ℝ) ^ (-a)) =
            ∑ j ∈ Finset.range (B - R), (((j + R : Nat) : ℝ) ^ (-a)) := by
        rw [Finset.range_eq_Ico,
          Finset.sum_Ico_add' (fun j : Nat => (j : ℝ) ^ (-a))
            0 (B - R) (c := R)]
        simp only [Nat.zero_add, Nat.sub_add_cancel hRB]
      rw [hreindex]
      exact hs.sum_le_tsum (Finset.range (B - R))
        (fun _ _ => Real.rpow_nonneg (by positivity) _)
    exact hint.trans hsum
  have hpow : Tendsto (fun B : Nat => (B : ℝ) ^ (1 - a)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (sub_pos.mpr ha)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [neg_sub] using h
  have hleft : Tendsto (fun B : Nat =>
      ((R : ℝ) ^ (1 - a) - (B : ℝ) ^ (1 - a)) / (a - 1)) atTop
      (𝓝 ((R : ℝ) ^ (1 - a) / (a - 1))) := by
    simpa only [sub_zero] using
      ((tendsto_const_nhds.sub hpow).div_const (a - 1))
  apply le_of_tendsto hleft
  filter_upwards [eventually_ge_atTop R] with B hRB
  have hden : a - 1 ≠ 0 := by linarith
  have hzero : (0 : ℝ) ∉ Set.uIcc (R : ℝ) (B : ℝ) := by
    rw [Set.uIcc_of_le (by exact_mod_cast hRB)]
    simp only [Set.mem_Icc, not_and_or, not_le]
    exact Or.inl (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR))
  have hr : -a ≠ -1 := by linarith
  have hden' : 1 - a ≠ 0 := by linarith
  have heq :
      ((R : ℝ) ^ (1 - a) - (B : ℝ) ^ (1 - a)) / (a - 1) =
        ∫ x in (R : ℝ)..(B : ℝ), x ^ (-a) := by
    rw [integral_rpow (Or.inr ⟨hr, hzero⟩)]
    rw [show -a + 1 = 1 - a by ring]
    rw [show (B : ℝ) ^ (1 - a) - (R : ℝ) ^ (1 - a) =
      -((R : ℝ) ^ (1 - a) - (B : ℝ) ^ (1 - a)) by ring]
    rw [show 1 - a = -(a - 1) by ring]
    exact (neg_div_neg_eq _ _).symm
  rw [heq]
  exact hfinite B hRB

/-- The integral main term at a moving threshold.  The two inputs which matter
are the critical-window coordinate and the exponential growth rate of the
threshold. -/
theorem movingRpowMainTerm
    (a : Nat → ℝ) (m : Nat → Nat) (b ell : ℝ)
    (ha : Tendsto a atTop (𝓝 2))
    (hb : Tendsto (fun n : Nat => (n : ℝ) * (a n - 2)) atTop (𝓝 b))
    (hlog : Tendsto (fun n : Nat => Real.log (m n : ℝ) / (n : ℝ))
      atTop (𝓝 ell))
    (hmpos : ∀ᶠ n : Nat in atTop, 0 < m n) :
    Tendsto (fun n : Nat =>
      (m n : ℝ) ^ (2 - a n) / (a n - 1)) atTop
      (𝓝 (Real.exp (-b * ell))) := by
  have hprod : Tendsto (fun n : Nat =>
      (-((n : ℝ) * (a n - 2))) *
        (Real.log (m n : ℝ) / (n : ℝ))) atTop (𝓝 (-b * ell)) := by
    simpa only [neg_mul] using hb.neg.mul hlog
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hprod
  have hrpow : Tendsto (fun n : Nat => (m n : ℝ) ^ (2 - a n))
      atTop (𝓝 (Real.exp (-b * ell))) := by
    apply hexp.congr'
    filter_upwards [eventually_ge_atTop 1, hmpos] with n hn hmn
    rw [Real.rpow_def_of_pos (by exact_mod_cast hmn)]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    apply congrArg Real.exp
    field_simp [hn0]
    ring
  have hden : Tendsto (fun n : Nat => a n - 1) atTop (𝓝 1) := by
    convert ha.sub_const 1 using 1
    norm_num
  simpa only [div_one] using hrpow.div hden one_ne_zero

theorem mul_rpowTail_bounds (a : ℝ) (ha : 1 < a) (R : Nat) (hR : 1 ≤ R) :
    (R : ℝ) ^ (2 - a) / (a - 1) ≤ (R : ℝ) * rpowTail a R ∧
      (R : ℝ) * rpowTail a R ≤
        (R : ℝ) ^ (1 - a) + (R : ℝ) ^ (2 - a) / (a - 1) := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR)
  have hmul1 : (R : ℝ) * (R : ℝ) ^ (-a) = (R : ℝ) ^ (1 - a) := by
    calc
      (R : ℝ) * (R : ℝ) ^ (-a) = (R : ℝ) ^ (1 : ℝ) * (R : ℝ) ^ (-a) := by
        rw [Real.rpow_one]
      _ = (R : ℝ) ^ ((1 : ℝ) + (-a)) := (Real.rpow_add hRpos 1 (-a)).symm
      _ = (R : ℝ) ^ (1 - a) := by ring_nf
  have hmul2 : (R : ℝ) * (R : ℝ) ^ (1 - a) = (R : ℝ) ^ (2 - a) := by
    calc
      (R : ℝ) * (R : ℝ) ^ (1 - a) =
          (R : ℝ) ^ (1 : ℝ) * (R : ℝ) ^ (1 - a) := by rw [Real.rpow_one]
      _ = (R : ℝ) ^ ((1 : ℝ) + (1 - a)) :=
        (Real.rpow_add hRpos 1 (1 - a)).symm
      _ = (R : ℝ) ^ (2 - a) := by ring_nf
  constructor
  · rw [← hmul2, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (rpowTail_ge_integral a ha R hR) hRpos.le
  · calc
      (R : ℝ) * rpowTail a R ≤ (R : ℝ) *
          ((R : ℝ) ^ (-a) + (R : ℝ) ^ (1 - a) / (a - 1)) :=
        mul_le_mul_of_nonneg_left (rpowTail_le a ha R hR) hRpos.le
      _ = (R : ℝ) ^ (1 - a) + (R : ℝ) ^ (2 - a) / (a - 1) := by
        rw [mul_add, hmul1, ← mul_div_assoc, hmul2]

theorem movingRpowHeadTerm (a : Nat → ℝ) (m : Nat → Nat)
    (ha : Tendsto a atTop (𝓝 2)) (hm : Tendsto m atTop atTop) :
    Tendsto (fun n : Nat => (m n : ℝ) ^ (1 - a n)) atTop (𝓝 0) := by
  have hmreal : Tendsto (fun n : Nat => (m n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp hm
  have hfixed : Tendsto (fun n : Nat => (m n : ℝ) ^ (-(1 / 2 : ℝ)))
      atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hmreal
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ℝ)) atTop (𝓝 0)) hfixed
  · filter_upwards with n
    exact Real.rpow_nonneg (by positivity) _
  · have haev : ∀ᶠ n : Nat in atTop, (3 / 2 : ℝ) < a n :=
      ha (Ioi_mem_nhds (by norm_num))
    filter_upwards [haev, (hm.eventually (eventually_ge_atTop 1))] with n han hmn
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hmn) (by linarith)

/-- Uniform moving-threshold asymptotic for the unnormalised Zipf tail. -/
theorem movingRpowTail
    (a : Nat → ℝ) (m : Nat → Nat) (b ell : ℝ)
    (ha : Tendsto a atTop (𝓝 2))
    (hb : Tendsto (fun n : Nat => (n : ℝ) * (a n - 2)) atTop (𝓝 b))
    (hlog : Tendsto (fun n : Nat => Real.log (m n : ℝ) / (n : ℝ))
      atTop (𝓝 ell))
    (hm : Tendsto m atTop atTop) :
    Tendsto (fun n : Nat => (m n : ℝ) * rpowTail (a n) (m n))
      atTop (𝓝 (Real.exp (-b * ell))) := by
  have hmpos : ∀ᶠ n : Nat in atTop, 0 < m n :=
    hm.eventually (eventually_gt_atTop 0)
  have hmain := movingRpowMainTerm a m b ell ha hb hlog hmpos
  have hhead := movingRpowHeadTerm a m ha hm
  have hupper : Tendsto (fun n : Nat =>
      (m n : ℝ) ^ (1 - a n) + (m n : ℝ) ^ (2 - a n) / (a n - 1))
      atTop (𝓝 (Real.exp (-b * ell))) := by
    simpa only [zero_add] using hhead.add hmain
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hmain hupper
  · have haev : ∀ᶠ n : Nat in atTop, 1 < a n := ha (Ioi_mem_nhds (by norm_num))
    filter_upwards [haev, hmpos] with n han hmn
    exact (mul_rpowTail_bounds (a n) han (m n) hmn).1
  · have haev : ∀ᶠ n : Nat in atTop, 1 < a n := ha (Ioi_mem_nhds (by norm_num))
    filter_upwards [haev, hmpos] with n han hmn
    exact (mul_rpowTail_bounds (a n) han (m n) hmn).2

/-- Normalized form for the actual Zipf law. -/
theorem movingZipfTail
    (a : Nat → ℝ) (m : Nat → Nat) (b ell : ℝ)
    (ha : Tendsto a atTop (𝓝 2))
    (hb : Tendsto (fun n : Nat => (n : ℝ) * (a n - 2)) atTop (𝓝 b))
    (hlog : Tendsto (fun n : Nat => Real.log (m n : ℝ) / (n : ℝ))
      atTop (𝓝 ell))
    (hm : Tendsto m atTop atTop) :
    Tendsto (fun n : Nat => (m n : ℝ) * zipfTailRatio (a n) (m n))
      atTop (𝓝 (Real.exp (-b * ell) / (Real.pi ^ 2 / 6))) := by
  have htail := movingRpowTail a m b ell ha hb hlog hm
  have hden : Tendsto (fun n : Nat => zipfNormalizer (a n)) atTop
      (𝓝 (Real.pi ^ 2 / 6)) := by
    simpa only [zipfNormalizer_two] using
      (continuousAt_zipfNormalizer one_lt_two).tendsto.comp ha
  have hquot := htail.div hden (by positivity : Real.pi ^ 2 / 6 ≠ 0)
  apply hquot.congr'
  filter_upwards with n
  dsimp [zipfTailRatio]
  ring

/-- Number of nonempty binary molecules of length at most `n`. -/
def sourceMoleculeCount (n : Nat) : Nat := 2 ^ (n + 1) - 2

theorem sourceMoleculeCount_bounds {n : Nat} (hn : 1 ≤ n) :
    2 ^ n ≤ sourceMoleculeCount n ∧ sourceMoleculeCount n ≤ 2 ^ (n + 1) := by
  unfold sourceMoleculeCount
  have hp : 2 ^ n + 2 ≤ 2 ^ (n + 1) := by
    rw [pow_succ]
    have htwo : 2 ≤ 2 ^ n := by
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hn
      norm_num at this ⊢
      exact this
    omega
  omega

theorem sourceMoleculeCount_tendsto_atTop : Tendsto sourceMoleculeCount atTop atTop := by
  have hp : Tendsto (fun n : Nat => 2 ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  refine tendsto_atTop_mono' atTop ?_ hp
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (sourceMoleculeCount_bounds hn).1

theorem log_sourceMoleculeCount_normalized :
    Tendsto (fun n : Nat => Real.log (sourceMoleculeCount n : ℝ) / (n : ℝ))
      atTop (𝓝 (Real.log 2)) := by
  let upper : Nat → ℝ := fun n =>
    (((n + 1 : Nat) : ℝ) / (n : ℝ)) * Real.log 2
  have hu : Tendsto upper atTop (𝓝 (Real.log 2)) := by
    have hmul := tendsto_nat_succ_div_nat.mul
      (tendsto_const_nhds : Tendsto (fun _ : Nat => Real.log 2)
        atTop (𝓝 (Real.log 2)))
    simpa [upper] using hmul
  have hl : Tendsto (fun _ : Nat => Real.log 2) atTop (𝓝 (Real.log 2)) :=
    tendsto_const_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hb := (sourceMoleculeCount_bounds hn).1
    have hlog : Real.log ((2 ^ n : Nat) : ℝ) ≤
        Real.log (sourceMoleculeCount n : ℝ) := by
      apply Real.strictMonoOn_log.monotoneOn
      · exact Set.mem_Ioi.mpr (by positivity)
      · exact Set.mem_Ioi.mpr (by exact_mod_cast (lt_of_lt_of_le (pow_pos (by norm_num) n) hb))
      · exact_mod_cast hb
    calc
      Real.log 2 = Real.log ((2 ^ n : Nat) : ℝ) / (n : ℝ) := by
        rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
        field_simp
      _ ≤ Real.log (sourceMoleculeCount n : ℝ) / (n : ℝ) :=
        div_le_div_of_nonneg_right hlog (by positivity)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hb := (sourceMoleculeCount_bounds hn).2
    have hlog : Real.log (sourceMoleculeCount n : ℝ) ≤
        Real.log ((2 ^ (n + 1) : Nat) : ℝ) := by
      apply Real.strictMonoOn_log.monotoneOn
      · exact Set.mem_Ioi.mpr (by
          exact_mod_cast (lt_of_lt_of_le (pow_pos (by norm_num) n)
            (sourceMoleculeCount_bounds hn).1))
      · exact Set.mem_Ioi.mpr (by positivity)
      · exact_mod_cast hb
    calc
      Real.log (sourceMoleculeCount n : ℝ) / (n : ℝ) ≤
          Real.log ((2 ^ (n + 1) : Nat) : ℝ) / (n : ℝ) :=
        div_le_div_of_nonneg_right hlog (by positivity)
      _ = upper n := by
        rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
        dsimp [upper]
        ring

/-- At the exact finite calibration, the expected number of molecule-scale
Zipf tails has the canonical critical-window constant. -/
theorem calibratedMoleculeScaleTail (lam : ℝ) (hlam : 0 < lam) :
    Tendsto (fun n : Nat =>
      (sourceMoleculeCount n : ℝ) *
        zipfTailRatio (calibrationExponent lam hlam n) (sourceMoleculeCount n))
      atTop
      (𝓝 (((2 : ℝ) ^
        (-criticalLambdaInv (⟨lam, hlam⟩ : Set.Ioi (0 : ℝ)))) /
          (Real.pi ^ 2 / 6))) := by
  let b₀ := criticalLambdaInv (⟨lam, hlam⟩ : Set.Ioi (0 : ℝ))
  have hb : Tendsto (fun n : Nat =>
      (n : ℝ) * (calibrationExponent lam hlam n - 2)) atTop (𝓝 b₀) := by
    apply (calibrationB_tendsto_inverse lam hlam).congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    dsimp [calibrationExponent]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    field_simp [hn0]
    ring
  have h := movingZipfTail (calibrationExponent lam hlam) sourceMoleculeCount
    b₀ (Real.log 2) (calibrationExponent_tendsto_two lam hlam) hb
    log_sourceMoleculeCount_normalized sourceMoleculeCount_tendsto_atTop
  convert h using 1
  dsimp [b₀]
  rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < 2)]
  congr 2
  ring

/-- Full molecule-scale law for any integer threshold asymptotic to
`y * |X_n|`.  A ceiling or floor realization only has to supply the displayed
ratio and logarithmic hypotheses. -/
theorem calibratedMoleculeScaleTail_of_ratio
    (lam y : ℝ) (hlam : 0 < lam) (hy : 0 < y) (m : Nat → Nat)
    (hm : Tendsto m atTop atTop)
    (hlog : Tendsto (fun n : Nat => Real.log (m n : ℝ) / (n : ℝ))
      atTop (𝓝 (Real.log 2)))
    (hratio : Tendsto (fun n : Nat =>
      (m n : ℝ) / (sourceMoleculeCount n : ℝ)) atTop (𝓝 y)) :
    Tendsto (fun n : Nat =>
      (sourceMoleculeCount n : ℝ) *
        zipfTailRatio (calibrationExponent lam hlam n) (m n)) atTop
      (𝓝 ((((2 : ℝ) ^
        (-criticalLambdaInv (⟨lam, hlam⟩ : Set.Ioi (0 : ℝ)))) /
          (Real.pi ^ 2 / 6)) / y)) := by
  let b₀ := criticalLambdaInv (⟨lam, hlam⟩ : Set.Ioi (0 : ℝ))
  have hb : Tendsto (fun n : Nat =>
      (n : ℝ) * (calibrationExponent lam hlam n - 2)) atTop (𝓝 b₀) := by
    apply (calibrationB_tendsto_inverse lam hlam).congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    dsimp [calibrationExponent]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    field_simp [hn0]
    ring
  have htail := movingZipfTail (calibrationExponent lam hlam) m b₀
    (Real.log 2) (calibrationExponent_tendsto_two lam hlam) hb hlog hm
  have hinv := hratio.inv₀ (ne_of_gt hy)
  have hfactor : Tendsto (fun n : Nat =>
      (sourceMoleculeCount n : ℝ) / (m n : ℝ)) atTop (𝓝 (1 / y)) := by
    simpa only [one_div, inv_div] using hinv
  have hmul := hfactor.mul htail
  have hmul' : Tendsto (fun n : Nat =>
      (sourceMoleculeCount n : ℝ) *
        zipfTailRatio (calibrationExponent lam hlam n) (m n)) atTop
      (𝓝 ((1 / y) * (Real.exp (-b₀ * Real.log 2) / (Real.pi ^ 2 / 6)))) := by
    apply hmul.congr'
    filter_upwards [hm.eventually (eventually_gt_atTop 0)] with n hmn
    field_simp
  convert hmul' using 1
  dsimp [b₀]
  rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < 2)]
  congr 2
  ring

theorem sourceMoleculeCount_div_power_tendsto_one :
    Tendsto (fun n : Nat =>
      (sourceMoleculeCount n : ℝ) / ((2 ^ (n + 1) : Nat) : ℝ))
      atTop (𝓝 1) := by
  have hp : Tendsto (fun n : Nat => ((2 ^ (n + 1) : Nat) : ℝ)) atTop atTop := by
    exact (tendsto_natCast_atTop_atTop (R := ℝ)).comp
      ((tendsto_add_atTop_iff_nat 1).2
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)))
  have hsmall : Tendsto (fun n : Nat =>
      (2 : ℝ) / ((2 ^ (n + 1) : Nat) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hp
  have h := (tendsto_const_nhds : Tendsto (fun _ : Nat => (1 : ℝ)) atTop (𝓝 1)).sub hsmall
  have h' : Tendsto (fun n : Nat =>
      (1 : ℝ) - 2 / ((2 ^ (n + 1) : Nat) : ℝ)) atTop (𝓝 1) := by
    simpa only [sub_zero] using h
  apply h'.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  dsimp [sourceMoleculeCount]
  have hpow : 2 ≤ 2 ^ (n + 1) := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 1 ≤ n + 1)
    norm_num at this ⊢
    exact this
  rw [Nat.cast_sub hpow]
  field_simp
  ring

theorem sourcePower_div_moleculeCount_tendsto_one :
    Tendsto (fun n : Nat =>
      ((2 ^ (n + 1) : Nat) : ℝ) / (sourceMoleculeCount n : ℝ))
      atTop (𝓝 1) := by
  have h := sourceMoleculeCount_div_power_tendsto_one.inv₀ one_ne_zero
  simpa only [inv_div, inv_one] using h

theorem sourceReactionCount_div_nat_molecule_tendsto_one :
    Tendsto (fun n : Nat =>
      (sourceReactionCount n : ℝ) /
        ((n : ℝ) * (sourceMoleculeCount n : ℝ))) atTop (𝓝 1) := by
  have htwo : Tendsto (fun n : Nat => (2 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hcoef : Tendsto (fun n : Nat => ((n : ℝ) - 2) / (n : ℝ))
      atTop (𝓝 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : Nat => (1 : ℝ)) atTop (𝓝 1)).sub htwo
    have h' : Tendsto (fun n : Nat => (1 : ℝ) - 2 / (n : ℝ)) atTop (𝓝 1) := by
      simpa only [sub_zero] using h
    apply h'.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    field_simp
  have hmain := hcoef.mul sourcePower_div_moleculeCount_tendsto_one
  have hninv : Tendsto (fun n : Nat => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
  have hxinv : Tendsto (fun n : Nat => (sourceMoleculeCount n : ℝ)⁻¹)
      atTop (𝓝 0) :=
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp
      sourceMoleculeCount_tendsto_atTop).inv_tendsto_atTop
  have hsmall : Tendsto (fun n : Nat =>
      (4 : ℝ) * (n : ℝ)⁻¹ * (sourceMoleculeCount n : ℝ)⁻¹)
      atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      (tendsto_const_nhds.mul hninv).mul hxinv
  have hsum := hmain.add hsmall
  have hsum' : Tendsto (fun n : Nat =>
      ((n : ℝ) - 2) / (n : ℝ) *
          (((2 ^ (n + 1) : Nat) : ℝ) / (sourceMoleculeCount n : ℝ)) +
        (4 : ℝ) * (n : ℝ)⁻¹ * (sourceMoleculeCount n : ℝ)⁻¹)
      atTop (𝓝 1) := by
    simpa only [mul_one, one_mul, add_zero] using hsum
  apply hsum'.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hx0 : (sourceMoleculeCount n : ℝ) ≠ 0 := by
    have hxnat : 0 < sourceMoleculeCount n :=
      (pow_pos (by norm_num) n).trans_le (sourceMoleculeCount_bounds (by omega)).1
    exact_mod_cast (Nat.ne_of_gt hxnat)
  dsimp [sourceReactionCount]
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_ofNat,
    Nat.cast_pow, Nat.cast_ofNat]
  field_simp [hn0, hx0]
  ring

/-- Mesoscopic transfer principle.  Taking `q_n = n^(s-1)` and a rounded
threshold `m_n ~ R_n/n^s` is justified by
`sourceReactionCount_div_nat_molecule_tendsto_one`. -/
theorem calibratedMesoscopicTail_of_ratio
    (lam : ℝ) (hlam : 0 < lam) (m : Nat → Nat) (q : Nat → ℝ)
    (hm : Tendsto m atTop atTop)
    (hlog : Tendsto (fun n : Nat => Real.log (m n : ℝ) / (n : ℝ))
      atTop (𝓝 (Real.log 2)))
    (hq : ∀ᶠ n : Nat in atTop, q n ≠ 0)
    (hratio : Tendsto (fun n : Nat =>
      ((m n : ℝ) * q n) / (sourceMoleculeCount n : ℝ)) atTop (𝓝 1)) :
    Tendsto (fun n : Nat =>
      ((sourceMoleculeCount n : ℝ) *
        zipfTailRatio (calibrationExponent lam hlam n) (m n)) / q n) atTop
      (𝓝 (((2 : ℝ) ^
        (-criticalLambdaInv (⟨lam, hlam⟩ : Set.Ioi (0 : ℝ)))) /
          (Real.pi ^ 2 / 6))) := by
  let b₀ := criticalLambdaInv (⟨lam, hlam⟩ : Set.Ioi (0 : ℝ))
  have hb : Tendsto (fun n : Nat =>
      (n : ℝ) * (calibrationExponent lam hlam n - 2)) atTop (𝓝 b₀) := by
    apply (calibrationB_tendsto_inverse lam hlam).congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    dsimp [calibrationExponent]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    field_simp [hn0]
    ring
  have htail := movingZipfTail (calibrationExponent lam hlam) m b₀
    (Real.log 2) (calibrationExponent_tendsto_two lam hlam) hb hlog hm
  have hinv := hratio.inv₀ one_ne_zero
  have hfactor : Tendsto (fun n : Nat =>
      (sourceMoleculeCount n : ℝ) / ((m n : ℝ) * q n)) atTop (𝓝 1) := by
    simpa only [inv_div, inv_one] using hinv
  have hmul := hfactor.mul htail
  have hmul0 : Tendsto (fun n : Nat =>
      (sourceMoleculeCount n : ℝ) / ((m n : ℝ) * q n) *
        ((m n : ℝ) * zipfTailRatio (calibrationExponent lam hlam n) (m n)))
      atTop (𝓝 (Real.exp (-b₀ * Real.log 2) / (Real.pi ^ 2 / 6))) := by
    simpa only [one_mul] using hmul
  have hmul' : Tendsto (fun n : Nat =>
      ((sourceMoleculeCount n : ℝ) *
        zipfTailRatio (calibrationExponent lam hlam n) (m n)) / q n) atTop
      (𝓝 (Real.exp (-b₀ * Real.log 2) / (Real.pi ^ 2 / 6))) := by
    apply hmul0.congr'
    filter_upwards [hm.eventually (eventually_gt_atTop 0), hq] with n hmn hqn
    field_simp
  convert hmul' using 1
  dsimp [b₀]
  rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < 2)]
  congr 2
  ring

end PowerLawSmallRAF

import proofs.PowerLawSmallRAF.CriticalBandExponent
import proofs.PowerLawSmallRAF.CalibratedGatewayHighTail

namespace PowerLawSmallRAF

open Filter Topology Set intervalIntegral

noncomputable section

/-- Continuous two-parameter primitive underlying every logarithmic degree
band, including the removable zero-tilt case. -/
def criticalPartialMass (b ell : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..ell, Real.exp (-b * t)

theorem continuous_criticalPartialMass :
    Continuous fun p : ℝ × ℝ => criticalPartialMass p.1 p.2 := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun p : ℝ × ℝ => fun t : ℝ => Real.exp (-p.1 * t))
    (by fun_prop) (by fun_prop)

theorem movingWindowIntegral_eq_criticalPartialMass
    (m : Nat → Nat) (B : ℝ) (n : Nat) (hn : 0 < n) (hm : 1 ≤ m n) :
    (∫ x in (1 : ℝ)..(m n : ℝ),
        x ^ (-(1 + B / (n : ℝ)))) / (n : ℝ) =
      criticalPartialMass B (Real.log (m n : ℝ) / (n : ℝ)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hmpos : (0 : ℝ) < (m n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  by_cases hB : B = 0
  · subst B
    rw [show -(1 + (0 : ℝ) / (n : ℝ)) = (-1 : ℝ) by ring]
    simp only [Real.rpow_neg_one]
    rw [integral_inv_of_pos (by norm_num) hmpos]
    simp [criticalPartialMass]
  · rw [movingWindowIntegral_eq m B hB n hn hm]
    rw [criticalPartialMass, integral_exp_neg_mul B hB]
    rw [Real.rpow_def_of_pos hmpos]
    congr 3
    field_simp [hn0]

/-- The tilted harmonic asymptotic remains valid when the critical-window
coordinate itself moves and converges. -/
theorem movingTiltedHarmonic_window_normalized
    (m : Nat → Nat) (B : Nat → ℝ) (b ell : ℝ)
    (hB : Tendsto B atTop (𝓝 b))
    (hlog : Tendsto (fun n : Nat => Real.log (m n : ℝ) / (n : ℝ))
      atTop (𝓝 ell))
    (hm : Tendsto m atTop atTop) :
    Tendsto (fun n : Nat =>
      tiltedHarmonic (1 + B n / (n : ℝ)) (m n) / (n : ℝ)) atTop
      (𝓝 (criticalPartialMass b ell)) := by
  have hpair : Tendsto (fun n : Nat =>
      (B n, Real.log (m n : ℝ) / (n : ℝ))) atTop (𝓝 (b, ell)) :=
    hB.prodMk_nhds hlog
  have hI : Tendsto (fun n : Nat =>
      (∫ x in (1 : ℝ)..(m n : ℝ),
        x ^ (-(1 + B n / (n : ℝ)))) / (n : ℝ)) atTop
      (𝓝 (criticalPartialMass b ell)) := by
    have hcont := continuous_criticalPartialMass.continuousAt.tendsto.comp hpair
    apply hcont.congr'
    filter_upwards [eventually_ge_atTop 1,
      hm.eventually (eventually_ge_atTop 1)] with n hn hmn
    exact (movingWindowIntegral_eq_criticalPartialMass m (B n) n hn hmn).symm
  have honeDiv : Tendsto (fun n : Nat => (1 : ℝ) / (n : ℝ))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hu := hI.add honeDiv
  have hBdiv : Tendsto (fun n : Nat => B n / (n : ℝ)) atTop (𝓝 0) :=
    hB.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hp : Tendsto (fun n : Nat => 1 + B n / (n : ℝ)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add hBdiv)
  have hpEv : ∀ᶠ n : Nat in atTop, 0 < 1 + B n / (n : ℝ) :=
    hp (Ioi_mem_nhds zero_lt_one)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hI (by simpa using hu)
  · filter_upwards [eventually_ge_atTop 1, hpEv,
      hm.eventually (eventually_ge_atTop 2)] with n hn hpn hmn
    exact div_le_div_of_nonneg_right
      (tiltedHarmonic_integral_bounds (1 + B n / (n : ℝ)) hpn (m n) hmn).1
      (by positivity)
  · filter_upwards [eventually_ge_atTop 1, hpEv,
      hm.eventually (eventually_ge_atTop 2)] with n hn hpn hmn
    have hbound :=
      (tiltedHarmonic_integral_bounds (1 + B n / (n : ℝ)) hpn (m n) hmn).2
    have hexp : (fun x : ℝ => x ^ (-(1 + B n / (n : ℝ)))) =
        fun x : ℝ => x ^ (-(B n / (n : ℝ)) + -1) := by
      funext x
      congr 1
      ring
    rw [hexp] at hbound
    calc
      tiltedHarmonic (1 + B n / (n : ℝ)) (m n) / (n : ℝ) ≤
          (1 + ∫ x in (1 : ℝ)..(m n : ℝ),
            x ^ (-(B n / (n : ℝ)) + -1)) / (n : ℝ) :=
        div_le_div_of_nonneg_right hbound (by positivity)
      _ = (∫ x in (1 : ℝ)..(m n : ℝ),
            x ^ (-(B n / (n : ℝ)) + -1)) / (n : ℝ) +
          (n : ℝ)⁻¹ := by
        rw [← one_div]
        field_simp
        ring

theorem movingWindowInterior_normalized_general
    (m : Nat → Nat) (B : Nat → ℝ) (b : ℝ)
    (hB : Tendsto B atTop (𝓝 b)) :
    Tendsto (fun n : Nat =>
      (∑ k ∈ Finset.Ico 2 (m n),
        (k : ℝ) ^ (-(2 + B n / (n : ℝ)))) / (n : ℝ))
      atTop (𝓝 0) := by
  have hBdiv : Tendsto (fun n : Nat => B n / (n : ℝ)) atTop (𝓝 0) :=
    hB.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have ha : Tendsto (fun n : Nat => 2 + B n / (n : ℝ)) atTop (𝓝 2) := by
    simpa using (tendsto_const_nhds.add hBdiv)
  have hzeta : Tendsto (fun n : Nat =>
      zipfNormalizer (2 + B n / (n : ℝ))) atTop
      (𝓝 (Real.pi ^ 2 / 6)) := by
    simpa only [zipfNormalizer_two] using
      (continuousAt_zipfNormalizer one_lt_two).tendsto.comp ha
  have hupper := hzeta.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have haEv : ∀ᶠ n : Nat in atTop, 1 < 2 + B n / (n : ℝ) :=
    ha (Ioi_mem_nhds one_lt_two)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ℝ)) atTop (𝓝 0))
    (by simpa using hupper)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_nonneg (windowInterior_nonneg _ _) (by positivity)
  · filter_upwards [eventually_ge_atTop 1, haEv] with n hn han
    exact div_le_div_of_nonneg_right
      (windowInterior_le_normalizer _ han (m n)) (by positivity)

theorem movingWindowPartialNumerator_normalized
    (m : Nat → Nat) (B : Nat → ℝ) (b ell : ℝ)
    (hB : Tendsto B atTop (𝓝 b))
    (hlog : Tendsto (fun n : Nat => Real.log (m n : ℝ) / (n : ℝ))
      atTop (𝓝 ell))
    (hm : Tendsto m atTop atTop) :
    Tendsto (fun n : Nat =>
      windowPartialNumerator (2 + B n / (n : ℝ)) (m n) / (n : ℝ))
      atTop (𝓝 (criticalPartialMass b ell)) := by
  have htilt := movingTiltedHarmonic_window_normalized m B b ell hB hlog hm
  have hone : Tendsto (fun n : Nat => (1 : ℝ) / (n : ℝ))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hinterior := movingWindowInterior_normalized_general m B b hB
  have hcombined := htilt.sub hone |>.sub hinterior
  have hcombined' : Tendsto (fun n : Nat =>
      tiltedHarmonic (1 + B n / (n : ℝ)) (m n) / (n : ℝ) -
        1 / (n : ℝ) -
        (∑ k ∈ Finset.Ico 2 (m n),
          (k : ℝ) ^ (-(2 + B n / (n : ℝ)))) / (n : ℝ))
      atTop (𝓝 (criticalPartialMass b ell)) := by
    simpa using hcombined
  apply hcombined'.congr'
  filter_upwards [eventually_ge_atTop 1,
    hm.eventually (eventually_ge_atTop 2)] with n hn hmn
  rw [windowPartialNumerator_eq (2 + B n / (n : ℝ)) (m n) hmn]
  ring_nf

/-- Exact calibration specialization of the moving partial-degree theorem. -/
theorem calibrated_windowPartialNumerator_normalized
    (lam : ℝ) (hlam : 0 < lam) (m : Nat → Nat) (ell : ℝ)
    (hlog : Tendsto (fun n : Nat => Real.log (m n : ℝ) / (n : ℝ))
      atTop (𝓝 ell))
    (hm : Tendsto m atTop atTop) :
    Tendsto (fun n : Nat =>
      windowPartialNumerator (calibrationExponent lam hlam n) (m n) /
        (n : ℝ)) atTop
      (𝓝 (criticalPartialMass
        (criticalLambdaInv (⟨lam, hlam⟩ : Ioi (0 : ℝ))) ell)) := by
  have h := movingWindowPartialNumerator_normalized m (calibrationB lam hlam)
    (criticalLambdaInv (⟨lam, hlam⟩ : Ioi (0 : ℝ))) ell
    (calibrationB_tendsto_inverse lam hlam) hlog hm
  simpa only [calibrationExponent] using h

theorem criticalTopBandMass_eq_total_sub_partial (b c : ℝ) :
    criticalTopBandMass b c =
      (criticalIntegral b -
        criticalPartialMass b ((1 - c) * Real.log 2)) /
          (Real.pi ^ 2 / 6) := by
  by_cases hb : b = 0
  · subst b
    simp [criticalTopBandMass, criticalIntegral, criticalPartialMass]
    ring
  · rw [criticalTopBandMass, if_neg hb, criticalIntegral,
      criticalPartialMass, integral_exp_neg_mul b hb,
      integral_exp_neg_mul b hb]
    ring

/-- Expected normalized total degree contributed by marks at least `m` in the
exact source population.  This is a deterministic expectation, before the
independent molecule marks are sampled. -/
def sourceExpectedHighBandDensity
    (lam : ℝ) (hlam : 0 < lam) (m : Nat → Nat) (n : Nat) : ℝ :=
  (sourceMoleculeCount n : ℝ) / (sourceReactionCount n : ℝ) *
    (windowHighNumerator (calibrationExponent lam hlam n)
      (sourceReactionCount n) (m n) /
        zipfNormalizer (calibrationExponent lam hlam n))

/-- A logarithmic threshold of exponent `(1-c) log 2` carries exactly the
candidate top-band channel mass in the finite calibrated source model. -/
theorem sourceExpectedHighBandDensity_tendsto
    (lam : ℝ) (hlam : 0 < lam) (c : ℝ) (m : Nat → Nat)
    (hlog : Tendsto (fun n : Nat => Real.log (m n : ℝ) / (n : ℝ))
      atTop (𝓝 ((1 - c) * Real.log 2)))
    (hm : Tendsto m atTop atTop) :
    Tendsto (sourceExpectedHighBandDensity lam hlam m) atTop
      (𝓝 (criticalTopBandMass
        (criticalLambdaInv (⟨lam, hlam⟩ : Ioi (0 : ℝ))) c)) := by
  let b := criticalLambdaInv (⟨lam, hlam⟩ : Ioi (0 : ℝ))
  have hpartial := calibrated_windowPartialNumerator_normalized lam hlam m
    ((1 - c) * Real.log 2) hlog hm
  have htotal := calibrated_windowDirectNumerator_normalized lam hlam
  have hhigh : Tendsto (fun n : Nat =>
      windowHighNumerator (calibrationExponent lam hlam n)
        (sourceReactionCount n) (m n) / (n : ℝ)) atTop
      (𝓝 (lam * (Real.pi ^ 2 / 6) -
        criticalPartialMass b ((1 - c) * Real.log 2))) := by
    have hsub := htotal.sub hpartial
    apply hsub.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    dsimp [windowHighNumerator]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    field_simp [hn0]
  have hnormalizer : Tendsto (fun n : Nat =>
      zipfNormalizer (calibrationExponent lam hlam n)) atTop
      (𝓝 (Real.pi ^ 2 / 6)) := by
    simpa only [zipfNormalizer_two] using
      (continuousAt_zipfNormalizer one_lt_two).tendsto.comp
        (calibrationExponent_tendsto_two lam hlam)
  have hcatalogInv := sourceReactionCount_div_nat_molecule_tendsto_one.inv₀
    one_ne_zero
  have hcatalog : Tendsto (fun n : Nat =>
      (n : ℝ) * (sourceMoleculeCount n : ℝ) /
        (sourceReactionCount n : ℝ)) atTop (𝓝 1) := by
    simpa only [inv_div, inv_one] using hcatalogInv
  have hquot := hhigh.div hnormalizer (by positivity : Real.pi ^ 2 / 6 ≠ 0)
  have hproduct := hcatalog.mul hquot
  have hproduct' : Tendsto (fun n : Nat =>
      ((n : ℝ) * (sourceMoleculeCount n : ℝ) /
          (sourceReactionCount n : ℝ)) *
        ((windowHighNumerator (calibrationExponent lam hlam n)
            (sourceReactionCount n) (m n) / (n : ℝ)) /
          zipfNormalizer (calibrationExponent lam hlam n))) atTop
      (𝓝 ((lam * (Real.pi ^ 2 / 6) -
        criticalPartialMass b ((1 - c) * Real.log 2)) /
          (Real.pi ^ 2 / 6))) := by
    simpa using hproduct
  have hbval : criticalLambda b = lam := criticalLambda_criticalLambdaInv _
  have hlimit :
      (lam * (Real.pi ^ 2 / 6) -
          criticalPartialMass b ((1 - c) * Real.log 2)) /
            (Real.pi ^ 2 / 6) = criticalTopBandMass b c := by
    rw [← hbval, criticalLambda_eq_integral,
      criticalTopBandMass_eq_total_sub_partial]
    field_simp
  rw [← hlimit]
  apply hproduct'.congr'
  have hRpos : ∀ᶠ n : Nat in atTop, (0 : ℝ) < sourceReactionCount n := by
    filter_upwards with n
    have hnat : 0 < sourceReactionCount n := by
      simp [sourceReactionCount]
    exact_mod_cast hnat
  filter_upwards [eventually_ge_atTop 1, hRpos] with n hn hRn
  dsimp [sourceExpectedHighBandDensity]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hR0 : (sourceReactionCount n : ℝ) ≠ 0 := ne_of_gt hRn
  field_simp [hn0, hR0]

end

end PowerLawSmallRAF

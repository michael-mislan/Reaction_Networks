import proofs.PowerLawSmallRAF.SourceCriticalSecondMoment

namespace PowerLawSmallRAF
open Filter Topology
noncomputable section

/-- Fixed-channel limits under the literal exponent sequence, using the existing
without-replacement gateway bounds. No global iid assumption is made. -/
theorem sourceExactCriticalGatewayUpper_scaled_tendsto
    (M : Nat) (hM0 : 0 < M) :
    Tendsto (fun n : Nat =>
      (sourceMoleculeCount n : ℝ) *
        ((M : ℝ) * windowZipfMean (2-2/(n : ℝ))
          (sourceReactionCount n) /
            ((sourceReactionCount n - M + 1 : Nat) : ℝ)))
      atTop (𝓝 ((M : ℝ) * (criticalLambda (-2)))) := by
  have hA := sourceExactCriticalFirstMoment_scaled_tendsto
  have hq := sourceReactionCount_div_gatewayDenominator_tendsto_one M hM0
  have htarget :=
    ((tendsto_const_nhds : Tendsto (fun _ : Nat => (M : ℝ)) atTop
      (𝓝 (M : ℝ))).mul hA).mul hq
  have htarget' : Tendsto (fun n : Nat =>
      ((M : ℝ) * ((sourceMoleculeCount n : ℝ) *
        windowZipfMean (2-2/(n : ℝ))
          (sourceReactionCount n) / (sourceReactionCount n : ℝ))) *
        ((sourceReactionCount n : ℝ) /
          ((sourceReactionCount n - M + 1 : Nat) : ℝ)))
      atTop (𝓝 ((M : ℝ) * (criticalLambda (-2)))) := by
    simpa only [mul_one] using htarget
  apply htarget'.congr'
  filter_upwards [sourceReactionCount_tendsto_atTop.eventually
    (eventually_ge_atTop (M + 1))] with n hR
  have hR0 : (sourceReactionCount n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (by omega : 0 < sourceReactionCount n)
  have hL0 : (((sourceReactionCount n - M + 1 : Nat) : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (by omega : 0 < sourceReactionCount n - M + 1)
  field_simp [hR0, hL0]

theorem sourceExactCriticalGatewayQuadraticError_scaled_tendsto_zero
    (M : Nat) (hM0 : 0 < M) :
    Tendsto (fun n : Nat =>
      (sourceMoleculeCount n : ℝ) *
        (((M : ℝ) / ((sourceReactionCount n - M + 1 : Nat) : ℝ)) ^ 2 *
          windowZipfSecondMoment (2-2/(n : ℝ))
            (sourceReactionCount n))) atTop (𝓝 0) := by
  have hq := sourceReactionCount_div_gatewayDenominator_tendsto_one M hM0
  have hE := sourceExactCriticalSecondMoment_scaled_tendsto_zero
  have htarget :=
    ((tendsto_const_nhds : Tendsto (fun _ : Nat => ((M : ℝ) ^ 2)) atTop
      (𝓝 ((M : ℝ) ^ 2))).mul (hq.pow 2)).mul hE
  have htarget' : Tendsto (fun n : Nat =>
      (((M : ℝ) ^ 2) *
        ((sourceReactionCount n : ℝ) /
          ((sourceReactionCount n - M + 1 : Nat) : ℝ)) ^ 2) *
        ((sourceMoleculeCount n : ℝ) *
          windowZipfSecondMoment (2-2/(n : ℝ))
            (sourceReactionCount n) / (sourceReactionCount n : ℝ) ^ 2))
      atTop (𝓝 0) := by
    simpa only [one_pow, mul_one, mul_zero] using htarget
  apply htarget'.congr'
  filter_upwards [sourceReactionCount_tendsto_atTop.eventually
    (eventually_ge_atTop (M + 1))] with n hR
  have hR0 : (sourceReactionCount n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (by omega : 0 < sourceReactionCount n)
  have hL0 : (((sourceReactionCount n - M + 1 : Nat) : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (by omega : 0 < sourceReactionCount n - M + 1)
  field_simp [hR0, hL0]

theorem sourceExactCriticalPowerLawMoleculeGatewayHit_scaled
    (M : Nat) (hM0 : 0 < M) :
    Tendsto (fun n : Nat =>
      (sourceMoleculeCount n : ℝ) *
        powerLawMoleculeGatewayHit (2-2/(n : ℝ))
          (sourceReactionCount n) M) atTop (𝓝 ((M : ℝ) * (criticalLambda (-2)))) := by
  have hA := sourceExactCriticalFirstMoment_scaled_tendsto
  have hmain0 :=
    (tendsto_const_nhds : Tendsto (fun _ : Nat => (M : ℝ)) atTop
      (𝓝 (M : ℝ))).mul hA
  have hmain : Tendsto (fun n : Nat =>
      (sourceMoleculeCount n : ℝ) *
        ((M : ℝ) * windowZipfMean (2-2/(n : ℝ))
          (sourceReactionCount n) / (sourceReactionCount n : ℝ)))
      atTop (𝓝 ((M : ℝ) * (criticalLambda (-2)))) := by
    apply hmain0.congr'
    exact Filter.Eventually.of_forall (fun n => by ring)
  have herr := sourceExactCriticalGatewayQuadraticError_scaled_tendsto_zero M hM0
  have hlower0 := hmain.sub herr
  have hlower : Tendsto (fun n : Nat =>
      (sourceMoleculeCount n : ℝ) *
        ((M : ℝ) * windowZipfMean (2-2/(n : ℝ))
            (sourceReactionCount n) / (sourceReactionCount n : ℝ) -
          ((M : ℝ) /
            ((sourceReactionCount n - M + 1 : Nat) : ℝ)) ^ 2 *
            windowZipfSecondMoment (2-2/(n : ℝ))
              (sourceReactionCount n)))
      atTop (𝓝 ((M : ℝ) * (criticalLambda (-2)))) := by
    have hlower1 : Tendsto (fun n : Nat =>
        (sourceMoleculeCount n : ℝ) *
            ((M : ℝ) * windowZipfMean (2-2/(n : ℝ))
              (sourceReactionCount n) / (sourceReactionCount n : ℝ)) -
          (sourceMoleculeCount n : ℝ) *
            (((M : ℝ) /
              ((sourceReactionCount n - M + 1 : Nat) : ℝ)) ^ 2 *
              windowZipfSecondMoment (2-2/(n : ℝ))
                (sourceReactionCount n)))
        atTop (𝓝 ((M : ℝ) * (criticalLambda (-2)))) := by
      simpa only [sub_zero] using hlower0
    apply hlower1.congr'
    exact Filter.Eventually.of_forall (fun n => by ring)
  have hupper := sourceExactCriticalGatewayUpper_scaled_tendsto M hM0
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · have ha : ∀ᶠ n : Nat in atTop, 1 < (2-2/(n : ℝ)) :=
      sourceExactCriticalExponent_tendsto (Ioi_mem_nhds one_lt_two)
    filter_upwards [ha, sourceReactionCount_tendsto_atTop.eventually
      (eventually_ge_atTop (max 2 M))] with n han hR
    have hb := powerLawMoleculeGatewayHit_bounds
      (2-2/(n : ℝ)) (sourceReactionCount n) M han
      (by omega) hM0 (by omega)
    exact mul_le_mul_of_nonneg_left hb.1 (Nat.cast_nonneg _)
  · have ha : ∀ᶠ n : Nat in atTop, 1 < (2-2/(n : ℝ)) :=
      sourceExactCriticalExponent_tendsto (Ioi_mem_nhds one_lt_two)
    filter_upwards [ha, sourceReactionCount_tendsto_atTop.eventually
      (eventually_ge_atTop (max 2 M))] with n han hR
    have hb := powerLawMoleculeGatewayHit_bounds
      (2-2/(n : ℝ)) (sourceReactionCount n) M han
      (by omega) hM0 (by omega)
    exact mul_le_mul_of_nonneg_left hb.2 (Nat.cast_nonneg _)

theorem sourceExactCriticalPowerLawSeedClosed
    (M : Nat) (hM0 : 0 < M) :
    Tendsto (fun n : Nat => powerLawSeedClosedProbability
      (2-2/(n : ℝ)) (sourceReactionCount n) M
        (sourceMoleculeCount n)) atTop
      (𝓝 (Real.exp (-((M : ℝ) * (criticalLambda (-2)))))) := by
  let p : Nat → ℝ := fun n =>
    powerLawMoleculeGatewayHit (2-2/(n : ℝ))
      (sourceReactionCount n) M
  have hNp : Tendsto (fun n : Nat => (sourceMoleculeCount n : ℝ) * p n)
      atTop (𝓝 ((M : ℝ) * (criticalLambda (-2)))) := by
    simpa only [p] using sourceExactCriticalPowerLawMoleculeGatewayHit_scaled M hM0
  have hxreal : Tendsto (fun n : Nat => (sourceMoleculeCount n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp sourceMoleculeCount_tendsto_atTop
  have hp : Tendsto p atTop (𝓝 0) := by
    have h := hNp.mul hxreal.inv_tendsto_atTop
    have h' : Tendsto (fun n : Nat =>
        ((sourceMoleculeCount n : ℝ) * p n) *
          (sourceMoleculeCount n : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa only [mul_zero] using h
    apply h'.congr'
    filter_upwards [sourceMoleculeCount_tendsto_atTop.eventually
      (eventually_gt_atTop 0)] with n hxn
    field_simp
  have htheta : 0 < (M : ℝ) * (criticalLambda (-2)) :=
    mul_pos (by exact_mod_cast hM0) (criticalLambda_pos (-2))
  have hprodpos : ∀ᶠ n : Nat in atTop,
      0 < (sourceMoleculeCount n : ℝ) * p n :=
    hNp (Ioi_mem_nhds htheta)
  have hpne : ∀ᶠ n : Nat in atTop, p n ≠ 0 := by
    filter_upwards [hprodpos] with n hn hzero
    rw [hzero, mul_zero] at hn
    exact (lt_irrefl 0 hn)
  have hplt : ∀ᶠ n : Nat in atTop, p n < 1 := hp (Iio_mem_nhds one_pos)
  simpa [powerLawSeedClosedProbability, p, powerLawMoleculeGatewayHit] using
    binomialNoHit_tendsto_exp_neg sourceMoleculeCount p ((M : ℝ) * (criticalLambda (-2)))
      hp hpne hplt hNp


end
end PowerLawSmallRAF

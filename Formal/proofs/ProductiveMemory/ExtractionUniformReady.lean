import proofs.ProductiveMemory.ExtractionUniformRecovery

namespace ProductiveMemory
open FiniteCopy Set
open scoped NNReal
noncomputable section
set_option Elab.async false

theorem low_extraction_uniform_ready (rho z : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hz : z ∈ Icc (98172/100000:ℝ) (98174/100000))
    (he : extractDrift rho 0 (lift rho z) = 0) (m : ℕ) (hm : recoveryCount ≤ m)
    (q : NNReal) (hq : 0 < (q:ℝ))
    (hclock : ∀ s, (extractionStoppedModel rho (by linarith [hr.1]) m (lowExtractionWell rho z m outerLevel)).total s ≤ q)
    (hk : (m:ℝ)*localAlpha*readyLevel/480 ≤ q)
    (n : {n : Counts // n ∈ lowExtractionWell rho z m outerLevel})
    (hbirth : lowExtractionEnergy (fun i => concentration m n.val i-lift rho z i) ≤ 8*readyLevel) :
    1-1/10^18 ≤
    ((extractionStoppedModel rho (by linarith [hr.1]) m (lowExtractionWell rho z m outerLevel)).uniformize q hq hclock).poissonized (q*5376)
      (FiniteKernel.eventIndicator (terminalReady m (lowExtractionWell rho z m outerLevel) (lift rho z) lowExtractionEnergy)) (some n) := by
  have hm1 : 1 ≤ m := (by norm_num [recoveryCount] : 1 ≤ recoveryCount).trans hm
  have hl : 480*100000000 ≤ (m:ℝ)*readyLevel := recovery_count_large.trans
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hm) (by norm_num [readyLevel,outerLevel]))
  have h := low_extraction_recovery_ready rho z hr hz he m hm1 hl q hq hclock hk n hbirth
  have hb := recovery_error_uniform m hm
  unfold recoveryError at hb
  linarith only [h,hb]

theorem high_extraction_uniform_ready (rho z : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hz : z ∈ Icc (289014/100000:ℝ) (289017/100000))
    (he : extractDrift rho 0 (lift rho z) = 0) (m : ℕ) (hm : recoveryCount ≤ m)
    (q : NNReal) (hq : 0 < (q:ℝ))
    (hclock : ∀ s, (extractionStoppedModel rho (by linarith [hr.1]) m (highExtractionWell rho z m outerLevel)).total s ≤ q)
    (hk : (m:ℝ)*localAlpha*readyLevel/480 ≤ q)
    (n : {n : Counts // n ∈ highExtractionWell rho z m outerLevel})
    (hbirth : highExtractionEnergy (fun i => concentration m n.val i-lift rho z i) ≤ 8*readyLevel) :
    1-1/10^18 ≤
    ((extractionStoppedModel rho (by linarith [hr.1]) m (highExtractionWell rho z m outerLevel)).uniformize q hq hclock).poissonized (q*5376)
      (FiniteKernel.eventIndicator (terminalReady m (highExtractionWell rho z m outerLevel) (lift rho z) highExtractionEnergy)) (some n) := by
  have hm1 : 1 ≤ m := (by norm_num [recoveryCount] : 1 ≤ recoveryCount).trans hm
  have hl : 480*100000000 ≤ (m:ℝ)*readyLevel := recovery_count_large.trans
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hm) (by norm_num [readyLevel,outerLevel]))
  have h := high_extraction_recovery_ready rho z hr hz he m hm1 hl q hq hclock hk n hbirth
  have hb := recovery_error_uniform m hm
  unfold recoveryError at hb
  linarith only [h,hb]

end
end ProductiveMemory

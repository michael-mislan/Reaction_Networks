import proofs.ProductiveMemory.ExtractionJointEndpoint

namespace ProductiveMemory
open FiniteCopy Set
open scoped NNReal
noncomputable section
set_option Elab.async false

theorem low_extraction_recovery_ready (rho z : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hz : z ∈ Icc (98172/100000:ℝ) (98174/100000))
    (he : extractDrift rho 0 (lift rho z) = 0) (N : ℕ) (hN : 1 ≤ N)
    (hlarge : 480*100000000 ≤ (N:ℝ)*readyLevel)
    (q : NNReal) (hq : 0 < (q:ℝ))
    (hclock : ∀ s, (extractionStoppedModel rho (by linarith [hr.1]) N (lowExtractionWell rho z N outerLevel)).total s ≤ q)
    (hk : (N:ℝ)*localAlpha*readyLevel/480 ≤ q)
    (n : {n : Counts // n ∈ lowExtractionWell rho z N outerLevel})
    (hbirth : lowExtractionEnergy (fun i => concentration N n.val i-lift rho z i) ≤ 8*readyLevel) :
    1-(Real.exp (-((N:ℝ)*localAlpha*readyLevel))+2*Real.exp (-((N:ℝ)*localAlpha*readyLevel)/2))
      -(Real.exp (8*((N:ℝ)*localAlpha*readyLevel))+5376*extractionCeiling)/Real.exp ((N:ℝ)*localAlpha*outerLevel) ≤
    ((extractionStoppedModel rho (by linarith [hr.1]) N (lowExtractionWell rho z N outerLevel)).uniformize q hq hclock).poissonized (q*5376)
      (FiniteKernel.eventIndicator (terminalReady N (lowExtractionWell rho z N outerLevel) (lift rho z) lowExtractionEnergy)) (some n) := by
  apply terminal_ready_lower
  · exact low_extraction_terminal_bound rho z hr hz he N hN hlarge q hq hclock hk n hbirth
  · apply (le_div_iff₀ (Real.exp_pos _)).mpr
    have h := low_extraction_exit_bound rho z hr hz he N hN outerLevel (by norm_num [outerLevel]) q 5376 hq hclock n
    have hi : energyExponential lowExtractionEnergy N (lift rho z) (concentration N n.val) ≤
        Real.exp (8*((N:ℝ)*localAlpha*readyLevel)) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hbirth (by unfold localAlpha; positivity : 0 ≤ (N:ℝ)*localAlpha)
      nlinarith only [hh]
    norm_num only [NNReal.coe_ofNat] at h
    nlinarith only [h,hi]

theorem high_extraction_recovery_ready (rho z : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hz : z ∈ Icc (289014/100000:ℝ) (289017/100000))
    (he : extractDrift rho 0 (lift rho z) = 0) (N : ℕ) (hN : 1 ≤ N)
    (hlarge : 480*100000000 ≤ (N:ℝ)*readyLevel)
    (q : NNReal) (hq : 0 < (q:ℝ))
    (hclock : ∀ s, (extractionStoppedModel rho (by linarith [hr.1]) N (highExtractionWell rho z N outerLevel)).total s ≤ q)
    (hk : (N:ℝ)*localAlpha*readyLevel/480 ≤ q)
    (n : {n : Counts // n ∈ highExtractionWell rho z N outerLevel})
    (hbirth : highExtractionEnergy (fun i => concentration N n.val i-lift rho z i) ≤ 8*readyLevel) :
    1-(Real.exp (-((N:ℝ)*localAlpha*readyLevel))+2*Real.exp (-((N:ℝ)*localAlpha*readyLevel)/2))
      -(Real.exp (8*((N:ℝ)*localAlpha*readyLevel))+5376*extractionCeiling)/Real.exp ((N:ℝ)*localAlpha*outerLevel) ≤
    ((extractionStoppedModel rho (by linarith [hr.1]) N (highExtractionWell rho z N outerLevel)).uniformize q hq hclock).poissonized (q*5376)
      (FiniteKernel.eventIndicator (terminalReady N (highExtractionWell rho z N outerLevel) (lift rho z) highExtractionEnergy)) (some n) := by
  apply terminal_ready_lower
  · exact high_extraction_terminal_bound rho z hr hz he N hN hlarge q hq hclock hk n hbirth
  · apply (le_div_iff₀ (Real.exp_pos _)).mpr
    have h := high_extraction_exit_bound rho z hr hz he N hN outerLevel (by norm_num [outerLevel]) q 5376 hq hclock n
    have hi : energyExponential highExtractionEnergy N (lift rho z) (concentration N n.val) ≤
        Real.exp (8*((N:ℝ)*localAlpha*readyLevel)) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hbirth (by unfold localAlpha; positivity : 0 ≤ (N:ℝ)*localAlpha)
      nlinarith only [hh]
    norm_num only [NNReal.coe_ofNat] at h
    nlinarith only [h,hi]

end
end ProductiveMemory

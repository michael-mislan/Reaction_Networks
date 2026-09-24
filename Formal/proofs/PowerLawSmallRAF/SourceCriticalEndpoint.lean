import proofs.PowerLawSmallRAF.SourceFiniteCapLimit
import proofs.PowerLawSmallRAF.SourceRAFSurvivalLower
import proofs.HordijkSteelThreshold.TransitionConsequences

namespace PowerLawSmallRAF
open Classical Filter Topology MeasureTheory HordijkSteelThreshold RAF.Polymer unitInterval
noncomputable section

theorem sourceFullIntensity_eq_criticalLambda : sourceFullIntensity = criticalLambda (-2) := by
  have hf : Real.exp (2*Real.log 2) = 4 := by
    rw [show (2 : ℝ)*Real.log 2 = Real.log 2+Real.log 2 by ring,Real.exp_add,
      Real.exp_log (by norm_num : (0 : ℝ)<2)]
    norm_num
  rw [sourceFullIntensity,criticalPartialMass_full_eq,criticalLambda]
  norm_num only [show (-2 : ℝ) ≠ 0 by norm_num,if_false,neg_neg]
  rw [hf]
  ring

theorem sourceCriticalOpenness_gt_half : (1/2 : ℝ) < (sourceCriticalOpenness : ℝ) := by
  have hp : Real.pi^2 < 10 := by nlinarith [Real.pi_pos,Real.pi_lt_d2]
  have hl : (9/10 : ℝ) < criticalLambda (-2) := by
    rw [← sourceFullIntensity_eq_criticalLambda,sourceFullIntensity,criticalPartialMass_full_eq]
    apply (lt_div_iff₀ (by positivity : 0 < Real.pi^2/6)).mpr
    nlinarith
  have hlog : Real.log 2 < criticalLambda (-2) := by linarith [Real.log_two_lt_d9]
  have he := Real.exp_lt_exp.mpr (neg_lt_neg hlog)
  have hehalf : Real.exp (-Real.log 2) = (1/2 : ℝ) := by
    rw [Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ)<2)]
    norm_num
  rw [hehalf] at he
  change (1/2 : ℝ) < 1-Real.exp (-criticalLambda (-2))
  linarith

/-- The constructive lower comparison reaches every mass below the endpoint
survival probability, by continuity through admissible retained intensities. -/
theorem source_subexponential_RAF_endpoint_lower (r : ℝ)
    (hr : r < (staticSurvival sourceCriticalOpenness).toReal) :
    ∃ N : Nat,
      (∀ b : ℝ, 0<b → ∀ᶠ n : Nat in atTop,
        (sourceFiniteSeedConstructionBudget N n : ℝ) < (2 : ℝ)^(b*(n : ℝ))) ∧
      (∀ᶠ n : Nat in atTop, r < sourceBoundedRevRAFProbability (2-2/(n : ℝ)) n
        (sourceFiniteSeedConstructionBudget N n)) := by
  let lam := criticalLambda (-2)
  have hlam : 0 < lam := criticalLambda_pos (-2)
  let t := intensityBelow lam
  have ht (k : Nat) : 0 < t k ∧ t k < lam := intensityBelow_bounds hlam k
  let q := fun k => transitionOpenness (t k) (ht k).1
  have hq : Tendsto q atTop (𝓝 sourceCriticalOpenness) := by
    exact transitionOpenness_tendsto (fun k => (ht k).1) hlam (intensityBelow_tendsto lam)
  have hhalf := ((continuous_subtype_val.continuousAt.tendsto.comp hq).eventually
    (Ioi_mem_nhds sourceCriticalOpenness_gt_half))
  have hspos : 0 < (staticSurvival sourceCriticalOpenness).toReal :=
    ENNReal.toReal_pos (ne_of_gt (staticSurvival_pos sourceCriticalOpenness
      (by linarith [sourceCriticalOpenness_gt_half]))) (measure_ne_top _ _)
  obtain ⟨s,hs,hss⟩ := exists_between (max_lt hr hspos)
  have hs0 : 0 < s := (le_max_right r 0).trans_lt hs
  let c := ENNReal.ofReal s
  have hc : c < staticSurvival sourceCriticalOpenness :=
    (ENNReal.ofReal_lt_iff_lt_toReal hs0.le (measure_ne_top _ _)).mpr hss
  have hsurv := staticSurvival_tendsto
    (show 0 < (sourceCriticalOpenness : ℝ) by linarith [sourceCriticalOpenness_gt_half]) hq
  obtain ⟨k,hkh,hkc⟩ := (hhalf.and (hsurv.eventually (Ioi_mem_nhds hc))).exists
  have htr : t k < sourceFullIntensity := by
    rw [sourceFullIntensity_eq_criticalLambda]
    exact (ht k).2
  have hrc : r < c.toReal := by
    rw [ENNReal.toReal_ofReal hs0.le]
    exact (le_max_left r 0).trans_lt hs
  exact source_subexponential_RAF_survival_lower (q k) hkh (t k) htr le_rfl c hkc r hrc

end
end PowerLawSmallRAF

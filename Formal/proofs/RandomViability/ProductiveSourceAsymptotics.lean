import proofs.PowerLawSmallRAF.CriticalProfile

namespace RandomViability
open Filter Topology PowerLawSmallRAF
noncomputable section
set_option maxHeartbeats 40000

def productiveSourceMean (n : ℕ) : ℝ :=
  windowZipfMean (2-2/(n : ℝ)) (sourceReactionCount n)

def productiveSourceIncidence (n : ℕ) : ℝ := productiveSourceMean n/sourceReactionCount n

theorem productive_source_mean_normalized :
    Tendsto (fun n => productiveSourceMean n/(n : ℝ)) atTop (𝓝 (criticalLambda (-2))) := by
  simpa only [productiveSourceMean,neg_div,sub_eq_add_neg] using
    windowZipfMean_source_window_normalized (-2)

theorem productive_source_mean_eventually_pos :
    ∀ᶠ n in atTop, 0 < productiveSourceMean n := by
  have hp := productive_source_mean_normalized.eventually (eventually_gt_nhds (criticalLambda_pos (-2)))
  filter_upwards [hp,eventually_ge_atTop 1] with n hn hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  exact (div_pos_iff_of_pos_right hnR).mp hn

theorem productive_source_log_mean_negligible :
    Tendsto (fun n => Real.log (productiveSourceMean n)/(n : ℝ)) atTop (𝓝 0) := by
  have hlog := (Real.continuousAt_log (criticalLambda_pos (-2)).ne').tendsto.comp
    productive_source_mean_normalized
  have hsmall := hlog.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hnlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hh := hsmall.add hnlog
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [productive_source_mean_eventually_pos,eventually_ge_atTop 1] with n hf hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  dsimp only [Function.comp_apply, id_eq]
  rw [Real.log_div hf.ne' hn0]
  ring

/-- The exact source incidence has exponential rate -log2 in the stated
critical Zipf window. No numerical fit is used. -/
theorem productive_source_incidence_log_rate :
    Tendsto (fun n => Real.log (productiveSourceIncidence n)/(n : ℝ))
      atTop (𝓝 (-Real.log 2)) := by
  have hh := productive_source_log_mean_negligible.sub log_sourceReactionCount_normalized
  simp only [zero_sub] at hh
  apply hh.congr'
  filter_upwards [productive_source_mean_eventually_pos] with n hf
  have hR : (sourceReactionCount n : ℝ) ≠ 0 := by
    exact_mod_cast (show sourceReactionCount n ≠ 0 by unfold sourceReactionCount; omega)
  rw [productiveSourceIncidence,Real.log_div hf.ne' hR]
  ring

end
end RandomViability

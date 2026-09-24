import proofs.PowerLawSmallRAF.GatewayMarks

namespace PowerLawSmallRAF

open Filter Topology

/-- At every endpoint-scale threshold, the size-biased mass above the
threshold vanishes in a nonzero explicit critical window. -/
theorem sizeBiasedHighTail_source_window_of_ne_zero
    (m : Nat → Nat) (b : ℝ) (hb : b ≠ 0)
    (hlog : Tendsto (fun n : Nat => Real.log (m n : ℝ) / (n : ℝ))
      atTop (𝓝 (Real.log 2)))
    (hm : Tendsto m atTop atTop) :
    Tendsto (fun n : Nat => 1 - sizeBiasedLogCdf (2 + b / (n : ℝ))
      (sourceReactionCount n) (m n)) atTop (𝓝 0) := by
  have hcdf := sizeBiasedLogCdf_source_window_of_ne_zero
    m b (Real.log 2) hb hlog hm
  have hexp : Real.exp (-b * Real.log 2) = (2 : ℝ) ^ (-b) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hlimit :
      1 - (((1 - Real.exp (-b * Real.log 2)) / b) /
        ((1 - (2 : ℝ) ^ (-b)) / b)) = 0 := by
    rw [hexp]
    have hpow : (2 : ℝ) ^ (-b) ≠ 1 := by
      intro heq
      have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
      have harg : Real.log 2 * (-b) = 0 := by
        apply Real.exp_injective
        simpa [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)] using heq
      rcases mul_eq_zero.mp harg with hzero | hzero
      · exact hlog2 hzero
      · exact hb (neg_eq_zero.mp hzero)
    field_simp [hb, sub_ne_zero.mpr hpow]
    ring
  simpa only [hlimit] using
    (tendsto_const_nhds : Tendsto (fun _ : Nat => (1 : ℝ)) atTop (𝓝 1)).sub hcdf

/-- The same endpoint high-tail extinction at the removable window `b=0`. -/
theorem sizeBiasedHighTail_source_window_zero
    (m : Nat → Nat)
    (hlog : Tendsto (fun n : Nat => Real.log (m n : ℝ) / (n : ℝ))
      atTop (𝓝 (Real.log 2)))
    (hm : Tendsto m atTop atTop) :
    Tendsto (fun n : Nat => 1 - sizeBiasedLogCdf 2
      (sourceReactionCount n) (m n + 1)) atTop (𝓝 0) := by
  have hcdf := sizeBiasedLogCdf_source_window_zero m (Real.log 2) hlog hm
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  have hlimit : 1 - Real.log 2 / Real.log 2 = 0 := by
    field_simp
    ring
  simpa only [hlimit] using
    (tendsto_const_nhds : Tendsto (fun _ : Nat => (1 : ℝ)) atTop (𝓝 1)).sub hcdf

end PowerLawSmallRAF

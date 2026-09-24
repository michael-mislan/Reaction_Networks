import proofs.PowerLawSmallRAF.SeedClosed

namespace PowerLawSmallRAF
open Filter Topology
noncomputable section

theorem sourceExactCriticalExponent_tendsto :
    Tendsto (fun n : Nat => 2-2/(n : ℝ)) atTop (𝓝 2) := by
  have hh : Tendsto (fun n : Nat => (2 : ℝ)/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [sub_zero] using (tendsto_const_nhds.sub hh :
    Tendsto (fun n : Nat => (2 : ℝ)-2/(n : ℝ)) atTop (𝓝 (2-0)))

/-- Full capped-Zipf second moment, including the cap atom. Its scaled
vanishing controls fixed-channel correlations for the exact source sequence. -/
theorem sourceExactCriticalSecondMoment_scaled_tendsto_zero :
    Tendsto (fun n : Nat => (sourceMoleculeCount n : ℝ)*
      windowZipfSecondMoment (2-2/(n : ℝ)) (sourceReactionCount n)/(sourceReactionCount n : ℝ)^2)
      atTop (𝓝 0) := by
  have hf : Tendsto (fun n : Nat => (sourceReactionCount n : ℝ)^((2 : ℝ)/(n : ℝ)))
      atTop (𝓝 ((2 : ℝ)^ (2 : ℝ))) := by
    simpa only [neg_neg] using sourceReactionCount_rpow_window (-2)
  have hz : Tendsto (fun n : Nat => zipfNormalizer (2-2/(n : ℝ))) atTop (𝓝 (Real.pi^2/6)) := by
    simpa only [zipfNormalizer_two] using
      (continuousAt_zipfNormalizer one_lt_two).tendsto.comp sourceExactCriticalExponent_tendsto
  have hu := sourceMoleculeCount_div_reactionCount_tendsto_zero.mul
    ((hf.const_mul 4).div hz (by positivity : Real.pi^2/6 ≠ 0))
  simp only [zero_mul] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [hz.eventually (Ioi_mem_nhds (by positivity : (0 : ℝ)<Real.pi^2/6))] with n hzp
    have hm : 0 ≤ windowZipfSecondMoment (2-2/(n : ℝ)) (sourceReactionCount n) :=
      div_nonneg (windowZipfSecondNumerator_nonneg _ _) hzp.le
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hm) (sq_nonneg _)
  · filter_upwards [eventually_ge_atTop 4,
      sourceExactCriticalExponent_tendsto.eventually (Ici_mem_nhds (by norm_num : (3/2 : ℝ)<2)),
      hz.eventually (Ioi_mem_nhds (by positivity : (0 : ℝ)<Real.pi^2/6))] with n hn ha hzp
    have hRnat : 2 ≤ sourceReactionCount n := by simp [sourceReactionCount]
    have hb := windowZipfSecondNumerator_le_four_mul (2-2/(n : ℝ)) 2 n
      (sourceReactionCount n) (by norm_num) ha le_rfl hRnat
    have hm := div_le_div_of_nonneg_right hb hzp.le
    have hs := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (sourceMoleculeCount n)))
      (sq_nonneg (sourceReactionCount n : ℝ))
    have hR : (sourceReactionCount n : ℝ) ≠ 0 := by exact_mod_cast (show sourceReactionCount n ≠ 0 by omega)
    change (sourceMoleculeCount n : ℝ)*windowZipfSecondMoment _ _/(sourceReactionCount n : ℝ)^2 ≤ _
    apply hs.trans_eq
    dsimp only [Pi.div_apply]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp

theorem sourceExactCriticalFirstMoment_scaled_tendsto :
    Tendsto (fun n : Nat => (sourceMoleculeCount n : ℝ)*
      windowZipfMean (2-2/(n : ℝ)) (sourceReactionCount n)/(sourceReactionCount n : ℝ))
      atTop (𝓝 (criticalLambda (-2))) := by
  have hm := windowZipfMean_source_window_normalized (-2)
  have hratio := sourceReactionCount_div_nat_molecule_tendsto_one.inv₀ one_ne_zero
  have hh := hratio.mul hm
  simp only [inv_one,one_mul,neg_div] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hR : (sourceReactionCount n : ℝ) ≠ 0 := by simp [sourceReactionCount]; positivity
  simp only [sub_eq_add_neg]
  field_simp

end
end PowerLawSmallRAF

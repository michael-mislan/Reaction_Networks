import proofs.RepeatedFunction.EnsembleBounds

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 100000

theorem c6_zipf_normalizer_pos (a : ℝ) (ha : 1 < a) : 0 < zipfNormalizer a := by
  rw [zipfNormalizer_eq_prefix_add_tail ha 2,zipfPrefix_two ha]
  nlinarith [rpowTail_nonneg a 2]

theorem c6_incidence_pos (a : ℝ) (ha : 1 < a) (n : ℕ) :
    0 < powerLawMoleculeGatewayHit a (sourceReactionCount n) 1 := by
  have hR : 3 ≤ sourceReactionCount n := by unfold sourceReactionCount; omega
  rw [powerLawMoleculeGatewayHit_one_eq_mean_div a _ ha (by omega)]
  apply div_pos
  · unfold windowZipfMean windowDirectNumerator
    apply div_pos _ (c6_zipf_normalizer_pos a ha)
    have hs : 0 < ∑ k ∈ Finset.Ico 2 (sourceReactionCount n),
        (((k-1 : ℕ) : ℝ)*(k : ℝ)^(-a)) := by
      apply Finset.sum_pos'
      · intro k _
        positivity
      · refine ⟨2,Finset.mem_Ico.mpr ⟨le_rfl,by omega⟩,?_⟩
        norm_num
        positivity
    exact add_pos_of_pos_of_nonneg hs (cappedRpowTail_nonneg a _)
  · exact_mod_cast (show 0 < sourceReactionCount n by omega)

theorem c6_source_witness_mass_pos (a : ℝ) (ha : 1 < a) (n : ℕ) :
    0 < sourceEmptyRowMass a n ^ 6*powerLawMoleculeGatewayHit a (sourceReactionCount n) 1 := by
  rw [source_empty_row_mass_eq]
  exact mul_pos (pow_pos (div_pos (by norm_num) (c6_zipf_normalizer_pos a ha)) _)
    (c6_incidence_pos a ha n)

theorem two_window_quadratic_volume_scale (n V : ℝ) (hn : 1 ≤ n)
    (hV : (10^60 : ℝ)*(n+1)^2 ≤ V) :
    2*n/markedNoiseDelta ≤ V ∧ 3*n ≤ twoWindowNoiseRate*V/n ∧
      48 ≤ twoWindowNoiseRate*V/n := by
  have hn0 : 0 < n := by linarith only [hn]
  refine ⟨(collective_quadratic_volume_scale n V hn hV).1,?_,?_⟩
  · apply (le_div_iff₀ hn0).2
    norm_num [twoWindowNoiseRate,markedNoiseDelta]
    nlinarith only [hV,sq_nonneg n,hn]
  · apply (le_div_iff₀ hn0).2
    norm_num [twoWindowNoiseRate,markedNoiseDelta]
    nlinarith only [hV,sq_nonneg n,hn]

theorem two_window_noise_factor_ge_half (x : ℝ) (hx : 48 ≤ x) :
    (1/2 : ℝ) ≤ 1-24*Real.exp (-x) := by
  have he : 48 ≤ Real.exp x := by linarith only [Real.add_one_le_exp x,hx]
  have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 48) he
  rw [Real.exp_neg]
  change 1/Real.exp x ≤ 1/48 at hi
  simp only [one_div] at hi
  linarith only [hi]

local instance positiveChannelSpace (n : ℕ) : MeasurableSpace (PhysicalCountChannel n) := ⊤
local instance positiveChannelSingleton (n : ℕ) : MeasurableSingletonClass (PhysicalCountChannel n) := ⟨fun _ => trivial⟩

/-- An explicit nonvacuous volume envelope, not an assumed positive weight. -/
theorem two_window_source_probability_positive {n : ℕ} (hn : 4 ≤ n) (V : ℕ)
    (hV : collectiveMinimalVolume n ≤ V) (a : ℝ) (ha : 1 < a) :
    0 < averagedMissionProbability hn V ((collective_minimal_volume_pos n).trans_le hV) a (fun _ => True) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hvR : (10^60 : ℝ)*((n : ℝ)+1)^2 ≤ (V : ℝ) := by exact_mod_cast hV
  have hs := two_window_quadratic_volume_scale n V hnR hvR
  have hl := averaged_mission_lower hn V ((collective_minimal_volume_pos n).trans_le hV)
    hs.1 a ha (fun _ => True) (fun _ _ => trivial)
  have hp := c6_source_witness_mass_pos a ha n
  have hf := two_window_noise_factor_ge_half _ hs.2.2
  exact (mul_pos hp (by linarith only [hf])).trans_le hl

end
end RandomViability

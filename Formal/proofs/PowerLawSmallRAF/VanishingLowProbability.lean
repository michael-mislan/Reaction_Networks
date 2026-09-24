import proofs.PowerLawSmallRAF.VanishingLowConcentration

namespace PowerLawSmallRAF
open Classical RAF RAF.Polymer RAF.Concrete Filter Topology
open scoped BigOperators
noncomputable section

theorem sourceVanishingLowDeficitMass_tendsto_zero (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (sourceVanishingLowDeficitMass δ) atTop (𝓝 0) := by
  have hu : Tendsto (fun n => 1/(δ^2*sourceVanishingLowMean n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (sourceVanishingLowMean_tendsto_atTop.const_mul_atTop (by positivity))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [eventually_ge_atTop 4] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have ha : 1 < 2-2/(n : ℝ) := by
      have h : (2 : ℝ)/(n : ℝ) < 1 := (div_lt_one hnpos).mpr (by exact_mod_cast (show 2 < n by omega))
      linarith
    apply Finset.sum_nonneg
    intro config _
    split_ifs
    · exact sourcePowerLawConfigWeight_nonneg _ _ ha config
    · exact le_rfl
  · filter_upwards [eventually_ge_atTop 4,
      sourceVanishingLowMean_tendsto_atTop.eventually (eventually_gt_atTop 0)] with n hn hm
    exact sourceVanishingLowDeficitMass_le δ hδ n hn hm

def sourceVanishingLowIntensityValue (n : Nat) (config : SourceMoleculeFibreConfig n) : ℝ :=
  sourceVanishingLowRetention n / (sourceReactionCount n : ℝ) *
    ∑ x : Molecule n, truncatedBandValue (sourceVanishingLowLower n) (sourceShrinkingLower n) (config x)

def sourceVanishingLowIntensityFailureMass (t : ℝ) (n : Nat) : ℝ :=
  ∑ config : SourceMoleculeFibreConfig n,
    if sourceVanishingLowIntensityValue n config < t
    then sourcePowerLawConfigWeight (2-2/(n : ℝ)) n config else 0

/-- Every fixed threshold strictly below the full intensity is attained
with probability tending to one under the original fixed-size-fibre law. -/
theorem sourceVanishingLowIntensityFailureMass_tendsto_zero (t : ℝ) (ht : t < sourceFullIntensity) :
    Tendsto (sourceVanishingLowIntensityFailureMass t) atTop (𝓝 0) := by
  have hgap : 0 < 1-t/sourceFullIntensity := by
    have h := (div_lt_one sourceFullIntensity_pos).mpr ht
    linarith
  obtain ⟨δ,hδ,hδgap⟩ := exists_between hgap
  have htarget : t < (1-δ)*sourceFullIntensity := by
    have h := (lt_div_iff₀ sourceFullIntensity_pos).mp (show δ < (sourceFullIntensity-t)/sourceFullIntensity by
      convert hδgap using 1
      field_simp [ne_of_gt sourceFullIntensity_pos])
    nlinarith
  have hlim := (tendsto_const_nhds : Tendsto (fun _ : Nat => 1-δ) atTop (𝓝 (1-δ))).mul
    sourceVanishingLowRetainedMean_tendsto
  have hev := hlim.eventually (Ioi_mem_nhds htarget)
  have hbound : ∀ᶠ n : Nat in atTop,
      sourceVanishingLowIntensityFailureMass t n ≤ sourceVanishingLowDeficitMass δ n := by
    filter_upwards [eventually_ge_atTop 4,hev] with n hn hb
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have ha : 1 < 2-2/(n : ℝ) := by
      have h : (2 : ℝ)/(n : ℝ) < 1 := (div_lt_one hnpos).mpr (by exact_mod_cast (show 2 < n by omega))
      linarith
    have hs : t < sourceVanishingLowRetention n / (sourceReactionCount n : ℝ) *
        ((1-δ)*(sourceMoleculeCount n : ℝ)*sourceVanishingLowMean n) := by
      convert hb using 1
      ring
    apply Finset.sum_le_sum
    intro config _
    have hw := sourcePowerLawConfigWeight_nonneg _ _ ha config
    by_cases hf : sourceVanishingLowIntensityValue n config < t
    · have hd : (∑ x : Molecule n, truncatedBandValue (sourceVanishingLowLower n) (sourceShrinkingLower n) (config x)) <
          (1-δ)*(sourceMoleculeCount n : ℝ)*sourceVanishingLowMean n := by
        by_contra hnot
        have hh := mul_le_mul_of_nonneg_left (le_of_not_gt hnot)
          (div_nonneg (sourceVanishingLowRetention_bounds n).1 (Nat.cast_nonneg (sourceReactionCount n)))
        change _ ≤ sourceVanishingLowIntensityValue n config at hh
        linarith
      simp only [if_pos hf,if_pos hd,le_refl]
    · simp only [if_neg hf]
      split_ifs <;> linarith
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (sourceVanishingLowDeficitMass_tendsto_zero δ hδ) _ hbound
  filter_upwards [eventually_ge_atTop 4] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ha : 1 < 2-2/(n : ℝ) := by
    have h : (2 : ℝ)/(n : ℝ) < 1 := (div_lt_one hnpos).mpr (by exact_mod_cast (show 2 < n by omega))
    linarith
  apply Finset.sum_nonneg
  intro config _
  split_ifs
  · exact sourcePowerLawConfigWeight_nonneg _ _ ha config
  · exact le_rfl

end
end PowerLawSmallRAF

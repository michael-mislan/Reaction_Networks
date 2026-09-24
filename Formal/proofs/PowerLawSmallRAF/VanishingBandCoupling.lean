import proofs.PowerLawSmallRAF.VanishingBandParameter

namespace PowerLawSmallRAF
open Classical RAF RAF.Polymer RAF.Concrete Filter Topology
open scoped BigOperators
noncomputable section

def sourceVanishingBandOverflowMass (n : Nat) : ℝ :=
  sourceMixedRowOverflowMass (2-2/(n : ℝ)) n (sourceVanishingBandParameter n)

theorem sourceVanishingBandOverflowMass_eventually_le :
    ∀ᶠ n : Nat in atTop, sourceVanishingBandOverflowMass n ≤ sourceVanishingRowErrorEnvelope n := by
  have he := sourceVanishingRowSlack_tendsto.eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/20))
  filter_upwards [sourceVanishingLow_eventual_bounds,he] with n hb he
  have hn := hb.1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ha : 1 < 2-2/(n : ℝ) := by
    have h : (2 : ℝ)/(n : ℝ) < 1 := (div_lt_one hnpos).mpr (by exact_mod_cast (show 2 < n by omega))
    linarith
  exact sourceMixedRowOverflowMass_le_variable_slack _ n (sourceVanishingLowLower n) ha hn
    (sourceVanishingRowSlack n) (sourceVanishingRowSlack_pos n).le (sourceVanishingBandParameter n)
    (fun d x => (sourceVanishingBandParameter_bounds n hn d x).1)
    (fun d x => (sourceVanishingBandParameter_bounds n hn d x).2)
    (sourceVanishingBandParameter_small n hb.2.2.1)
    (sourceVanishingBandParameter_slack n hn he.le)

theorem sourceVanishingBandOverflowMass_tendsto_zero :
    Tendsto sourceVanishingBandOverflowMass atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    sourceVanishingRowErrorEnvelope_tendsto_zero _ sourceVanishingBandOverflowMass_eventually_le
  filter_upwards [eventually_ge_atTop 4] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ha : 1 < 2-2/(n : ℝ) := by
    have h : (2 : ℝ)/(n : ℝ) < 1 := (div_lt_one hnpos).mpr (by exact_mod_cast (show 2 < n by omega))
    linarith
  exact sourceMixedRowOverflowMass_nonneg _ n ha (sourceVanishingBandParameter n)
    (fun d x => (sourceVanishingBandParameter_bounds n hn d x).1)
    (fun d x => (sourceVanishingBandParameter_bounds n hn d x).2)

def sourceVanishingBandAuxiliaryRAFMass (n m : Nat) : ℝ :=
  ∑ d : SourceDegreeConfig n, sourceDegreeWeight (2-2/(n : ℝ)) n d *
    ∑ B : SourceMoleculeFibreConfig n,
      if ∃ S : Finset (Reaction n), S.card ≤ m ∧
        IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig B) S
      then bernoulliRowsWeight (sourceVanishingBandParameter n d) B else 0

/-- Every auxiliary bounded-RAF event transfers to the original source
with the same vanishing error, uniformly in the chosen size budget. -/
theorem sourceVanishingBandAuxiliaryRAFMass_eventually_le_source :
    ∀ᶠ n : Nat in atTop, ∀ m : Nat, sourceVanishingBandAuxiliaryRAFMass n m ≤
      sourceBoundedRevRAFProbability (2-2/(n : ℝ)) n m + sourceVanishingRowErrorEnvelope n := by
  filter_upwards [eventually_ge_atTop 4,sourceVanishingBandOverflowMass_eventually_le] with n hn he
  intro m
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ha : 1 < 2-2/(n : ℝ) := by
    have h : (2 : ℝ)/(n : ℝ) < 1 := (div_lt_one hnpos).mpr (by exact_mod_cast (show 2 < n by omega))
    linarith
  have h := sourceBoundedRevRAFProbability_ge_degree_coupling _ n m ha (sourceVanishingBandParameter n)
    (fun d x => (sourceVanishingBandParameter_bounds n hn d x).1)
    (fun d x => (sourceVanishingBandParameter_bounds n hn d x).2)
  exact h.trans (add_le_add le_rfl he)

end
end PowerLawSmallRAF

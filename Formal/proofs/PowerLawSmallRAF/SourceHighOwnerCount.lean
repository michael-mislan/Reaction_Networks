import proofs.PowerLawSmallRAF.SourceOwnerMarkov
import proofs.PowerLawSmallRAF.SourceShrinkingBandMean

namespace PowerLawSmallRAF
open RAF RAF.Polymer RAF.Concrete Filter Topology
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 100000

def sourceHighOwnerCountFailureMass (n : Nat) : ℝ :=
  ∑ config : SourceMoleculeFibreConfig n,
    if (n : ℝ)^3*(2 : ℝ)^(shrinkingBandWidth n) ≤
      sourceOwnerThresholdCount n Finset.univ (sourceShrinkingLower n) config
    then sourcePowerLawConfigWeight (2-2/(n : ℝ)) n config else 0

theorem sourceHighOwnerCountFailureMass_eventually_le :
    ∀ᶠ n : Nat in atTop,
      sourceHighOwnerCountFailureMass n ≤ 4/(n : ℝ)^2 := by
  filter_upwards [sourceShrinkingBand_eventual_bounds, sourceTotalDegreeMean_eventually_le] with n hn hm
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ha : 1 < 2-2/(n : ℝ) := by
    have h : (2 : ℝ)/(n : ℝ) < 1 := (div_lt_one hnpos).mpr (by exact_mod_cast (show 2 < n by omega))
    linarith
  have hLpos : (0 : ℝ) < sourceShrinkingLower n := by
    exact_mod_cast (show 0 < sourceShrinkingLower n by omega)
  have hpow : (0 : ℝ) < (2 : ℝ)^(shrinkingBandWidth n) := by positivity
  have hmark := source_owner_count_markov (2-2/(n : ℝ)) n ha hn.1 Finset.univ
    (sourceShrinkingLower n) (by omega) ((n : ℝ)^3*(2 : ℝ)^(shrinkingBandWidth n)) (by positivity)
  simp only [Finset.card_univ, card_binaryMolecule_eq_sourceMoleculeCount] at hmark
  have hproduct : sourceShrinkingLower n * 2^(shrinkingBandWidth n) = 2^n := by
    rw [sourceShrinkingLower, ← pow_add, Nat.sub_add_cancel hn.2.2.1.le]
  have hNnat : sourceMoleculeCount n ≤ 2*(sourceShrinkingLower n * 2^(shrinkingBandWidth n)) := by
    rw [hproduct]
    unfold sourceMoleculeCount
    rw [pow_succ]
    omega
  have hN : (sourceMoleculeCount n : ℝ) ≤
      2*((sourceShrinkingLower n : ℝ)*(2 : ℝ)^(shrinkingBandWidth n)) := by exact_mod_cast hNnat
  have hnum : (sourceMoleculeCount n : ℝ)*windowZipfMean (2-2/(n : ℝ)) (sourceReactionCount n) ≤
      4*(n : ℝ)*(sourceShrinkingLower n : ℝ)*(2 : ℝ)^(shrinkingBandWidth n) := by
    calc
      _ ≤ (sourceMoleculeCount n : ℝ)*(2*(n : ℝ)) := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)
      _ ≤ (2*((sourceShrinkingLower n : ℝ)*(2 : ℝ)^(shrinkingBandWidth n)))*(2*(n : ℝ)) :=
        mul_le_mul_of_nonneg_right hN (by positivity)
      _ = _ := by ring
  apply hmark.trans
  calc
    _ ≤ (4*(n : ℝ)*(sourceShrinkingLower n : ℝ)*(2 : ℝ)^(shrinkingBandWidth n))/
        ((sourceShrinkingLower n : ℝ)*((n : ℝ)^3*(2 : ℝ)^(shrinkingBandWidth n))) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = _ := by
      field_simp

theorem sourceHighOwnerCountFailureMass_tendsto_zero :
    Tendsto sourceHighOwnerCountFailureMass atTop (𝓝 0) := by
  have hi : Tendsto (fun n : Nat => (1 : ℝ)/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hu : Tendsto (fun n : Nat => (4 : ℝ)/(n : ℝ)^2) atTop (𝓝 0) := by
    have h := (hi.mul hi).const_mul 4
    simp only [mul_zero] at h
    convert h using 1
    funext n
    ring
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
  · exact sourceHighOwnerCountFailureMass_eventually_le

end
end PowerLawSmallRAF

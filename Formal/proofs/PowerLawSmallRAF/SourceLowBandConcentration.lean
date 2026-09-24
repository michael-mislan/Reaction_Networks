import proofs.PowerLawSmallRAF.SourceLowBandBudget

namespace PowerLawSmallRAF
open RAF RAF.Polymer RAF.Concrete
open Filter Topology
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 100000

theorem sourceLowBandMean_tendsto_atTop : Tendsto sourceLowBandMean atTop atTop := by
  have hc : 0 < sourceLowBandIntegralLimit/(Real.pi^2/6) := by
    have hp : 0 < sourceLowBandIntegralLimit := by linarith [sourceLowBandIntegralLimit_lower]
    positivity
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_pos hc sourceLowBandMean_tendsto
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp

def sourceLowBandDeficitMass (n : Nat) : ℝ :=
  ∑ config : SourceMoleculeFibreConfig n,
    if (∑ x : Molecule n, truncatedBandValue (sourceLowBandLower n) (sourceShrinkingLower n) (config x)) <
      (49/50 : ℝ)*(sourceMoleculeCount n : ℝ)*sourceLowBandMean n
    then sourcePowerLawConfigWeight (2-2/(n : ℝ)) n config else 0

theorem sourceLowBandDeficitMass_le (n : Nat) (hn : 4 ≤ n)
    (hm : 0 < sourceLowBandMean n) :
    sourceLowBandDeficitMass n ≤ 2500/sourceLowBandMean n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ha : 1 < 2-2/(n : ℝ) := by
    have h : (2 : ℝ)/(n : ℝ) < 1 := (div_lt_one hnpos).mpr (by exact_mod_cast (show 2 < n by omega))
    linarith
  have hpow : 2 ≤ 2^n := by
    exact (show 2^1 ≤ 2^n from Nat.pow_le_pow_right (by omega) (by omega))
  have hN : 2^n ≤ sourceMoleculeCount n := by
    unfold sourceMoleculeCount
    rw [pow_succ]
    omega
  have hNpos : (0 : ℝ) < sourceMoleculeCount n := by exact_mod_cast (show 0 < sourceMoleculeCount n by omega)
  have hUN : (sourceShrinkingLower n : ℝ) ≤ sourceMoleculeCount n := by
    exact_mod_cast ((Nat.pow_le_pow_right (by omega : 1 ≤ 2) (Nat.sub_le n (shrinkingBandWidth n))).trans hN)
  let eps : ℝ := (1/50 : ℝ)*(sourceMoleculeCount n : ℝ)*sourceLowBandMean n
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hcheb := sourceTruncatedBand_chebyshev_sq (2-2/(n : ℝ)) n
    (sourceLowBandLower n) (sourceShrinkingLower n) ha hn heps
  have hinc : sourceLowBandDeficitMass n ≤
      ∑ config : SourceMoleculeFibreConfig n,
        if eps^2 ≤ (∑ x : Molecule n,
          (truncatedBandValue (sourceLowBandLower n) (sourceShrinkingLower n) (config x)-sourceLowBandMean n))^2
        then sourcePowerLawConfigWeight (2-2/(n : ℝ)) n config else 0 := by
    apply Finset.sum_le_sum
    intro config _
    have hw := sourcePowerLawConfigWeight_nonneg (2-2/(n : ℝ)) n ha config
    have hcenter : (∑ x : Molecule n,
        (truncatedBandValue (sourceLowBandLower n) (sourceShrinkingLower n) (config x)-sourceLowBandMean n)) =
        (∑ x : Molecule n, truncatedBandValue (sourceLowBandLower n) (sourceShrinkingLower n) (config x)) -
          (sourceMoleculeCount n : ℝ)*sourceLowBandMean n := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, card_binaryMolecule_eq_sourceMoleculeCount]
    by_cases hd : (∑ x : Molecule n, truncatedBandValue (sourceLowBandLower n) (sourceShrinkingLower n) (config x)) <
        (49/50 : ℝ)*(sourceMoleculeCount n : ℝ)*sourceLowBandMean n
    · have hs : eps^2 ≤ (∑ x : Molecule n,
          (truncatedBandValue (sourceLowBandLower n) (sourceShrinkingLower n) (config x)-sourceLowBandMean n))^2 := by
        rw [hcenter]
        dsimp [eps] at heps ⊢
        nlinarith only [hd, heps]
      simp only [if_pos hd, if_pos hs, le_refl]
    · simp only [if_neg hd]
      split_ifs <;> linarith only [hw]
  apply hinc.trans
  apply (show _ ≤ _ from hcheb).trans
  change ((sourceMoleculeCount n : ℝ)*(sourceShrinkingLower n : ℝ)*sourceLowBandMean n)/eps^2 ≤ _
  calc
    _ = 2500*((sourceShrinkingLower n : ℝ)/(sourceMoleculeCount n : ℝ))/sourceLowBandMean n := by
      dsimp [eps]
      field_simp
      ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hm.le
      apply mul_le_of_le_one_right (by norm_num : (0 : ℝ) ≤ 2500)
      exact (div_le_one hNpos).mpr hUN

theorem sourceLowBandDeficitMass_tendsto_zero :
    Tendsto sourceLowBandDeficitMass atTop (𝓝 0) := by
  have hu : Tendsto (fun n => (2500 : ℝ)/sourceLowBandMean n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop sourceLowBandMean_tendsto_atTop
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
      sourceLowBandMean_tendsto_atTop.eventually (eventually_gt_atTop 0)] with n hn hm
    exact sourceLowBandDeficitMass_le n hn hm

end
end PowerLawSmallRAF

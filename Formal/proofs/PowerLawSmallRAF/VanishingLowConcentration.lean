import proofs.PowerLawSmallRAF.VanishingLowIntensity
import proofs.PowerLawSmallRAF.SourceLowBandConcentration

namespace PowerLawSmallRAF
open RAF RAF.Polymer RAF.Concrete Filter Topology
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def sourceVanishingLowDeficitMass (δ : ℝ) (n : Nat) : ℝ :=
  ∑ config : SourceMoleculeFibreConfig n,
    if (∑ x : Molecule n, truncatedBandValue (sourceVanishingLowLower n) (sourceShrinkingLower n) (config x)) <
      (1-δ)*(sourceMoleculeCount n : ℝ)*sourceVanishingLowMean n
    then sourcePowerLawConfigWeight (2-2/(n : ℝ)) n config else 0

theorem sourceVanishingLowDeficitMass_le (δ : ℝ) (hδ : 0 < δ) (n : Nat) (hn : 4 ≤ n)
    (hm : 0 < sourceVanishingLowMean n) :
    sourceVanishingLowDeficitMass δ n ≤ 1/(δ^2*sourceVanishingLowMean n) := by
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
  let eps : ℝ := δ*(sourceMoleculeCount n : ℝ)*sourceVanishingLowMean n
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hcheb := sourceTruncatedBand_chebyshev_sq (2-2/(n : ℝ)) n
    (sourceVanishingLowLower n) (sourceShrinkingLower n) ha hn heps
  have hinc : sourceVanishingLowDeficitMass δ n ≤
      ∑ config : SourceMoleculeFibreConfig n,
        if eps^2 ≤ (∑ x : Molecule n,
          (truncatedBandValue (sourceVanishingLowLower n) (sourceShrinkingLower n) (config x)-sourceVanishingLowMean n))^2
        then sourcePowerLawConfigWeight (2-2/(n : ℝ)) n config else 0 := by
    apply Finset.sum_le_sum
    intro config _
    have hw := sourcePowerLawConfigWeight_nonneg (2-2/(n : ℝ)) n ha config
    have hcenter : (∑ x : Molecule n,
        (truncatedBandValue (sourceVanishingLowLower n) (sourceShrinkingLower n) (config x)-sourceVanishingLowMean n)) =
        (∑ x : Molecule n, truncatedBandValue (sourceVanishingLowLower n) (sourceShrinkingLower n) (config x)) -
          (sourceMoleculeCount n : ℝ)*sourceVanishingLowMean n := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, card_binaryMolecule_eq_sourceMoleculeCount]
    by_cases hd : (∑ x : Molecule n, truncatedBandValue (sourceVanishingLowLower n) (sourceShrinkingLower n) (config x)) <
        (1-δ)*(sourceMoleculeCount n : ℝ)*sourceVanishingLowMean n
    · have hs : eps^2 ≤ (∑ x : Molecule n,
          (truncatedBandValue (sourceVanishingLowLower n) (sourceShrinkingLower n) (config x)-sourceVanishingLowMean n))^2 := by
        rw [hcenter]
        dsimp [eps] at heps ⊢
        nlinarith only [hd, heps]
      simp only [if_pos hd, if_pos hs, le_refl]
    · simp only [if_neg hd]
      split_ifs <;> linarith only [hw]
  apply hinc.trans
  apply (show _ ≤ _ from hcheb).trans
  change ((sourceMoleculeCount n : ℝ)*(sourceShrinkingLower n : ℝ)*sourceVanishingLowMean n)/eps^2 ≤ _
  calc
    _ = ((sourceShrinkingLower n : ℝ)/(sourceMoleculeCount n : ℝ))/(δ^2*sourceVanishingLowMean n) := by
      dsimp [eps]
      field_simp
    _ ≤ _ := div_le_div_of_nonneg_right ((div_le_one hNpos).mpr hUN) (by positivity)

end
end PowerLawSmallRAF

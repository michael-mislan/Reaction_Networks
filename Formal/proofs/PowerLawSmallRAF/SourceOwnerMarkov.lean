import proofs.PowerLawSmallRAF.SourceDegreeBandConcentration
import Mathlib.Analysis.Real.Pi.Bounds

namespace PowerLawSmallRAF
open RAF RAF.Polymer RAF.Concrete Filter Topology
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 100000

theorem sourceTotalDegreeMean_eventually_le :
    ∀ᶠ n : Nat in atTop,
      windowZipfMean (2-2/(n : ℝ)) (sourceReactionCount n) ≤ 2*(n : ℝ) := by
  have h := windowZipfMean_source_window_normalized_of_ne_zero (-2) (by norm_num)
  have hc : (((1-(2 : ℝ)^(-(-2 : ℝ)))/(-2))/(Real.pi^2/6)) < 2 := by
    norm_num [Real.rpow_natCast] 
    have hp : 3 < Real.pi := Real.pi_gt_three
    apply (div_lt_iff₀ (by positivity : 0 < Real.pi^2/6)).mpr
    nlinarith
  have he := h (Iio_mem_nhds hc)
  filter_upwards [he, eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn' : windowZipfMean (2-2/(n : ℝ)) (sourceReactionCount n)/(n : ℝ) < 2 := by
    simpa only [sub_eq_add_neg, neg_div] using hn
  exact ((div_lt_iff₀ hnpos).mp hn').le

theorem source_oneFibre_degree_mean (a : ℝ) (n : Nat) (hn : 4 ≤ n) :
    (∑ A : Finset (Reaction n),
      subsetDegreeWeight (cappedZipfDegreeMass a (sourceReactionCount n)) A * (A.card : ℝ)) =
      windowZipfMean a (sourceReactionCount n) := by
  have h := sum_subsetDegreeWeight_mul_cardFunction_eq
    (J := Reaction n) (cappedZipfDegreeMass a (sourceReactionCount n)) (fun d => (d : ℝ))
  rw [card_binaryReaction_eq_sourceReactionCount (by omega)] at h
  rw [h, Finset.sum_range_succ]
  have hR : 2 ≤ sourceReactionCount n := by simp [sourceReactionCount]
  have hz : cappedZipfDegreeMass a (sourceReactionCount n) (sourceReactionCount n) = 0 := by
    simp [cappedZipfDegreeMass]
  rw [hz, zero_mul, add_zero]
  exact cappedZipfDegreeFirstMoment_eq a _ hR

theorem source_coordinate_degree_mean (a : ℝ) (n : Nat) (ha : 1 < a) (hn : 4 ≤ n)
    (x : Molecule n) :
    (∑ config : SourceMoleculeFibreConfig n,
      sourcePowerLawConfigWeight a n config * ((config x).card : ℝ)) =
      windowZipfMean a (sourceReactionCount n) := by
  let p := fun A : Finset (Reaction n) =>
    subsetDegreeWeight (cappedZipfDegreeMass a (sourceReactionCount n)) A
  have hp : ∑ A, p A = 1 := by
    dsimp [p]
    rw [← card_binaryReaction_eq_sourceReactionCount (by omega : 2 ≤ n)]
    apply sum_powerLawSubsetWeight_eq_one a ha
    rw [card_binaryReaction_eq_sourceReactionCount (by omega)]
    simp [sourceReactionCount]
  have h := finiteProduct_expectation_coordinate (I := Molecule n) p
    (fun A => (A.card : ℝ)) hp x
  exact h.trans (source_oneFibre_degree_mean a n hn)

def sourceOwnerThresholdCount (n : Nat) (H : Finset (Molecule n)) (L : Nat)
    (config : SourceMoleculeFibreConfig n) : ℝ :=
  ∑ x ∈ H, if L ≤ (config x).card then (1 : ℝ) else 0

theorem source_owner_count_markov (a : ℝ) (n : Nat) (ha : 1 < a) (hn : 4 ≤ n)
    (H : Finset (Molecule n)) (L : Nat) (hL : 0 < L) (T : ℝ) (hT : 0 < T) :
    (∑ config : SourceMoleculeFibreConfig n,
      if T ≤ sourceOwnerThresholdCount n H L config then sourcePowerLawConfigWeight a n config else 0) ≤
      (H.card : ℝ)*windowZipfMean a (sourceReactionCount n)/((L : ℝ)*T) := by
  have hLT : 0 < (L : ℝ)*T := mul_pos (by exact_mod_cast hL) hT
  apply (le_div_iff₀ hLT).mpr
  rw [Finset.sum_mul]
  have hpoint (config : SourceMoleculeFibreConfig n) :
      (if T ≤ sourceOwnerThresholdCount n H L config then sourcePowerLawConfigWeight a n config else 0)*
        ((L : ℝ)*T) ≤ sourcePowerLawConfigWeight a n config * ∑ x ∈ H, ((config x).card : ℝ) := by
    have hw := sourcePowerLawConfigWeight_nonneg a n ha config
    have hcount : (L : ℝ)*sourceOwnerThresholdCount n H L config ≤
        ∑ x ∈ H, ((config x).card : ℝ) := by
      rw [sourceOwnerThresholdCount, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro x hx
      split_ifs with hd
      · simpa only [mul_one] using (show (L : ℝ) ≤ (config x).card by exact_mod_cast hd)
      · simp
    split_ifs with ht
    · apply mul_le_mul_of_nonneg_left _ hw
      exact (mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg L)).trans hcount
    · simp only [zero_mul]
      positivity
  calc
    _ ≤ ∑ config : SourceMoleculeFibreConfig n,
        sourcePowerLawConfigWeight a n config * ∑ x ∈ H, ((config x).card : ℝ) :=
      Finset.sum_le_sum (fun config _ => hpoint config)
    _ = (H.card : ℝ)*windowZipfMean a (sourceReactionCount n) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [source_coordinate_degree_mean a n ha hn, Finset.sum_const, nsmul_eq_mul]

end
end PowerLawSmallRAF

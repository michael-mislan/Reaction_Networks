import proofs.PowerLawSmallRAF.SourceActiveRowError
import proofs.PowerLawSmallRAF.SourceActiveRowErrorScale

namespace PowerLawSmallRAF
open RAF RAF.Polymer RAF.Concrete Filter Topology
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 100000

def sourceBandBernoulliParameter (n : Nat) (d : SourceDegreeConfig n) (x : Molecule n) : ℝ :=
  if sourceLowBandLower n ≤ (d x).val ∧ (d x).val < sourceShrinkingUpper n
  then (19/20 : ℝ)*(d x : ℝ)/(sourceReactionCount n : ℝ) else 0

theorem sourceBandBernoulliParameter_bounds (n : Nat) (hn : 4 ≤ n)
    (d : SourceDegreeConfig n) (x : Molecule n) :
    0 ≤ sourceBandBernoulliParameter n d x ∧ sourceBandBernoulliParameter n d x ≤ 1 ∧
    (Fintype.card (Reaction n) : ℝ)*sourceBandBernoulliParameter n d x ≤ (19/20 : ℝ)*(d x : ℝ) ∧
    ((d x).val < sourceLowBandLower n → sourceBandBernoulliParameter n d x = 0) := by
  have hR : (0 : ℝ) < sourceReactionCount n := by
    exact_mod_cast (show 0 < sourceReactionCount n by simp [sourceReactionCount])
  have hdR : (d x : ℝ) ≤ sourceReactionCount n := by
    have h := Nat.le_of_lt_succ (d x).isLt
    exact_mod_cast h.trans_eq (card_binaryReaction_eq_sourceReactionCount (by omega))
  by_cases hb : sourceLowBandLower n ≤ (d x).val ∧ (d x).val < sourceShrinkingUpper n
  · simp only [sourceBandBernoulliParameter, if_pos hb]
    refine ⟨by positivity, ?_, ?_, ?_⟩
    · apply (div_le_one hR).mpr
      have hd : (0 : ℝ) ≤ d x := Nat.cast_nonneg _
      nlinarith
    · simp only [card_binaryReaction_eq_sourceReactionCount (by omega : 2 ≤ n)]
      apply le_of_eq
      field_simp
    · intro hs
      omega
  · simp only [sourceBandBernoulliParameter, if_neg hb, mul_zero]
    exact ⟨le_rfl, by norm_num, by positivity, fun _ => True.intro⟩

def sourceTwoBandOverflowMass (n : Nat) : ℝ :=
  sourceMixedRowOverflowMass (2-2/(n : ℝ)) n (sourceBandBernoulliParameter n)

theorem sourceTwoBandOverflowMass_le (n : Nat) (hn : 4 ≤ n) :
    sourceTwoBandOverflowMass n ≤ sourceActiveRowErrorEnvelope n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ha : 1 < 2-2/(n : ℝ) := by
    have h : (2 : ℝ)/(n : ℝ) < 1 := (div_lt_one hnpos).mpr (by exact_mod_cast (show 2 < n by omega))
    linarith
  exact sourceMixedRowOverflowMass_le _ n (sourceLowBandLower n) ha hn
    (sourceBandBernoulliParameter n)
    (fun d x => (sourceBandBernoulliParameter_bounds n hn d x).1)
    (fun d x => (sourceBandBernoulliParameter_bounds n hn d x).2.1)
    (fun d x => (sourceBandBernoulliParameter_bounds n hn d x).2.2.2)
    (fun d x => (sourceBandBernoulliParameter_bounds n hn d x).2.2.1)

theorem sourceTwoBandOverflowMass_tendsto_zero :
    Tendsto sourceTwoBandOverflowMass atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds sourceActiveRowErrorEnvelope_tendsto_zero
  · filter_upwards [eventually_ge_atTop 4] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have ha : 1 < 2-2/(n : ℝ) := by
      have h : (2 : ℝ)/(n : ℝ) < 1 := (div_lt_one hnpos).mpr (by exact_mod_cast (show 2 < n by omega))
      linarith
    exact sourceMixedRowOverflowMass_nonneg _ n ha (sourceBandBernoulliParameter n)
      (fun d x => (sourceBandBernoulliParameter_bounds n hn d x).1)
      (fun d x => (sourceBandBernoulliParameter_bounds n hn d x).2.1)
  · filter_upwards [eventually_ge_atTop 4] with n hn
    exact sourceTwoBandOverflowMass_le n hn

def sourceTwoBandAuxiliaryRAFMass (n m : Nat) : ℝ :=
  ∑ d : SourceDegreeConfig n, sourceDegreeWeight (2-2/(n : ℝ)) n d *
    ∑ B : SourceMoleculeFibreConfig n,
      if ∃ S : Finset (Reaction n), S.card ≤ m ∧
        IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig B) S
      then bernoulliRowsWeight (sourceBandBernoulliParameter n d) B else 0

/-- Actual bounded-RAF event transfer with an explicit vanishing error. -/
theorem sourceTwoBandAuxiliaryRAFMass_le_source (n m : Nat) (hn : 4 ≤ n) :
    sourceTwoBandAuxiliaryRAFMass n m ≤
      sourceBoundedRevRAFProbability (2-2/(n : ℝ)) n m + sourceActiveRowErrorEnvelope n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ha : 1 < 2-2/(n : ℝ) := by
    have h : (2 : ℝ)/(n : ℝ) < 1 := (div_lt_one hnpos).mpr (by exact_mod_cast (show 2 < n by omega))
    linarith
  have h := sourceBoundedRevRAFProbability_ge_degree_coupling _ n m ha (sourceBandBernoulliParameter n)
    (fun d x => (sourceBandBernoulliParameter_bounds n hn d x).1)
    (fun d x => (sourceBandBernoulliParameter_bounds n hn d x).2.1)
  exact h.trans (add_le_add le_rfl (sourceTwoBandOverflowMass_le n hn))

end
end PowerLawSmallRAF

import proofs.PowerLawSmallRAF.SourceConditionalUnionLaw
import proofs.PowerLawSmallRAF.SourceDegreeStatistics

namespace PowerLawSmallRAF
open RAF RAF.Polymer RAF.Concrete
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 100000

def sourceDegreeBandSum (n : Nat) (d : SourceDegreeConfig n) (L U : Nat) : ℝ :=
  ∑ x : Molecule n, if L ≤ (d x).val ∧ (d x).val < U then (d x : ℝ) else 0

theorem sourceLowOwnerParameter_sum (n : Nat) (d : SourceDegreeConfig n)
    (hLU : sourceShrinkingLower n ≤ sourceShrinkingUpper n) :
    (∑ x : SourceLowOwnerGroup n d, sourceBandBernoulliParameter n d x.val) =
      (19/20 : ℝ)/(sourceReactionCount n : ℝ)*
        sourceDegreeBandSum n d (sourceLowBandLower n) (sourceShrinkingLower n) := by
  rw [← Finset.sum_subtype
    (Finset.univ.filter fun x : Molecule n => (d x).val < sourceShrinkingLower n)
    (by intro x; simp) (fun x => sourceBandBernoulliParameter n d x)]
  rw [Finset.sum_filter, sourceDegreeBandSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hlo : (d x).val < sourceShrinkingLower n
  · by_cases ha : sourceLowBandLower n ≤ (d x).val
    · have hu : (d x).val < sourceShrinkingUpper n := hlo.trans_le hLU
      simp only [sourceBandBernoulliParameter, hlo, ha, hu, and_self, ite_true]
      ring
    · simp [sourceBandBernoulliParameter, hlo, ha]
  · simp [hlo]

theorem sourceHighOwnerParameter_sum (n : Nat) (d : SourceDegreeConfig n)
    (hAL : sourceLowBandLower n ≤ sourceShrinkingLower n) :
    (∑ x : SourceHighOwnerGroup n d, sourceBandBernoulliParameter n d x.val) =
      (19/20 : ℝ)/(sourceReactionCount n : ℝ)*
        sourceDegreeBandSum n d (sourceShrinkingLower n) (sourceShrinkingUpper n) := by
  rw [← Finset.sum_subtype
    (Finset.univ.filter fun x : Molecule n => ¬(d x).val < sourceShrinkingLower n)
    (by intro x; simp) (fun x => sourceBandBernoulliParameter n d x)]
  rw [Finset.sum_filter, sourceDegreeBandSum, Finset.mul_sum]
  simp only [not_lt]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hlo : sourceShrinkingLower n ≤ (d x).val
  · have ha : sourceLowBandLower n ≤ (d x).val := hAL.trans hlo
    by_cases hu : (d x).val < sourceShrinkingUpper n
    · simp only [sourceBandBernoulliParameter, hlo, ha, hu, and_self, ite_true]
      ring
    · simp [sourceBandBernoulliParameter, hlo, hu]
  · simp [hlo]

theorem sourceDegreeBandSum_config (n : Nat) (B : SourceMoleculeFibreConfig n) (L U : Nat) :
    sourceDegreeBandSum n (sourceConfigDegrees n B) L U =
      ∑ x : Molecule n, truncatedBandValue L U (B x) := by
  rfl

theorem sourceHighUnionParameter_ge_band_intensity (n : Nat) (hn : 4 ≤ n) (d : SourceDegreeConfig n)
    (hAL : sourceLowBandLower n ≤ sourceShrinkingLower n) :
    1-Real.exp (-((19/20 : ℝ)/(sourceReactionCount n : ℝ)*
      sourceDegreeBandSum n d (sourceShrinkingLower n) (sourceShrinkingUpper n))) ≤
      sourceHighUnionParameter n d := by
  simpa only [sourceHighOwnerParameter_sum n d hAL] using sourceHighUnionParameter_ge_intensity n hn d

theorem sourceLowUnionParameter_ge_band_intensity (n : Nat) (hn : 4 ≤ n) (d : SourceDegreeConfig n)
    (hLU : sourceShrinkingLower n ≤ sourceShrinkingUpper n) :
    1-Real.exp (-((19/20 : ℝ)/(sourceReactionCount n : ℝ)*
      sourceDegreeBandSum n d (sourceLowBandLower n) (sourceShrinkingLower n))) ≤
      sourceLowUnionParameter n d := by
  simpa only [sourceLowOwnerParameter_sum n d hLU] using sourceLowUnionParameter_ge_intensity n hn d

end
end PowerLawSmallRAF

import proofs.PowerLawSmallRAF.SourceTwoBandCoupling
import proofs.PowerLawSmallRAF.BernoulliRetainedLowRows
import proofs.PowerLawSmallRAF.BernoulliUnionCoverage

namespace PowerLawSmallRAF
open RAF RAF.Polymer RAF.Concrete
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 100000

abbrev SourceLowOwnerGroup (n : Nat) (d : SourceDegreeConfig n) :=
  {x : Molecule n // (d x).val < sourceShrinkingLower n}

abbrev SourceHighOwnerGroup (n : Nat) (d : SourceDegreeConfig n) :=
  {x : Molecule n // ¬(d x).val < sourceShrinkingLower n}

def sourceLowUnionParameter (n : Nat) (d : SourceDegreeConfig n) : ℝ :=
  bernoulliUnionParameter (fun x : SourceLowOwnerGroup n d => sourceBandBernoulliParameter n d x.val)

def sourceHighUnionParameter (n : Nat) (d : SourceDegreeConfig n) : ℝ :=
  bernoulliUnionParameter (fun x : SourceHighOwnerGroup n d => sourceBandBernoulliParameter n d x.val)

/-- Exact source-parameter joint field law, conditional on the full degree
vector. This theorem does not assert independence after averaging degrees. -/
theorem sourceConditionalBandUnion_expectation (n : Nat) (d : SourceDegreeConfig n)
    (F : Finset (Reaction n) → Finset (Reaction n) → ℝ) :
    (∑ B : SourceMoleculeFibreConfig n, bernoulliRowsWeight (sourceBandBernoulliParameter n d) B *
      F (bernoulliRowsUnion (fun x : SourceLowOwnerGroup n d => B x.val))
        (bernoulliRowsUnion (fun x : SourceHighOwnerGroup n d => B x.val))) =
      ∑ S : Finset (Reaction n), bernoulliSubsetRowWeight (sourceLowUnionParameter n d) S *
        ∑ T : Finset (Reaction n), bernoulliSubsetRowWeight (sourceHighUnionParameter n d) T * F S T :=
  bernoulliRows_partition_union_expectation (sourceBandBernoulliParameter n d)
    (fun x => (d x).val < sourceShrinkingLower n) F

/-- Keep low catalyst identities available for selecting nucleus support,
and use the independent high channel field to generate those selected labels. -/
theorem sourceRetainedLowRows_high_union_expectation (n : Nat) (d : SourceDegreeConfig n)
    (F : (SourceLowOwnerGroup n d → Finset (Reaction n)) → Finset (Reaction n) → ℝ) :
    (∑ B : SourceMoleculeFibreConfig n, bernoulliRowsWeight (sourceBandBernoulliParameter n d) B *
      F (fun x => B x.val) (bernoulliRowsUnion (fun x : SourceHighOwnerGroup n d => B x.val))) =
      ∑ A : SourceLowOwnerGroup n d → Finset (Reaction n),
        bernoulliRowsWeight (fun x => sourceBandBernoulliParameter n d x.val) A *
          ∑ T : Finset (Reaction n), bernoulliSubsetRowWeight (sourceHighUnionParameter n d) T * F A T :=
  bernoulliRows_retained_low_high_union_expectation (sourceBandBernoulliParameter n d)
    (fun x => (d x).val < sourceShrinkingLower n) F

theorem sourceBandUnionParameter_bounds (n : Nat) (hn : 4 ≤ n) (d : SourceDegreeConfig n) :
    (0 ≤ sourceLowUnionParameter n d ∧ sourceLowUnionParameter n d ≤ 1) ∧
    (0 ≤ sourceHighUnionParameter n d ∧ sourceHighUnionParameter n d ≤ 1) := by
  constructor
  · exact bernoulliUnionParameter_bounds _
      (fun x => (sourceBandBernoulliParameter_bounds n hn d x.val).1)
      (fun x => (sourceBandBernoulliParameter_bounds n hn d x.val).2.1)
  · exact bernoulliUnionParameter_bounds _
      (fun x => (sourceBandBernoulliParameter_bounds n hn d x.val).1)
      (fun x => (sourceBandBernoulliParameter_bounds n hn d x.val).2.1)

theorem sourceHighUnionParameter_ge_intensity (n : Nat) (hn : 4 ≤ n) (d : SourceDegreeConfig n) :
    1-Real.exp (-(∑ x : SourceHighOwnerGroup n d, sourceBandBernoulliParameter n d x.val)) ≤
      sourceHighUnionParameter n d :=
  bernoulliUnionParameter_ge_exp _ (fun x => (sourceBandBernoulliParameter_bounds n hn d x.val).2.1)

theorem sourceLowUnionParameter_ge_intensity (n : Nat) (hn : 4 ≤ n) (d : SourceDegreeConfig n) :
    1-Real.exp (-(∑ x : SourceLowOwnerGroup n d, sourceBandBernoulliParameter n d x.val)) ≤
      sourceLowUnionParameter n d :=
  bernoulliUnionParameter_ge_exp _ (fun x => (sourceBandBernoulliParameter_bounds n hn d x.val).2.1)

end
end PowerLawSmallRAF

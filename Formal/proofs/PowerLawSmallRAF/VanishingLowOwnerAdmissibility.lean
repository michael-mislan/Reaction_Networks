import proofs.PowerLawSmallRAF.VanishingLowOwnerLength
import proofs.PowerLawSmallRAF.VanishingBandParameter
import proofs.PowerLawSmallRAF.SourceLowOwnerAdmissibility

namespace PowerLawSmallRAF
open Classical RAF.Polymer RAF.Concrete Filter Topology
open scoped BigOperators
noncomputable section

theorem sourceVanishingLowNonemptyRow_active (n : Nat) (d : SourceDegreeConfig n)
    (A : RetainedSourceLowRows n d)
    (hw : bernoulliRowsWeight (sourceVanishingLowOwnerParameter n d) A ≠ 0)
    (x : SourceLowOwnerGroup n d) (hx : (A x).Nonempty) :
    sourceVanishingLowLower n ≤ (d x.val).val := by
  have hp := nonempty_row_parameter_ne_zero _ A hw x hx
  by_contra h
  exact hp (by simp [sourceVanishingLowOwnerParameter,h])

/-- The short-owner exclusion controls every selected owner with a used
mark, including catalysts of the fixed finite seed base. -/
theorem sourceVanishingLowUsedOwner_length (n m : Nat) (d : SourceDegreeConfig n)
    (A : RetainedSourceLowRows n d)
    (hw : bernoulliRowsWeight (sourceVanishingLowOwnerParameter n d) A ≠ 0)
    (hs : ¬ ∃ x : Molecule n, x.1.val < m ∧ sourceVanishingLowLower n ≤ (d x).val)
    (x : SourceLowOwnerGroup n d) (hx : (A x).Nonempty) :
    m ≤ (sourceOwnerWord x.val).length := by
  have hd := sourceVanishingLowNonemptyRow_active n d A hw x hx
  have hnot : ¬ x.val.1.val < m := fun hh => hs ⟨x.val,hh,hd⟩
  rw [sourceOwnerWord_length]
  unfold molLength
  omega

def sourceVanishingLowShortDegreeMass (n : Nat) : ℝ :=
  ∑ d : SourceDegreeConfig n, sourceDegreeWeight (2-2/(n : ℝ)) n d *
    (if ∃ x : Molecule n, x.1.val < sourceVanishingLowOwnerLength n ∧
      sourceVanishingLowLower n ≤ (d x).val then 1 else 0)

theorem sourceVanishingLowShortDegreeMass_eq (n : Nat) : sourceVanishingLowShortDegreeMass n =
    sourceShortOwnerFailureMass (2-2/(n : ℝ)) n (sourceVanishingLowOwnerLength n) (sourceVanishingLowLower n) := by
  unfold sourceVanishingLowShortDegreeMass
  rw [← sourceDegreeStatistics_expectation (2-2/(n : ℝ)) n
    (fun d => if ∃ x : Molecule n, x.1.val < sourceVanishingLowOwnerLength n ∧
      sourceVanishingLowLower n ≤ (d x).val then 1 else 0)]
  unfold sourceShortOwnerFailureMass
  apply Finset.sum_congr rfl
  intro B _
  simp only [sourceConfigDegrees,mul_ite,mul_one,mul_zero]

theorem sourceVanishingLowShortDegreeMass_tendsto_zero :
    Tendsto sourceVanishingLowShortDegreeMass atTop (𝓝 0) := by
  change Tendsto (fun n => sourceVanishingLowShortDegreeMass n) atTop (𝓝 0)
  simp_rw [sourceVanishingLowShortDegreeMass_eq]
  exact sourceVanishingLowShortOwnerFailureMass_tendsto_zero

end
end PowerLawSmallRAF

import proofs.PowerLawSmallRAF.SourceLowNucleusSelector
import proofs.PowerLawSmallRAF.SelectedTargetAverage

namespace PowerLawSmallRAF
open RAF.Polymer RAF.Concrete
noncomputable section
attribute [local instance] Classical.propDecidable

theorem nonempty_row_parameter_ne_zero {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (p : I → ℝ) (A : I → Finset J)
    (hw : bernoulliRowsWeight p A ≠ 0) (x : I) (hx : (A x).Nonempty) : p x ≠ 0 := by
  intro hp
  apply hw
  apply Finset.prod_eq_zero (Finset.mem_univ x)
  have hc : (A x).card ≠ 0 := ne_of_gt (Finset.card_pos.mpr hx)
  simp [bernoulliSubsetRowWeight,hp,hc]

theorem sourceLowNonemptyRow_active (n : Nat) (hn : 4 ≤ n) (d : SourceDegreeConfig n)
    (A : RetainedSourceLowRows n d)
    (hw : bernoulliRowsWeight (fun x => sourceBandBernoulliParameter n d x.val) A ≠ 0)
    (x : SourceLowOwnerGroup n d) (hx : (A x).Nonempty) :
    sourceLowBandLower n ≤ (d x.val).val := by
  have hp := nonempty_row_parameter_ne_zero _ A hw x hx
  by_contra h
  exact hp ((sourceBandBernoulliParameter_bounds n hn d x.val).2.2.2 (lt_of_not_ge h))

/-- Admissibility holds on every nonzero-weight low-row configuration once
the degree vector contains no short active owner. Zero-weight rows are not
mistakenly treated as impossible configurations at the type level. -/
theorem sourceLowNucleusOwnerWords_admissible (n L m : Nat) (hn : 4 ≤ n)
    (d : SourceDegreeConfig n) (A : RetainedSourceLowRows n d)
    (hw : bernoulliRowsWeight (fun x => sourceBandBernoulliParameter n d x.val) A ≠ 0)
    (hs : ¬ ∃ x : Molecule n, x.1.val < m ∧ sourceLowBandLower n ≤ (d x).val) :
    targetSetAdmissible n m ((2 : ℝ)^(L+1)) (sourceLowNucleusOwnerWords n L d A) := by
  refine ⟨?_,?_⟩
  · exact_mod_cast sourceLowNucleusOwnerWords_card_le n L d A
  · intro w hwW
    refine ⟨?_,sourceLowNucleusOwnerWords_length_le n L d A w hwW⟩
    obtain ⟨x,hx,hrow⟩ := sourceLowNucleusOwnerWords_has_mark n L d A w hwW
    have hd := sourceLowNonemptyRow_active n hn d A hw x hrow
    have hnot : ¬ x.val.1.val < m := fun hh => hs ⟨x.val,hh,hd⟩
    rw [← hx,sourceOwnerWord_length]
    unfold molLength
    omega

end
end PowerLawSmallRAF

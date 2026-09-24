import proofs.PowerLawSmallRAF.SourceOwnerMarkov

namespace PowerLawSmallRAF
open RAF RAF.Polymer RAF.Concrete Filter Topology
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 100000

def sourceShortOwnerFailureMass (a : ℝ) (n m L : Nat) : ℝ :=
  ∑ config : SourceMoleculeFibreConfig n,
    if ∃ x : Molecule n, x.1.val < m ∧ L ≤ (config x).card
    then sourcePowerLawConfigWeight a n config else 0

/-- The length test is `x.1.val < m` because a molecule's length is its
sigma index plus one. This bounds all short labels simultaneously. -/
theorem source_short_owner_failure_le (a : ℝ) (n m L : Nat)
    (ha : 1 < a) (hn : 4 ≤ n) (hmn : m ≤ n) (hL : 0 < L) :
    sourceShortOwnerFailureMass a n m L ≤
      (2 : ℝ)^(m+1)*windowZipfMean a (sourceReactionCount n)/(L : ℝ) := by
  let H : Finset (Molecule n) := Finset.univ.image (liftBinaryMolecule hmn)
  have hcard : H.card ≤ sourceMoleculeCount m := by
    exact Finset.card_image_le.trans (by rw [Finset.card_univ, card_binaryMolecule_eq_sourceMoleculeCount])
  have hmem (x : Molecule n) (hx : x.1.val < m) : x ∈ H := by
    refine Finset.mem_image.mpr ⟨⟨⟨x.1.val, hx⟩, x.2⟩, Finset.mem_univ _, ?_⟩
    rfl
  have hcount (config : SourceMoleculeFibreConfig n)
      (he : ∃ x : Molecule n, x.1.val < m ∧ L ≤ (config x).card) :
      (1 : ℝ) ≤ sourceOwnerThresholdCount n H L config := by
    obtain ⟨x, hx, hd⟩ := he
    have hb := Finset.single_le_sum
      (f := fun y : Molecule n => if L ≤ (config y).card then (1 : ℝ) else 0)
      (fun y _ => by dsimp only; split_ifs <;> norm_num) (hmem x hx)
    simpa only [if_pos hd] using hb
  have hinc : sourceShortOwnerFailureMass a n m L ≤
      ∑ config : SourceMoleculeFibreConfig n,
        if (1 : ℝ) ≤ sourceOwnerThresholdCount n H L config
        then sourcePowerLawConfigWeight a n config else 0 := by
    apply Finset.sum_le_sum
    intro config _
    have hw := sourcePowerLawConfigWeight_nonneg a n ha config
    by_cases he : ∃ x : Molecule n, x.1.val < m ∧ L ≤ (config x).card
    · simp only [if_pos he, if_pos (hcount config he), le_refl]
    · simp only [if_neg he]
      split_ifs <;> linarith only [hw]
  have hmark := source_owner_count_markov a n ha hn H L hL 1 (by norm_num)
  simp only [mul_one] at hmark
  have hmean : 0 ≤ windowZipfMean a (sourceReactionCount n) := by
    rw [← source_oneFibre_degree_mean a n hn]
    apply Finset.sum_nonneg
    intro A _
    apply mul_nonneg _ (Nat.cast_nonneg _)
    apply subsetDegreeWeight_nonneg
    intro d
    apply cappedZipfDegreeMass_nonneg a _ d
    rw [zipfNormalizer_eq_prefix_add_tail ha 2, zipfPrefix_two ha]
    nlinarith [rpowTail_nonneg a 2]
  apply (hinc.trans hmark).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_right _ hmean
  have hpow : sourceMoleculeCount m ≤ 2^(m+1) := by
    unfold sourceMoleculeCount
    exact Nat.sub_le _ _
  exact_mod_cast hcard.trans hpow

end
end PowerLawSmallRAF

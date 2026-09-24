import proofs.SmallResidentCompositionCopying.AmplificationIteration

namespace SmallResidentCompositionCopying
open Amplification

/-- Four nonempty, composition-separated labels copied by the same explicit
controlled reversible interacting mechanism. All counts in each admitted pure
module range from1 to19; both complementary daughters are tested at time20.
The law includes the one-billion-event resource quota and zero-counter restart.
The external module-total quench and food/solvent resets are part of the protocol. -/
theorem four_label_copying :
    sourceProperties ∧
    (∀ word : Word, newborn preparation ∧ totalResidents preparation=20 ∧
      (99:ℝ)/100 ≤ actualJointReturn word preparation) ∧
    (∀ (word : Word) (z : Counts), newborn z →
      totalResidents z ≤ 38 ∧ decoder (composition word z)=word ∧
      (99:ℝ)/100 ≤ actualJointReturn word z) ∧
    (∀ (word word' : Word) (z z' : Counts), newborn z → word ≠ word' →
      (1:ℝ)/20 ≤ distance word word' z z') ∧
    (∀ (a b : ℕ) (h : goodAllocation a b),
      newborn (daughterCounts a b h) ∧ newborn (complementCounts a b h)) ∧
    (∀ z : Counts, totalResidents z ≤ 40) := by
  refine ⟨source_properties,encoded_cycle,?_,separated_words,daughters_restart,parent_budget⟩
  intro word z hz
  exact ⟨newborn_budget z hz,decoder_correct word z hz,actual_joint_return word z⟩

end SmallResidentCompositionCopying

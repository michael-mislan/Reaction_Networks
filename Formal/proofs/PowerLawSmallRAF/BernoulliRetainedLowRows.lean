import proofs.PowerLawSmallRAF.BernoulliPartitionUnion

namespace PowerLawSmallRAF
open scoped BigOperators
noncomputable section
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
set_option maxHeartbeats 100000

/-- Retain all low-group rows, including catalyst ownership, while replacing
the independent high-group union by its exact iid channel law. -/
theorem bernoulliRows_retained_low_high_union_expectation (p : I → ℝ)
    (cut : I → Prop) [DecidablePred cut]
    (F : ({i // cut i} → Finset J) → Finset J → ℝ) :
    (∑ B : I → Finset J, bernoulliRowsWeight p B *
      F (fun i => B i.val) (bernoulliRowsUnion (fun i : {i // ¬cut i} => B i.val))) =
      ∑ A : {i // cut i} → Finset J, bernoulliRowsWeight (fun i => p i.val) A *
        ∑ T : Finset J, bernoulliSubsetRowWeight (bernoulliUnionParameter (fun i : {i // ¬cut i} => p i.val)) T * F A T := by
  calc
    _ = ∑ A : {i // cut i} → Finset J, bernoulliRowsWeight (fun i => p i.val) A *
        ∑ B : {i // ¬cut i} → Finset J, bernoulliRowsWeight (fun i => p i.val) B * F A (bernoulliRowsUnion B) := by
      rw [bernoulliRows_partition_expectation p cut (fun A B => F A (bernoulliRowsUnion B))]
      simp only [Finset.mul_sum, mul_assoc]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro A _
      rw [bernoulliRows_union_expectation]

end
end PowerLawSmallRAF

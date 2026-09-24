import proofs.PowerLawSmallRAF.BernoulliUnionLaw

namespace PowerLawSmallRAF
open scoped BigOperators
noncomputable section
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
set_option maxHeartbeats 100000

omit [DecidableEq J] in
/-- Reindex the complete row experiment by two complementary owner groups.
The observable may couple the groups arbitrarily. -/
theorem bernoulliRows_partition_expectation (p : I → ℝ) (cut : I → Prop) [DecidablePred cut]
    (F : ({i // cut i} → Finset J) → ({i // ¬cut i} → Finset J) → ℝ) :
    (∑ B : I → Finset J, bernoulliRowsWeight p B *
      F (fun i => B i.val) (fun i => B i.val)) =
      ∑ A : {i // cut i} → Finset J, ∑ B : {i // ¬cut i} → Finset J,
        bernoulliRowsWeight (fun i => p i.val) A * bernoulliRowsWeight (fun i => p i.val) B * F A B := by
  calc
    _ = ∑ pair : ({i // cut i} → Finset J) × ({i // ¬cut i} → Finset J),
        bernoulliRowsWeight (fun i => p i.val) pair.1 *
          bernoulliRowsWeight (fun i => p i.val) pair.2 * F pair.1 pair.2 := by
      apply Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd cut (fun _ : I => Finset J))
      intro B
      change (∏ i, bernoulliSubsetRowWeight (p i) (B i))*F (fun i => B i.val) (fun i => B i.val) =
        ((∏ i : {i // cut i}, bernoulliSubsetRowWeight (p i.val) (B i.val))*
          (∏ i : {i // ¬cut i}, bernoulliSubsetRowWeight (p i.val) (B i.val)))*
            F (fun i => B i.val) (fun i => B i.val)
      rw [Fintype.prod_subtype_mul_prod_subtype cut (fun i => bernoulliSubsetRowWeight (p i) (B i))]
    _ = _ := Fintype.sum_prod_type _

/-- Joint union-field law for two complementary owner groups, with all row
parameters fixed. This permits conditioning on a low-group realization before
using the independent high-group field. -/
theorem bernoulliRows_partition_union_expectation (p : I → ℝ) (cut : I → Prop) [DecidablePred cut]
    (F : Finset J → Finset J → ℝ) :
    (∑ B : I → Finset J, bernoulliRowsWeight p B *
      F (bernoulliRowsUnion (fun i : {i // cut i} => B i.val))
        (bernoulliRowsUnion (fun i : {i // ¬cut i} => B i.val))) =
      ∑ S : Finset J, bernoulliSubsetRowWeight (bernoulliUnionParameter (fun i : {i // cut i} => p i.val)) S *
        ∑ T : Finset J, bernoulliSubsetRowWeight (bernoulliUnionParameter (fun i : {i // ¬cut i} => p i.val)) T * F S T := by
  calc
    _ = ∑ A : {i // cut i} → Finset J, bernoulliRowsWeight (fun i => p i.val) A *
        ∑ B : {i // ¬cut i} → Finset J, bernoulliRowsWeight (fun i => p i.val) B *
          F (bernoulliRowsUnion A) (bernoulliRowsUnion B) := by
      rw [bernoulliRows_partition_expectation p cut
        (fun A B => F (bernoulliRowsUnion A) (bernoulliRowsUnion B))]
      simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ S : Finset J, bernoulliSubsetRowWeight (bernoulliUnionParameter (fun i : {i // cut i} => p i.val)) S *
        ∑ B : {i // ¬cut i} → Finset J, bernoulliRowsWeight (fun i => p i.val) B * F S (bernoulliRowsUnion B) :=
      bernoulliRows_union_expectation (fun i : {i // cut i} => p i.val)
        (fun S => ∑ B : {i // ¬cut i} → Finset J,
          bernoulliRowsWeight (fun i => p i.val) B * F S (bernoulliRowsUnion B))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro S _
      rw [bernoulliRows_union_expectation]

end
end PowerLawSmallRAF

import proofs.SmallResidentCompositionCopying.FiniteFoodPartition
import proofs.SmallResidentCompositionCopying.FiniteFoodInvariants
import proofs.SmallResidentCompositionCopying.FiniteFoodGeometry

namespace SmallResidentCompositionCopying.FiniteFood

theorem publication :
    (∀ word z, (8046297159:ℝ)/8112104000 ≤ actualReturn nominal 9 word z) ∧
    (∀ p, OperatingBox p → ∀ word z,
      (114080769:ℝ)/115203200 ≤ actualReturn p 9 word z) ∧
    (∀ (w v : Word) (z t : Counts 9), newborn z → newborn t → w≠v →
      (2:ℝ)/9 ≤ distance w v z t) ∧
    (∀ z : Counts 9, newborn z → total z≤16) ∧
    (∀ z : Counts 9, total z≤18) := by
  refine ⟨return9,return_box,separated,?_,?_⟩
  · intro z hz; exact (budgets z).2 hz
  · intro z; exact (budgets z).1

end SmallResidentCompositionCopying.FiniteFood

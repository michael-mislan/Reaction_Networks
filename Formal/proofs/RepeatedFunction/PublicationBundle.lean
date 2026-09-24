import proofs.RepeatedFunction.ProductiveCensus
import proofs.RepeatedFunction.StartupNecessary

namespace RandomViability

/-- Compact checked publication constants; the full stopped-generator and
asymptotic consequence arguments are written explicitly in the paper. -/
theorem publication_census_and_startup_constants :
    Fintype.card (ProductiveLabel 4) = 224 ∧
    (∀ n,Fintype.card (ProductiveLabel n) ≤ 224) ∧
    (∀ x y : ℝ,0 ≤ y → x+2*y ≤ 11 → 2*x*y+y^2 ≤ 121/3) :=
  ⟨productive_labels_four,productive_labels_card_le,food_pair_birth_bound⟩

end RandomViability

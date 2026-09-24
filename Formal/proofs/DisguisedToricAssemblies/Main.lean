import proofs.DisguisedToricAssemblies.CACExamples

namespace DisguisedToricAssemblies
open CoreCouplingCAC

/-- Literal six-parameter family endpoint; no generic assembly claim is made. -/
theorem cacFamilyResolution :
    (∀ p : Rates, p.Positive → (DisguisedToric p ↔ ParameterCriterion p)) ∧
    (∀ p : Rates, p.Positive → ParameterCriterion p →
      ∃ x : State, x.Positive ∧
        (∀ i j, 0 ≤ realizingRates p x i j) ∧
        (∀ i, realizingRates p x i i = 0) ∧
        (∀ i, ∑ j, realizingRates p x i j*(∏ k, coordinates x k^exponents i k) =
          ∑ j, realizingRates p x j i*(∏ k, coordinates x k^exponents j k)) ∧
        (∀ y : State, auxiliaryDerivative (realizingRates p x) y = sourceDerivative p y)) ∧
    (∀ p : Rates, p.Positive → 1 ≤ p.d → p.e ≤ 1 → DisguisedToric p) ∧
    (negativeRates.Positive ∧ negativeState.Positive ∧ Stationary negativeRates negativeState) ∧
    (∀ x : State, x.Positive → Stationary negativeRates x → x = negativeState) ∧
    ¬ DisguisedToric negativeRates :=
  ⟨cacParameterLocus,criterion_literal_witness,safe_region,negative_stationary,
    negative_unique_stationary,negative_not_disguised⟩

end DisguisedToricAssemblies

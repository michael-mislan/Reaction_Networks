import proofs.InheritedCellAssay.CountAssaySource
import proofs.InheritedCellAssay.ConcreteScalarSource

namespace InheritedCellAssay

/-- Exact finite prediction decision for the declared inherited-type count
    source versus its rate-defined scalar backward-equation count model.
    The scalar class is inhabited; no desired coverage is a source assumption.
    This is a known-parameter synthetic theorem, not an empirical claim. -/
theorem count_prediction_comparison :
    Nonempty ScalarRateSource.BackwardCountSource ∧
    (∀ S : ScalarRateSource.BackwardCountSource,
      (19/20 : ℝ) < S.weight 0+S.weight 1+S.weight 2) ∧
    CountAssay.coverage 2 = 91/96 ∧
    CountAssay.coverage 2 < 19/20 ∧
    CountAssay.coverage 3 = 187/192 ∧
    19/20 < CountAssay.coverage 3 := by
  exact ⟨⟨ScalarRateSource.concreteScalarSource⟩,
    ScalarRateSource.scalar_source_coverage, CountAssay.actual_source_failure_and_repair⟩

end InheritedCellAssay

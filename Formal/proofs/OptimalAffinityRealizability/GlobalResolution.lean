import proofs.OptimalAffinityRealizability.GlobalBoundary
import proofs.OptimalAffinityRealizability.ArbitraryRateGlobal
import proofs.OptimalAffinityRealizability.GlobalAccessibility
import proofs.OptimalAffinityRealizability.SourceGlobalCapacity

namespace OptimalAffinityRealizability

/-- The source-level global-capacity conclusion, with explicit nonempty physical
scope and a unique-global conclusion on the strongly connected subclass. -/
theorem sharpGlobalResponseCapacityResolution {n : ℕ} [Nonempty (Fin n)]
    (source : SquareSource n) (weights : Fin n → ℕ) (J : ℝ) (g : Fin n → ℝ)
    (hclass : AccessibleRootedResponseClass source)
    (hT : ∀ i j, 0 ≤ responseMatrix source i j)
    (hJ : 0 < J) (hg : ∀ i, 0 < g i) (hmode : ControlledProductionMode source g)
    (hne : ∃ f, ResponseFeasible (responseMatrix source) f) :
    ((∃ f, GlobalRealizable source J g f) ∧
      realizationCapacity (responseMatrix source) weights (GlobalRealizable source J g) =
        responseLayerCapacity (responseMatrix source) weights) ∧
    (ResponseStronglyConnected (responseMatrix source) →
      (∃ f, UniqueGlobalRealizable source J g f) ∧
      realizationCapacity (responseMatrix source) weights (UniqueGlobalRealizable source J g) =
        responseLayerCapacity (responseMatrix source) weights) := by
  exact ⟨rawSquareSource_globalCapacityEquality source weights J g hclass hT hJ hg hmode hne,
    fun hc => rawSquareSource_uniqueGlobalCapacityEquality source weights J g
      hclass hT hc hJ hg hmode hne⟩

end OptimalAffinityRealizability

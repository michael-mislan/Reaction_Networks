import proofs.TypeIIStability.SourceDynamics
import proofs.TypeIIStability.Eigenpair

namespace TypeIIStability
open Witness

/-- A literal minimal Type II3 core with one internal return-path species,
 strictly positive reversible rates and degradation, and a positive stationary
 state whose full physical Jacobian has the exact eigenvalue 1+8i. -/
theorem typeII3_instability_counterexample :
    MixedDegradation.TypeII.PaperRaw.IsPaperTypeIILCore paperNetwork ∧
    paperNetwork.PositiveState paperState ∧
    paperNetwork.Stationary paperState ∧
    (∀ i, 0 < forwardRate i) ∧
    (∀ i, 0 < reverseRate i) ∧
    (∀ i, 0 < degradation i) ∧
    (∀ i, 0 < x i) ∧
    sourceDrift x = 0 ∧
    HasFDerivAt sourceDrift (MixedDegradation.matrixCLM A) x ∧
    DUnstableCores.HasEigenpair A (1 + 8 * Complex.I) eigenvector ∧
    DUnstableCores.HurwitzUnstable A := by
  exact ⟨paper_core, paper_positive, paper_stationary,
    rates_positive.1, rates_positive.2.1, rates_positive.2.2,
    parameters_positive.2.2.2, (source_drift_eq x).trans stationary,
    source_physical_derivative, exact_eigenpair, unstable⟩

/-- Instability is compatible with the already proved uniqueness theorem:
 the displayed source has exactly one positive stationary state. -/
theorem unique_positive_stationary_state (y : paperNetwork.State)
    (hy : paperNetwork.PositiveState y) (hs : paperNetwork.Stationary y) :
    y = paperState := by
  exact MixedDegradation.TypeII.PaperRaw.paper_typeII_l_unistationarity
    paperNetwork paper_core (by omega) y paperState hy paper_positive hs paper_stationary

end TypeIIStability

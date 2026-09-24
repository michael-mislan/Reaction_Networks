import proofs.PersisterMemory.SupersolutionSegment
import proofs.PersisterMemory.ImprovedPulseCertificate
import proofs.PersisterMemory.RemainingBudgetAlgebra
import proofs.PersisterMemory.DoseExposureBounds
import proofs.PersisterMemory.ShortTimeComparison

namespace PersisterMemory
theorem publication_algebra (e a : ℚ) (q : Fin 6 → ℚ) (i : Fin 6) :
    Source.pgfResidual e (fun j => 1-a*(1-q j)) i =
      a*Source.pgfResidual e q i-
      a*(1-a)*Source.daughterPair (fun j => 1-q j) i/10 ∧
    Source.meanAction (3/10) improvedWeight i ≤ -(21/200)*improvedWeight i :=
  ⟨segment_identity e a q i, (improved_pulse_certificate i).1⟩
end PersisterMemory

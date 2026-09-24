import proofs.OptimalAffinityRealizability.PowerGlobalFamily

namespace OptimalAffinityRealizability

noncomputable section

/-- The minimal higher-order datum absent from a response jet: a branch-wide
current bound and uniqueness certificate on the literal source's full positive
stationary fiber. -/
structure GlobalGapCertificate {n : ℕ} (source : SquareSource n) (J : ℝ)
    (production q : Fin n → ℝ) where
  globalBound : ∀ z, GlobalStationaryFiber source J production q z →
    controlledFluxAtLogState source J production q z ≤ J
  uniqueEquality : ∀ z, GlobalStationaryFiber source J production q z →
    controlledFluxAtLogState source J production q z = J → z = 0

/-- Corrected global profile: the response/local jet plus the source-bound
global invariant.  No claim is made that first-order response data determine
this certificate outside proved source classes. -/
structure CorrectedGlobalKineticProfile {n : ℕ} (source : SquareSource n)
    (J : ℝ) (production f : Fin n → ℝ) where
  localWitness : StrictLocalRealizationWitness source J production f
  globalGap : GlobalGapCertificate source J production localWitness.q

def UniqueGlobalRealizationWitness.toCorrectedProfile {n : ℕ}
    {source : SquareSource n} {J : ℝ} {production f : Fin n → ℝ}
    (w : UniqueGlobalRealizationWitness source J production f) :
    CorrectedGlobalKineticProfile source J production f where
  localWitness := w.localWitness
  globalGap := {
    globalBound := w.globalBound
    uniqueEquality := w.uniqueEquality
  }

def CorrectedGlobalKineticProfile.toUniqueGlobalWitness {n : ℕ}
    {source : SquareSource n} {J : ℝ} {production f : Fin n → ℝ}
    (p : CorrectedGlobalKineticProfile source J production f) :
    UniqueGlobalRealizationWitness source J production f where
  localWitness := p.localWitness
  globalBound := p.globalGap.globalBound
  uniqueEquality := p.globalGap.uniqueEquality

/-- The corrected invariant is neither weaker nor stronger by definition: it
is an interface decomposition of exact unique global realizability. -/
theorem uniqueGlobalRealizable_iff_correctedGlobalProfile {n : ℕ}
    (source : SquareSource n) (J : ℝ) (production f : Fin n → ℝ) :
    UniqueGlobalRealizable source J production f ↔
      Nonempty (CorrectedGlobalKineticProfile source J production f) := by
  constructor
  · rintro ⟨w⟩
    exact ⟨w.toCorrectedProfile⟩
  · rintro ⟨p⟩
    exact ⟨p.toUniqueGlobalWitness⟩

end
end OptimalAffinityRealizability

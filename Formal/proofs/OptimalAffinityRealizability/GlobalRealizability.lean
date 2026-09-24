import proofs.OptimalAffinityRealizability.MatrixScalingKKT

namespace OptimalAffinityRealizability

noncomputable section

/-- Positive concentrations are represented by arbitrary log states.  The
global stationary fiber imposes every balance law except the controlled row. -/
def GlobalStationaryFiber {n : ℕ} (source : SquareSource n) (J : ℝ)
    (production q : Fin n → ℝ) (z : Fin n → ℝ) : Prop :=
  ∀ i, i ≠ source.controlled →
    reconstructedLogSourceDrift source J production q z i = 0

def controlledFluxAtLogState {n : ℕ} (source : SquareSource n) (J : ℝ)
    (production q : Fin n → ℝ) (z : Fin n → ℝ) : ℝ :=
  reconstructedLogSourceDrift source J production q z source.controlled

/-- Exact global obligations: a strict-local response witness whose controlled
current is globally maximal on the full positive stationary fiber, with a
unique equality state. -/
structure UniqueGlobalRealizationWitness {n : ℕ} (source : SquareSource n)
    (J : ℝ) (production f : Fin n → ℝ) where
  localWitness : StrictLocalRealizationWitness source J production f
  globalBound : ∀ z, GlobalStationaryFiber source J production localWitness.q z →
    controlledFluxAtLogState source J production localWitness.q z ≤ J
  uniqueEquality : ∀ z, GlobalStationaryFiber source J production localWitness.q z →
    controlledFluxAtLogState source J production localWitness.q z = J → z = 0

def UniqueGlobalRealizable {n : ℕ} (source : SquareSource n) (J : ℝ)
    (production f : Fin n → ℝ) : Prop :=
  Nonempty (UniqueGlobalRealizationWitness source J production f)

theorem uniqueGlobalRealizable_strictLocal {n : ℕ}
    (source : SquareSource n) (J : ℝ) (production f : Fin n → ℝ)
    (hglobal : UniqueGlobalRealizable source J production f) :
    StrictLocalRealizable source J production f := by
  obtain ⟨hglobal⟩ := hglobal
  exact ⟨hglobal.localWitness⟩

theorem uniqueGlobalRealizable_responseFeasible {n : ℕ}
    (source : SquareSource n) (J : ℝ) (production f : Fin n → ℝ)
    (hglobal : UniqueGlobalRealizable source J production f) :
    ResponseFeasible (responseMatrix source) f :=
  firstOrderRealizable_responseFeasible source J production f
    (regularBranchRealizable_firstOrder source J production f
      (strictLocalRealizable_regularBranch source J production f
        (uniqueGlobalRealizable_strictLocal source J production f hglobal)))

theorem uniqueGlobalRealizable_globalBound {n : ℕ}
    (source : SquareSource n) (J : ℝ) (production f : Fin n → ℝ)
    (hglobal : UniqueGlobalRealizable source J production f)
    (z : Fin n → ℝ) :
    GlobalStationaryFiber source J production hglobal.some.localWitness.q z →
      controlledFluxAtLogState source J production hglobal.some.localWitness.q z ≤ J := by
  exact hglobal.some.globalBound z

theorem uniqueGlobalRealizable_uniqueEquality {n : ℕ}
    (source : SquareSource n) (J : ℝ) (production f : Fin n → ℝ)
    (hglobal : UniqueGlobalRealizable source J production f)
    (z : Fin n → ℝ)
    (hz : GlobalStationaryFiber source J production hglobal.some.localWitness.q z)
    (heq : controlledFluxAtLogState source J production hglobal.some.localWitness.q z = J) :
    z = 0 := by
  exact hglobal.some.uniqueEquality z hz heq

end
end OptimalAffinityRealizability

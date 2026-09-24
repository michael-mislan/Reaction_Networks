import proofs.RAF1519.Refinement.CountPulse

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators
set_option maxHeartbeats 20000

theorem graphPulseCategory_nonnegative {n : ℕ} (N : MolecularState n) (p : Fin n → Intervention) :
    ∀ (m : PulseMolecules N) (a : Fin 3), 0 ≤ graphPulseCategory N p m a := by
  intro m a
  exact pulseCategory_nonnegative (p m.1.1) m.1.2 a

theorem graphPulseCategory_total {n : ℕ} (N : MolecularState n) (p : Fin n → Intervention) :
    ∀ m : PulseMolecules N, ∑ a, graphPulseCategory N p m a=1 := by
  intro m
  exact pulseCategory_total (p m.1.1) m.1.2

/-- Conditional on the actual state and chosen actions, every molecule gets one of three fates. -/
def graphPulsePMF {n : ℕ} (N : MolecularState n) (p : Fin n → Intervention) : PMF (PulseOutcomes N) :=
  categoricalPMF (ι := PulseMolecules N) (graphPulseCategory N p)
    (graphPulseCategory_nonnegative N p) (graphPulseCategory_total N p)

end
end RAF1519.Refinement

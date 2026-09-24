import proofs.SerialTransferSelection.TransferRecovery
import proofs.SerialTransferSelection.CycleTransferInputs

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

noncomputable def sizeLogOdds (s : PopulationState) : ℝ :=
  Real.log (ancestralMembrane true s.live)-Real.log (ancestralMembrane false s.live)

noncomputable def cycleSizeGain (ε : ℝ) : ℝ :=
  (3/5)*Real.log 4-19/500-Real.log ((1+ε)/(1-ε))

def cycleReadyRelation (N M : ℕ) (zL zH : ℝ) (s : PopulationState) (p ε : ℝ)
    (y : ReadyPopulation N M zL zH) : Prop :=
  (∀ b, 0 < ancestralCount b y.val.live ∧
    (1-ε)*p/16 ≤ (ancestralCount b y.val.live : ℝ)/(M : ℝ)) ∧
  cycleSizeGain ε < sizeLogOdds y.val-sizeLogOdds s

theorem source_cycle_outcome (N M : ℕ) (zL zH : ℝ) (s : PopulationState)
    (p ε : ℝ) {D : Finset PopulationState} (x : StoppedPopulation D)
    (hx : x ∈ phaseBatchGoodSet N (membrane s.live)
      (ancestralMembrane true s.live) (ancestralMembrane false s.live) zL zH D)
    (y : ReadyPopulation N M zL zH)
    (hy : transferReadyRelation N M zL zH (physicalState N x) p ε y) :
    cycleReadyRelation N M zL zH s p ε y := by
  obtain ⟨e,rfl,_,_,_,_,_,_,hg⟩ := hx
  refine ⟨hy.1,?_⟩
  have ht := hy.2
  dsimp only [physicalState] at ht
  unfold cycleSizeGain sizeLogOdds
  linarith only [hg,ht]

end SerialTransferSelection

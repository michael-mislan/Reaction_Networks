import proofs.ProductiveMemory.ExtractionTransferRecovery
import proofs.ProductiveMemory.ExtractionTransferInputs
import proofs.ProductiveMemory.ExtractionBatchSchedule
import proofs.SerialTransferSelection.CycleOutcome

namespace ProductiveMemory
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Set
open scoped NNReal
noncomputable section
set_option Elab.async false

abbrev ProductiveCycleResult (N M J : ℕ) (rho zL zH : ℝ) := ProductiveReady N M rho zL zH × Fin J

def productiveRecordOutput {α : Type*} [Fintype α] (J : ℕ) (e : Fin J) (mu : FiniteLaw (Option α)) :
    FiniteLaw (Option (α × Fin J)) :=
  mu.bind (fun x => FiniteLaw.pure (x.map (fun y => (y,e))))

theorem productive_record_probability {α : Type*} [Fintype α] (J : ℕ) (e : Fin J)
    (mu : FiniteLaw (Option α)) (R : α × Fin J → Prop) :
    (productiveRecordOutput J e mu).expect (FiniteKernel.eventIndicator (SerialTransferSelection.successfulOutput R)) =
      mu.expect (FiniteKernel.eventIndicator (SerialTransferSelection.successfulOutput (fun y => R (y,e)))) := by
  classical
  unfold productiveRecordOutput
  rw [FiniteLaw.expect_bind]
  apply congrArg mu.expect
  funext x
  cases x <;> simp [FiniteLaw.expect_pure,SerialTransferSelection.successfulOutput,FiniteKernel.eventIndicator]

def productiveCycleRelation (N M J : ℕ) (rho zL zH : ℝ) (s : ProductiveState) (p eps : ℝ)
    (y : ProductiveCycleResult N M J rho zL zH) : Prop :=
  (∀ b, 0 < ancestralCount b y.1.val.population.live ∧
    (1-eps)*p/16 ≤ (ancestralCount b y.1.val.population.live:ℝ)/(M:ℝ)) ∧
  SerialTransferSelection.cycleSizeGain eps <
    SerialTransferSelection.sizeLogOdds y.1.val.population-SerialTransferSelection.sizeLogOdds s.population ∧
  5*membrane s.population.live < y.2.val

theorem productive_cycle_outcome (N M J : ℕ) (rho zL zH : ℝ) (s : ProductiveState) (p eps : ℝ)
    {D : Finset ProductiveState} (x : ProductiveStopped D)
    (hx : x ∈ productiveBatchGoodSet N (membrane s.population.live) J
      (ancestralMembrane true s.population.live) (ancestralMembrane false s.population.live) rho zL zH D)
    (y : ProductiveReady N M rho zL zH)
    (hy : extractionTransferRelation N M rho zL zH (productivePhysical N x).population p eps y)
    (e : Fin J) (he : e.val=(productivePhysical N x).collected) :
    productiveCycleRelation N M J rho zL zH s p eps (y,e) := by
  obtain ⟨a,rfl,_,_,_,_,_,_,hg,hout,_⟩ := hx
  refine ⟨hy.1,?_,?_⟩
  · have ht := hy.2
    dsimp only [productivePhysical] at ht
    unfold SerialTransferSelection.cycleSizeGain SerialTransferSelection.sizeLogOdds
    linarith only [hg,ht]
  · rw [he]
    exact hout

theorem productive_good_collected (N W0 J H0 L0 : ℕ) (rho zL zH : ℝ) {D : Finset ProductiveState}
    (x : ProductiveStopped D) (hx : x ∈ productiveBatchGoodSet N W0 J H0 L0 rho zL zH D) :
    (productivePhysical N x).collected < J := by
  obtain ⟨e,rfl,_,_,_,_,_,_,_,_,h⟩ := hx
  exact h

end
end ProductiveMemory

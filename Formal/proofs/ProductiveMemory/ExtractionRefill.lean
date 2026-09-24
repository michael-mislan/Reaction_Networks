import proofs.ProductiveMemory.ExtractionReadyPopulation
import proofs.ProductiveMemory.ExtractionPopulationRecovery
import proofs.SerialTransferSelection.RecoveryRefill

namespace ProductiveMemory
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Set
noncomputable section
set_option Elab.async false

def extractionRecoveredCell (rho zL zH : ℝ) (c : TaggedCell)
    (hmem : c.compartment.1 ∈ extractionDomain rho zL zH c.high c.compartment.2)
    (x : ExtractionStoppedCounts (extractionDomain rho zL zH c.high c.compartment.2)) : TaggedCell :=
  ⟨c.high,((x.getD ⟨c.compartment.1,hmem⟩).val,c.compartment.2)⟩

theorem extraction_recovered_ready (rho zL zH : ℝ) (c : TaggedCell)
    (hmem : c.compartment.1 ∈ extractionDomain rho zL zH c.high c.compartment.2)
    (x : ExtractionStoppedCounts (extractionDomain rho zL zH c.high c.compartment.2))
    (hx : x ∈ extractionCellReady rho zL zH c) :
    extractionCellEnergy rho zL zH (extractionRecoveredCell rho zL zH c hmem x) ≤ readyLevel := by
  cases x with
  | none => exact False.elim hx
  | some d => exact hx

def extractionRecoveredRefill (M : ℕ) (rho zL zH : ℝ) (c : Fin M → TaggedCell)
    (hmem : ∀ i, (c i).compartment.1 ∈ extractionDomain rho zL zH (c i).high (c i).compartment.2)
    (x : ∀ i, ExtractionStoppedCounts (extractionDomain rho zL zH (c i).high (c i).compartment.2)) : ProductiveState :=
  ⟨SerialTransferSelection.preparePhaseBatch (List.ofFn (fun i => extractionRecoveredCell rho zL zH (c i) (hmem i) (x i))),0⟩

theorem extraction_refill_ready (N M : ℕ) (rho zL zH : ℝ) (c : Fin M → TaggedCell)
    (hmem : ∀ i, (c i).compartment.1 ∈ extractionDomain rho zL zH (c i).high (c i).compartment.2)
    (hv : ∀ i, N ≤ (c i).compartment.2 ∧ (c i).compartment.2 < 2*N)
    (x : ∀ i, ExtractionStoppedCounts (extractionDomain rho zL zH (c i).high (c i).compartment.2))
    (hx : ∀ i, x i ∈ extractionCellReady rho zL zH (c i)) :
    ProductiveReadyPopulation N M rho zL zH (extractionRecoveredRefill M rho zL zH c hmem x) := by
  refine ⟨by simp [extractionRecoveredRefill,SerialTransferSelection.preparePhaseBatch],rfl,rfl,?_,?_,rfl⟩
  · intro d hd
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hd
    exact hv i
  · intro d hd
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hd
    exact extraction_recovered_ready rho zL zH (c i) (hmem i) (x i) (hx i)

theorem extraction_refill_ancestry (M : ℕ) (rho zL zH : ℝ) (c : Fin M → TaggedCell)
    (hmem : ∀ i, (c i).compartment.1 ∈ extractionDomain rho zL zH (c i).high (c i).compartment.2)
    (x : ∀ i, ExtractionStoppedCounts (extractionDomain rho zL zH (c i).high (c i).compartment.2)) (b : Bool) :
    ancestralCount b (extractionRecoveredRefill M rho zL zH c hmem x).population.live=ancestralCount b (List.ofFn c) ∧
    ancestralMembrane b (extractionRecoveredRefill M rho zL zH c hmem x).population.live=ancestralMembrane b (List.ofFn c) := by
  constructor
  · simp only [SerialTransferSelection.ancestralCount_as_sum,extractionRecoveredRefill,
      SerialTransferSelection.preparePhaseBatch,List.map_ofFn,extractionRecoveredCell]
    rfl
  · simp only [ancestralMembrane,extractionRecoveredRefill,SerialTransferSelection.preparePhaseBatch,
      List.map_ofFn,extractionRecoveredCell]
    rfl

end
end ProductiveMemory

import proofs.ProductiveMemory.ExtractionRefill
import proofs.ProductiveMemory.ExtractionRecoveryService
import proofs.SerialTransferSelection.CycleLawBounds

namespace ProductiveMemory
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Set
open scoped NNReal
noncomputable section
set_option Elab.async false

variable (M N : ℕ) (hN : 1 ≤ N) (rho zL zH : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (c : Fin M → TaggedCell)
    (hmem : ∀ i, (c i).compartment.1 ∈ extractionDomain rho zL zH (c i).high (c i).compartment.2)
    (hv : ∀ i, N ≤ (c i).compartment.2 ∧ (c i).compartment.2 < 2*N)
    (J : Fin M → ℕ)

def extractionRestartOutput
    (x : ∀ i, ExtractionStoppedCounts (extractionDomain rho zL zH (c i).high (c i).compartment.2) × Fin (J i+1))
    (hx : x ∈ extractionServiceGood M rho zL zH c J) : ProductiveReady N M rho zL zH :=
  ⟨extractionRecoveredRefill M rho zL zH c hmem (fun i => (x i).1),
    productiveReady_mem N M hN rho zL zH hr hzL hzH _
      (extraction_refill_ready N M rho zL zH c hmem hv (fun i => (x i).1) (fun i => (hx i).1))⟩

def extractionRestartLaw (q : Fin M → NNReal) (hq : ∀ i, 0 < (q i:ℝ))
    (hclock : ∀ i x, (extractionStoppedModel rho (by linarith [hr.1]) (c i).compartment.2
      (extractionDomain rho zL zH (c i).high (c i).compartment.2)).total x ≤ q i) :
    FiniteLaw (Option (ProductiveReady N M rho zL zH)) :=
  SerialTransferSelection.guardedPush (extractionServiceLaw M rho (by linarith [hr.1]) zL zH c hmem J q hq hclock)
    (extractionServiceGood M rho zL zH c J)
    (extractionRestartOutput M N hN rho zL zH hr hzL hzH c hmem hv J)

def extractionRestartAncestry (s : ProductiveReady N M rho zL zH) : Prop :=
  ∀ b, ancestralCount b s.val.population.live=ancestralCount b (List.ofFn c) ∧
    ancestralMembrane b s.val.population.live=ancestralMembrane b (List.ofFn c)

theorem extraction_restart_probability
    (heL : extractDrift rho 0 (lift rho zL)=0) (heH : extractDrift rho 0 (lift rho zH)=0)
    (hm : ∀ i, recoveryCount ≤ (c i).compartment.2)
    (hb : ∀ i, extractionCellEnergy rho zL zH (c i) ≤ 8*readyLevel)
    (hJ : ∀ i, 0 < J i) (q : Fin M → NNReal) (hq : ∀ i, 0 < (q i:ℝ))
    (hclock : ∀ i x, (extractionStoppedModel rho (by linarith [hr.1]) (c i).compartment.2
      (extractionDomain rho zL zH (c i).high (c i).compartment.2)).total x ≤ q i)
    (hk : ∀ i, ((c i).compartment.2:ℝ)*localAlpha*readyLevel/480 ≤ q i)
    (htail : ∀ i, 5376*(q i:ℝ)/(J i:ℝ) ≤ 1/10^18) :
    1-2*(M:ℝ)/10^18 ≤
      (extractionRestartLaw M N hN rho zL zH hr hzL hzH c hmem hv J q hq hclock).expect
        (FiniteKernel.eventIndicator (SerialTransferSelection.successfulOutput (extractionRestartAncestry M N rho zL zH c))) := by
  unfold extractionRestartLaw
  rw [SerialTransferSelection.guardedPush_probability _ _ _ _ (by
    intro x hx b
    exact (extraction_refill_ancestry M rho zL zH c hmem (fun i => (x i).1) b))]
  exact extraction_service_return M rho zL zH hr hzL hzH heL heH c hm hb hmem J hJ q hq hclock hk htail

end
end ProductiveMemory

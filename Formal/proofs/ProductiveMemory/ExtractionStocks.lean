import proofs.ProductiveMemory.ExtractionCycleKernel
import proofs.ProductiveMemory.ExtractionMaterialService

namespace ProductiveMemory
open ResourceLimitedCompetition HeritableCompositions FiniteCopy
noncomputable section
set_option Elab.async false

/-- A fixed pre-run batch allowance, shared by every finite restart state. -/
def productiveBatchStock (N M : ℕ) (rho zL zH gamma : ℝ) (hr : 0 ≤ rho) (hg : 0 ≤ gamma) (t : NNReal) : ℕ :=
  1+∑ s : ProductiveReady N M rho zL zH,
    (extractionBatchSchedule rho gamma hr hg N M (membrane s.val.population.live)
      (productiveCollectionQuota N M rho t) zL zH t).service

/-- Fixed per-cell allowance covering every literal cell in the batch box. -/
def extractionRecoveryStock (N : ℕ) (rho zL zH : ℝ) (hr : 0 ≤ rho) : ℕ :=
  1+∑ c ∈ cellBox N, (extractionRecoverySchedule rho hr zL zH c).quota

theorem productive_batch_stock_covers (N M : ℕ) (rho zL zH gamma : ℝ) (hr : 0 ≤ rho) (hg : 0 ≤ gamma)
    (t : NNReal) (s : ProductiveReady N M rho zL zH) :
    (extractionBatchSchedule rho gamma hr hg N M (membrane s.val.population.live)
      (productiveCollectionQuota N M rho t) zL zH t).service < productiveBatchStock N M rho zL zH gamma hr hg t := by
  classical
  have h := Finset.single_le_sum (s:=Finset.univ)
    (f:=fun s : ProductiveReady N M rho zL zH => (extractionBatchSchedule rho gamma hr hg N M
      (membrane s.val.population.live) (productiveCollectionQuota N M rho t) zL zH t).service)
    (fun s _ => Nat.zero_le _) (Finset.mem_univ s)
  dsimp only at h
  unfold productiveBatchStock
  omega

theorem extraction_recovery_stock_covers (N : ℕ) (rho zL zH : ℝ) (hr : 0 ≤ rho)
    (c : TaggedCell) (hc : c ∈ cellBox N) :
    (extractionRecoverySchedule rho hr zL zH c).quota < extractionRecoveryStock N rho zL zH hr := by
  have h := Finset.single_le_sum (s:=cellBox N)
    (f:=fun c => (extractionRecoverySchedule rho hr zL zH c).quota) (fun c _ => Nat.zero_le _) hc
  dsimp only at h
  unfold extractionRecoveryStock
  omega

/-- One fixed inventory per reservoir covers both batches and every selected-cell recovery. -/
theorem productive_two_cycle_service_stock (N M : ℕ) (rho zL zH gamma : ℝ)
    (hr : 0 ≤ rho) (hg : 0 ≤ gamma) (t : NNReal)
    (s : Fin 2 → ProductiveReady N M rho zL zH)
    (c : Fin 2 → Fin M → TaggedCell) (hc : ∀ j i, c j i ∈ cellBox N)
    (B : Fin 2 → ℕ) (R : Fin 2 → Fin M → ℕ)
    (hB : ∀ j, B j < (extractionBatchSchedule rho gamma hr hg N M (membrane (s j).val.population.live)
      (productiveCollectionQuota N M rho t) zL zH t).service)
    (hR : ∀ j i, R j i < (extractionRecoverySchedule rho hr zL zH (c j i)).quota) :
    (∑ j, (B j+(∑ i, R j i))) <
      2*(productiveBatchStock N M rho zL zH gamma hr hg t+M*extractionRecoveryStock N rho zL zH hr) := by
  apply SerialTransferSelection.two_cycle_gross_allowance
  · intro j
    exact (hB j).trans (productive_batch_stock_covers N M rho zL zH gamma hr hg t (s j))
  · intro j i
    exact (hR j i).trans (extraction_recovery_stock_covers N rho zL zH hr (c j i) (hc j i))

end
end ProductiveMemory

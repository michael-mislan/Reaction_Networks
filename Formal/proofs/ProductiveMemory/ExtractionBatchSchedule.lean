import proofs.ProductiveMemory.ExtractionBatchService

namespace ProductiveMemory
open ResourceLimitedCompetition HeritableCompositions FiniteCopy
open scoped NNReal
noncomputable section
set_option Elab.async false

structure ExtractionCollectionCapacity (N M : ℕ) (rho : ℝ) (t : NNReal) where
  quota : ℕ
  positive : 0 < quota
  error_le : (t:ℝ)*(560*(N:ℝ)*(M:ℝ)*rho)/(quota:ℝ) ≤ 1/10^6

def extractionCollectionCapacity (N M : ℕ) (rho : ℝ) (t : NNReal) :
    ExtractionCollectionCapacity N M rho t := by
  have h : Nonempty (ExtractionCollectionCapacity N M rho t) := by
    obtain ⟨J,hJ,ht⟩ := SerialTransferSelection.exists_finite_service_quota
      (560*(N:ℝ)*(M:ℝ)*rho) (t:ℝ) (1/10^6) (by norm_num)
    exact ⟨⟨J,hJ,ht.le⟩⟩
  exact Classical.choice h

structure ExtractionBatchSchedule (rho γ : ℝ) (hr : 0 ≤ rho) (hg : 0 ≤ γ)
    (N M W0 J : ℕ) (zL zH : ℝ) (t : NNReal) where
  clock : NNReal
  service : ℕ
  clock_pos : 0 < (clock:ℝ)
  service_pos : 0 < service
  decay_le : (9/40000)*(N:ℝ)*γ ≤ clock
  total_le : ∀ x, (productiveStoppedModel rho γ hr hg (4*W0) N W0 J zL zH
    (productiveActiveDomain N M W0 J rho zL zH)).total x ≤ clock
  error_le : (t:ℝ)*clock/(service:ℝ) ≤ 1/10^6

def extractionBatchSchedule (rho γ : ℝ) (hr : 0 ≤ rho) (hg : 0 ≤ γ)
    (N M W0 J : ℕ) (zL zH : ℝ) (t : NNReal) : ExtractionBatchSchedule rho γ hr hg N M W0 J zL zH t := by
  classical
  have h : Nonempty (ExtractionBatchSchedule rho γ hr hg N M W0 J zL zH t) := by
    obtain ⟨q,hq,hk,hclock⟩ := (productiveStoppedModel rho γ hr hg (4*W0) N W0 J zL zH
      (productiveActiveDomain N M W0 J rho zL zH)).exists_clock ((9/40000)*(N:ℝ)*γ)
    obtain ⟨J,hJ,ht⟩ := SerialTransferSelection.exists_finite_service_quota (q:ℝ) (t:ℝ) (1/10^6) (by norm_num)
    exact ⟨⟨q,J,hq,hJ,hk,hclock,ht.le⟩⟩
  exact Classical.choice h

end
end ProductiveMemory

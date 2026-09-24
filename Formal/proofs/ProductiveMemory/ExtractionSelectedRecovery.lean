import proofs.ProductiveMemory.ExtractionRestart
import proofs.ProductiveMemory.ExtractionRecoverySchedule

namespace ProductiveMemory
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Set
noncomputable section
set_option Elab.async false

variable (N M : ℕ) (hN : 1 ≤ N) (hlarge : recoveryCount ≤ N) (rho zL zH : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (s : PopulationState) (hv : ValidVolumes N s)
    (he : ∀ c ∈ s.live, extractionCellEnergy rho zL zH c < 8*readyLevel)
    (S : SerialTransferSelection.TransferSubset s.live.length M)

def extractionSelectedRecoveryLaw : FiniteLaw (Option (ProductiveReady N M rho zL zH)) := by
  classical
  let c := extractionRetained M s S
  let hmem := fun i => extraction_cell_admitted rho zL zH hr hzL hzH (c i)
    (hlarge.trans (hv _ (extraction_retained_mem M s S i)).1) (he _ (extraction_retained_mem M s S i)).le
  let schedule := fun i => extractionRecoverySchedule rho (by linarith [hr.1]) zL zH (c i)
  exact extractionRestartLaw M N hN rho zL zH hr hzL hzH c hmem
    (fun i => hv _ (extraction_retained_mem M s S i))
    (fun i => (schedule i).quota) (fun i => (schedule i).clock)
    (fun i => (schedule i).clock_pos) (fun i => (schedule i).total_le)

def extractionSelectedAncestry (y : ProductiveReady N M rho zL zH) : Prop :=
  extractionRestartAncestry M N rho zL zH (extractionRetained M s S) y

theorem extraction_selected_probability
    (heL : extractDrift rho 0 (lift rho zL)=0) (heH : extractDrift rho 0 (lift rho zH)=0) :
    1-2*(M:ℝ)/10^18 ≤
      (extractionSelectedRecoveryLaw N M hN hlarge rho zL zH hr hzL hzH s hv he S).expect
        (FiniteKernel.eventIndicator (SerialTransferSelection.successfulOutput
          (extractionSelectedAncestry N M rho zL zH s S))) := by
  classical
  unfold extractionSelectedRecoveryLaw
  dsimp only
  apply extraction_restart_probability M N hN rho zL zH hr hzL hzH
    (extractionRetained M s S) _ _ _ heL heH
  · intro i
    exact hlarge.trans (hv _ (extraction_retained_mem M s S i)).1
  · intro i
    exact (he _ (extraction_retained_mem M s S i)).le
  · intro i
    exact (extractionRecoverySchedule rho (by linarith [hr.1]) zL zH (extractionRetained M s S i)).quota_pos
  · intro i
    exact (extractionRecoverySchedule rho (by linarith [hr.1]) zL zH (extractionRetained M s S i)).decay_le
  · intro i
    exact (extractionRecoverySchedule rho (by linarith [hr.1]) zL zH (extractionRetained M s S i)).quota_error

theorem extraction_retained_list : List.ofFn (extractionRetained M s S) =
    (SerialTransferSelection.exchangeSelectedMedium M s S).live :=
  SerialTransferSelection.retainedVector_list M s S

theorem extraction_selected_ancestry_physical (y : ProductiveReady N M rho zL zH)
    (hy : extractionSelectedAncestry N M rho zL zH s S y) (b : Bool) :
    ancestralCount b y.val.population.live=ancestralCount b (SerialTransferSelection.exchangeSelectedMedium M s S).live ∧
    ancestralMembrane b y.val.population.live=ancestralMembrane b (SerialTransferSelection.exchangeSelectedMedium M s S).live := by
  have h := hy b
  simpa only [extraction_retained_list] using h

end
end ProductiveMemory

import proofs.SerialTransferSelection.RecoveryRefill

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set

/-- One finite restart space, containing all admitted division phases. -/
noncomputable def readyPopulationDomain (N M : ℕ) (zL zH : ℝ) : Finset PopulationState := by
  classical
  exact (phasePopulationBox N M (2*N*M)).filter (PhaseReadyPopulation N M zL zH)

abbrev ReadyPopulation (N M : ℕ) (zL zH : ℝ) :=
  {s : PopulationState // s ∈ readyPopulationDomain N M zL zH}

theorem readyPopulation_ready (N M : ℕ) (zL zH : ℝ) (s : ReadyPopulation N M zL zH) :
    PhaseReadyPopulation N M zL zH s.val := by
  classical
  exact (Finset.mem_filter.mp s.property).2

theorem readyPopulation_mem (N M : ℕ) (hN : 1 ≤ N) (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (s : PopulationState) (hs : PhaseReadyPopulation N M zL zH s) :
    s ∈ readyPopulationDomain N M zL zH := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨?_,hs⟩
  obtain ⟨hlen,hD,hQ,hv,he⟩ := hs
  apply (mem_phasePopulationBox N M (2*N*M) s).mpr
  have hw := membrane_upper N s.live (fun c hc => (hv c hc).2.le)
  rw [hlen] at hw
  refine ⟨by rw [hQ]; omega,⟨by omega,?_⟩,by omega⟩
  intro c hc
  apply safe_cell_in_box N hN zL zH hzL hzH c (hv c hc).1 (hv c hc).2.le
  exact (he c hc).trans_lt (by norm_num [innerEnergy,outerEnergy])

/-- No additional readiness hypothesis is hidden in the finite restart encoding. -/
theorem readyPopulation_mem_iff (N M : ℕ) (hN : 1 ≤ N) (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (s : PopulationState) : s ∈ readyPopulationDomain N M zL zH ↔ PhaseReadyPopulation N M zL zH s :=
  ⟨fun hs => readyPopulation_ready N M zL zH ⟨s,hs⟩,
    readyPopulation_mem N M hN zL zH hzL hzH s⟩

end SerialTransferSelection

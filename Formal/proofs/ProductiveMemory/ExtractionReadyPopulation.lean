import proofs.ProductiveMemory.ExtractionInitial

namespace ProductiveMemory
noncomputable section
set_option Elab.async false
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set

/-- One finite restart space, containing all admitted division phases. -/
noncomputable def productiveReadyDomain (N M : ℕ) (rho zL zH : ℝ) : Finset ProductiveState := by
  classical
  exact (productiveBox N M (2*N*M) 1).filter (ProductiveReadyPopulation N M rho zL zH)

abbrev ProductiveReady (N M : ℕ) (rho zL zH : ℝ) :=
  {s : ProductiveState // s ∈ productiveReadyDomain N M rho zL zH}

theorem productiveReady_ready (N M : ℕ) (rho zL zH : ℝ) (s : ProductiveReady N M rho zL zH) :
    ProductiveReadyPopulation N M rho zL zH s.val := by
  classical
  exact (Finset.mem_filter.mp s.property).2

theorem productiveReady_mem (N M : ℕ) (hN : 1 ≤ N) (rho zL zH : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (s : ProductiveState) (hs : ProductiveReadyPopulation N M rho zL zH s) :
    s ∈ productiveReadyDomain N M rho zL zH := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨?_,hs⟩
  obtain ⟨hlen,hD,hQ,hv,he,hE⟩ := hs
  apply (mem_productiveBox N M (2*N*M) 1 s).mpr
  refine ⟨?_,by omega⟩
  apply (SerialTransferSelection.mem_phasePopulationBox N M (2*N*M) s.population).mpr
  have hw := membrane_upper N s.population.live (fun c hc => (hv c hc).2.le)
  rw [hlen] at hw
  refine ⟨by rw [hQ]; omega,⟨by omega,?_⟩,by omega⟩
  intro c hc
  apply extraction_cell_in_box rho zL zH hr hzL hzH N hN c (hv c hc).1 (hv c hc).2.le
  exact (he c hc).trans_lt (by norm_num [readyLevel,outerLevel])

/-- No additional readiness hypothesis is hidden in the finite restart encoding. -/
theorem productiveReady_mem_iff (N M : ℕ) (hN : 1 ≤ N) (rho zL zH : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (s : ProductiveState) : s ∈ productiveReadyDomain N M rho zL zH ↔ ProductiveReadyPopulation N M rho zL zH s :=
  ⟨fun hs => productiveReady_ready N M rho zL zH ⟨s,hs⟩,
    productiveReady_mem N M hN rho zL zH hr hzL hzH s⟩

end
end ProductiveMemory

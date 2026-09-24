import proofs.ProductiveMemory.ExtractionInitialLattice
import proofs.SerialTransferSelection.NewbornPhase
import proofs.ProductiveMemory.ExtractionNetProduction
namespace ProductiveMemory
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Set
noncomputable section
set_option Elab.async false
theorem extraction_balanced_newborn (N K : ℕ) (hN : 1000000000000 ≤ N)
    (rho zL zH : ℝ) (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000)) :
    ∃ s : ProductiveReady N (2*K) rho zL zH, (∀ b, ancestralCount b s.val.population.live=K) ∧ (∀ c ∈ s.val.population.live, c.compartment.2=N) := by
  have hposL := reconstructed_positive rho zL (by linarith [hr.1]) (by linarith [hzL.1])
  have hposH := reconstructed_positive rho zH (by linarith [hr.1]) (by linarith [hzH.1])
  obtain ⟨nL,hL⟩ := extraction_rounded_ready N hN (lift rho zL) (fun i => (hposL i).le)
    lowExtractionEnergy lowExtractionEnergy_upper
  obtain ⟨nH,hH⟩ := extraction_rounded_ready N hN (lift rho zH) (fun i => (hposH i).le)
    highExtractionEnergy highExtractionEnergy_upper
  let s : ProductiveState := ⟨SerialTransferSelection.preparePhaseBatch (SerialTransferSelection.balancedCells K N nL nH),0⟩
  have hmem (c : TaggedCell) (hc : c ∈ s.population.live) :
      c=⟨false,(nL,N)⟩ ∨ c=⟨true,(nH,N)⟩ := by
    obtain hc | hc := List.mem_append.mp hc
    · exact Or.inl (List.mem_replicate.mp hc).2
    · exact Or.inr (List.mem_replicate.mp hc).2
  have hs : ProductiveReadyPopulation N (2*K) rho zL zH s := by
    refine ⟨?_,rfl,rfl,?_,?_,rfl⟩
    · simp [s,SerialTransferSelection.preparePhaseBatch,SerialTransferSelection.balancedCells]
      omega
    · intro c hc
      obtain rfl | rfl := hmem c hc <;> exact ⟨le_rfl,by change N < 2*N; omega⟩
    · intro c hc
      obtain rfl | rfl := hmem c hc
      · exact hL
      · exact hH
  refine ⟨⟨s,productiveReady_mem N (2*K) (by omega) rho zL zH hr hzL hzH s hs⟩,?_⟩
  constructor
  · intro b
    exact SerialTransferSelection.balancedCells_count K N nL nH b
  · intro c hc
    obtain rfl | rfl := hmem c hc <;> rfl

theorem batch_net_production_covers_export (N : ℕ) (initial s : ProductiveState)
    (P : ℝ) (G D : ℕ) (hist : ProductiveHistory N initial s P G D)
    (hE : initial.collected=0) (hz : zInventory initial.population.live ≤ G) :
    (s.collected:ℝ) ≤ P := by
  have h := productive_history_z_account N initial s P G D hist
  rw [chemicalInventory_z_cast,chemicalInventory_z_cast,hE] at h
  have hz' : (zInventory initial.population.live:ℝ) ≤ G := by exact_mod_cast hz
  have hf := Nat.cast_nonneg (α:=ℝ) (zInventory s.population.live)
  have hd := Nat.cast_nonneg (α:=ℝ) D
  norm_num only [Nat.cast_zero,sub_zero] at h
  linarith only [h,hz',hf,hd]
end
end ProductiveMemory

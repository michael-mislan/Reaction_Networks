import proofs.ProductiveMemory.ExtractionReadyPopulation
import proofs.FiniteCopy.InitialLattice
import proofs.SerialTransferSelection.InitialPopulation

namespace ProductiveMemory
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Set
noncomputable section
set_option Elab.async false

theorem extraction_rounded_ready (N : ℕ) (hN : 1000000000000 ≤ N)
    (s : Point) (hs : ∀ i, 0 ≤ s i) (E : Point → ℝ)
    (hE : ∀ y, E y ≤ 60*normSq y) :
    ∃ n : Counts, E (fun i => concentration N n i-s i) ≤ readyLevel := by
  let n : Counts := fun i => ⌊(N:ℝ)*s i⌋₊
  let y : Point := fun i => concentration N n i-s i
  have hy (i : Fin 4) : |y i| ≤ 1/1000000000000 := by
    have hf := floor_concentration_bounds N hN (s i) (hs i)
    change |(⌊(N:ℝ)*s i⌋₊:ℝ)/(N:ℝ)-s i| ≤ _
    apply abs_le.mpr
    constructor <;> linarith only [hf.1,hf.2]
  have hsq (i : Fin 4) : (y i)^2 ≤ (1/1000000000000:ℝ)^2 := by
    have h := (abs_le.mp (hy i))
    nlinarith only [h.1,h.2]
  have hnorm : normSq y ≤ 4*(1/1000000000000:ℝ)^2 := by
    have h0 := hsq 0
    have h1 := hsq 1
    have h2 := hsq 2
    have h3 := hsq 3
    unfold normSq
    linarith only [h0,h1,h2,h3]
  refine ⟨n,(hE y).trans ?_⟩
  norm_num [readyLevel,outerLevel]
  linarith only [hnorm]

theorem extraction_balanced_initial (N K : ℕ) (hN : 1000000000000 ≤ N)
    (rho zL zH : ℝ) (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000)) :
    ∃ s : ProductiveReady N (2*K) rho zL zH, ∀ b, ancestralCount b s.val.population.live=K := by
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
  intro b
  exact SerialTransferSelection.balancedCells_count K N nL nH b

end
end ProductiveMemory

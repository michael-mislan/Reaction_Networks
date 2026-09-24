import proofs.SerialTransferSelection.ReadyPopulation
import proofs.SerialTransferSelection.ReadyRegions

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set

def balancedCells (K N : ℕ) (nL nH : Counts) : List TaggedCell :=
  List.replicate K ⟨false,(nL,N)⟩ ++ List.replicate K ⟨true,(nH,N)⟩

theorem balancedCells_count (K N : ℕ) (nL nH : Counts) (b : Bool) :
    ancestralCount b (balancedCells K N nL nH)=K := by
  cases b <;> simp [ancestralCount,balancedCells]

theorem balanced_initial_nonempty (N K : ℕ) (hN : 1000000000000 ≤ N) (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000)) :
    ∃ s : ReadyPopulation N (2*K) zL zH, ∀ b, ancestralCount b s.val.live=K := by
  obtain ⟨nL,hL⟩ := low_ready_nonempty zL hzL N N hN le_rfl (by omega)
  obtain ⟨nH,hH⟩ := high_ready_nonempty zH hzH N N hN le_rfl (by omega)
  let s := preparePhaseBatch (balancedCells K N nL nH)
  have hmem (c : TaggedCell) (hc : c ∈ s.live) :
      c=⟨false,(nL,N)⟩ ∨ c=⟨true,(nH,N)⟩ := by
    obtain hc | hc := List.mem_append.mp hc
    · exact Or.inl (List.mem_replicate.mp hc).2
    · exact Or.inr (List.mem_replicate.mp hc).2
  have hs : PhaseReadyPopulation N (2*K) zL zH s := by
    refine ⟨?_,rfl,rfl,?_,?_⟩
    · simp [s,preparePhaseBatch,balancedCells]
      omega
    · intro c hc
      obtain rfl | rfl := hmem c hc <;> exact ⟨le_rfl,by change N < 2*N; omega⟩
    · intro c hc
      obtain rfl | rfl := hmem c hc
      · exact hL.2.2
      · exact hH.2.2
  refine ⟨⟨s,readyPopulation_mem N (2*K) (by omega) zL zH hzL hzH s hs⟩,?_⟩
  intro b
  exact balancedCells_count K N nL nH b

end SerialTransferSelection

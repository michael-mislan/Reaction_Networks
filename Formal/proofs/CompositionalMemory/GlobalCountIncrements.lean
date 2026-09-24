import proofs.CompositionalMemory.LocalCountGrowth

namespace CompositionalMemory
open FiniteCopy

noncomputable def globalMoleculeCount {k : ℕ} (s : ModularCountState k) : ℝ :=
  (s.2 : ℝ)+∑ i, localMoleculeCount (s.1 i)

theorem sum_local_count_update {k : ℕ} (n : Fin k → Counts) (i : Fin k) (b : Counts) :
    (∑ j, localMoleculeCount (Function.update n i b j))-(∑ j, localMoleculeCount (n j)) =
      localMoleculeCount b-localMoleculeCount (n i) := by
  classical
  have he : (fun j => localMoleculeCount (Function.update n i b j)) =
      Function.update (fun j => localMoleculeCount (n j)) i (localMoleculeCount b) := by
    funext j
    by_cases hj : j=i
    · subst j
      simp
    · simp only [Function.update_of_ne hj]
  rw [he,Finset.sum_update_of_mem (Finset.mem_univ i)]
  have hb := Finset.sum_update_of_mem (Finset.mem_univ i) (fun j => localMoleculeCount (n j)) (localMoleculeCount (n i))
  simp only [Function.update_eq_self] at hb
  rw [hb]
  ring

theorem consuming_local_count (n : Counts) (hn : 1 ≤ n 2) :
    localMoleculeCount (Function.update n 2 (n 2-1)) = localMoleculeCount n-1 := by
  unfold localMoleculeCount
  simp_rw [consuming_count_cast n hn]
  rw [Finset.sum_sub_distrib]
  simp

theorem receiving_local_count (n : Counts) :
    localMoleculeCount (Function.update n 2 (n 2+1)) = localMoleculeCount n+1 := by
  unfold localMoleculeCount
  simp_rw [receiving_count_cast n]
  rw [Finset.sum_add_distrib]
  simp

theorem resident_global_count_increment {k : ℕ} (s : ModularCountState k) (i : Fin k) (r : Fin 13) :
    globalMoleculeCount (modularNext s (.inl (i,r)))-globalMoleculeCount s =
      localMoleculeCount (nextCounts (s.1 i) r)-localMoleculeCount (s.1 i) := by
  have h := sum_local_count_update s.1 i (nextCounts (s.1 i) r)
  dsimp [globalMoleculeCount,modularNext]
  linarith only [h]

theorem membrane_global_count_increment {k : ℕ} (s : ModularCountState k) (i : Fin k)
    (hn : 1 ≤ s.1 i 2) :
    globalMoleculeCount (modularNext s (.inr (.inr i)))-globalMoleculeCount s = 0 := by
  have h := sum_local_count_update s.1 i (Function.update (s.1 i) 2 (s.1 i 2-1))
  rw [consuming_local_count _ hn] at h
  dsimp [globalMoleculeCount,modularNext]
  push_cast
  linarith only [h]

theorem exchange_global_count_increment {k : ℕ} (s : ModularCountState k) (i j : Fin k)
    (hn : 1 ≤ s.1 i 2) :
    globalMoleculeCount (modularNext s (.inr (.inl (i,j))))-globalMoleculeCount s = 0 := by
  classical
  by_cases hij : i=j
  · simp [modularNext,hij]
  · have h₀ := sum_local_count_update s.1 i (Function.update (s.1 i) 2 (s.1 i 2-1))
    have h₁ := sum_local_count_update (Function.update s.1 i (Function.update (s.1 i) 2 (s.1 i 2-1)))
      j (Function.update (s.1 j) 2 (s.1 j 2+1))
    rw [consuming_local_count _ hn] at h₀
    rw [receiving_local_count,Function.update_of_ne (Ne.symm hij)] at h₁
    simp only [modularNext,if_neg hij,globalMoleculeCount]
    linarith only [h₀,h₁]

end CompositionalMemory

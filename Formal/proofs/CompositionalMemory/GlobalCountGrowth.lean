import proofs.CompositionalMemory.GlobalCountIncrements

namespace CompositionalMemory
open FiniteCopy

theorem membrane_count_rate_zero {k : ℕ} (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (s : ModularCountState k) (i : Fin k) :
    modularRate γ w s (.inr (.inr i))*
      (globalMoleculeCount (modularNext s (.inr (.inr i)))-globalMoleculeCount s) = 0 := by
  by_cases hn : 1 ≤ s.1 i 2
  · rw [membrane_global_count_increment s i hn,mul_zero]
  · have hz : s.1 i 2=0 := by omega
    simp [modularRate,hz]

theorem exchange_count_rate_zero {k : ℕ} (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (s : ModularCountState k) (i j : Fin k) :
    modularRate γ w s (.inr (.inl (i,j)))*
      (globalMoleculeCount (modularNext s (.inr (.inl (i,j))))-globalMoleculeCount s) = 0 := by
  by_cases hn : 1 ≤ s.1 i 2
  · rw [exchange_global_count_increment s i j hn,mul_zero]
  · have hz : s.1 i 2=0 := by omega
    simp [modularRate,hz]

theorem global_count_growth {k : ℕ} (hk : 1 ≤ k) (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (s : ModularCountState k) (hm : 0 < s.2) :
    modularGenerator γ w globalMoleculeCount s ≤ 33*globalMoleculeCount s := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hmpos : (0 : ℝ) < s.2 := by exact_mod_cast hm
  have hv : (0 : ℝ) < (s.2 : ℝ)/k := div_pos hmpos hkpos
  have hlocal (i) := local_count_growth ((s.2 : ℝ)/k) hv (s.1 i)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hlocal i)
  have hconst : (∑ _i : Fin k, 33*((s.2 : ℝ)/k)) = 33*(s.2 : ℝ) := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  rw [Finset.sum_add_distrib,hconst] at hsum
  have hnon : 0 ≤ ∑ i, localMoleculeCount (s.1 i) := by
    apply Finset.sum_nonneg
    intro i _
    exact Finset.sum_nonneg (fun a _ => Nat.cast_nonneg (s.1 i a))
  simp only [modularGenerator,Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp only [membrane_count_rate_zero,exchange_count_rate_zero,Finset.sum_const_zero,add_zero]
  simp only [resident_global_count_increment,modularRate]
  unfold globalMoleculeCount
  linarith only [hsum,hnon]

end CompositionalMemory

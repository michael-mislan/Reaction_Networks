import proofs.CompositionalMemory.GlobalCountGrowth
import proofs.CompositionalMemory.ProductDomain

namespace CompositionalMemory
open FiniteCopy

theorem local_count_nonneg (n : Counts) : 0 ≤ localMoleculeCount n :=
  Finset.sum_nonneg (fun a _ => Nat.cast_nonneg (n a))

theorem membrane_le_global_count {k : ℕ} (s : ModularCountState k) :
    (s.2 : ℝ) ≤ globalMoleculeCount s := by
  have h := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => local_count_nonneg (s.1 i))
  unfold globalMoleculeCount
  linarith only [h]

theorem global_count_nonneg {k : ℕ} (s : ModularCountState k) :
    0 ≤ globalMoleculeCount s := (Nat.cast_nonneg s.2).trans (membrane_le_global_count s)

theorem coordinate_le_global_count {k : ℕ} (s : ModularCountState k) (i : Fin k) (a : Fin 4) :
    (s.1 i a : ℝ) ≤ globalMoleculeCount s := by
  have ha : (s.1 i a : ℝ) ≤ localMoleculeCount (s.1 i) :=
    Finset.single_le_sum (fun b _ => Nat.cast_nonneg (s.1 i b)) (Finset.mem_univ a)
  have hi : localMoleculeCount (s.1 i) ≤ ∑ j, localMoleculeCount (s.1 j) :=
    Finset.single_le_sum (fun j _ => local_count_nonneg (s.1 j)) (Finset.mem_univ i)
  unfold globalMoleculeCount
  have hm : (0 : ℝ) ≤ s.2 := Nat.cast_nonneg _
  linarith only [ha,hi,hm]

noncomputable def countCutoff (k R : ℕ) : Finset (ModularCountState k) := by
  classical
  exact ((modularCountBox k R).product (Finset.Icc 1 R)).filter
    (fun s => globalMoleculeCount s ≤ (R : ℝ))

theorem mem_countCutoff {k : ℕ} (R : ℕ) (s : ModularCountState k) :
    s ∈ countCutoff k R ↔ 0 < s.2 ∧ globalMoleculeCount s ≤ (R : ℝ) := by
  classical
  change (s.1,s.2) ∈ countCutoff k R ↔ _
  simp only [countCutoff,Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc]
  constructor
  · rintro ⟨⟨_,hm,_⟩,hR⟩
    exact ⟨by omega,hR⟩
  · rintro ⟨hm,hR⟩
    have hmem : s.2 ≤ R := by exact_mod_cast (membrane_le_global_count s).trans hR
    have hbox : s.1 ∈ modularCountBox k R := by
      apply (mem_modularCountBox R s.1).mpr
      intro i a
      have hc : s.1 i a ≤ R := by exact_mod_cast (coordinate_le_global_count s i a).trans hR
      omega
    exact ⟨⟨hbox,by omega,hmem⟩,hR⟩

theorem modular_membrane_positive {k : ℕ} (s : ModularCountState k)
    (hm : 0 < s.2) (r : ModularChannel k) : 0 < (modularNext s r).2 := by
  rcases r with ⟨i,r⟩ | ⟨i,j⟩ | i
  · exact hm
  · by_cases h : i=j <;> simpa [modularNext,h] using hm
  · simp only [modularNext]
    omega

theorem count_cutoff_departure {k : ℕ} (R : ℕ) (s : ModularCountState k)
    (hs : s ∈ countCutoff k R) (r : ModularChannel k)
    (hout : modularNext s r ∉ countCutoff k R) :
    (R : ℝ) ≤ globalMoleculeCount (modularNext s r) := by
  have hm := modular_membrane_positive s ((mem_countCutoff R s).mp hs).1 r
  have hh : ¬ globalMoleculeCount (modularNext s r) ≤ (R : ℝ) := by
    intro h
    exact hout ((mem_countCutoff R _).mpr ⟨hm,h⟩)
  exact (lt_of_not_ge hh).le

end CompositionalMemory

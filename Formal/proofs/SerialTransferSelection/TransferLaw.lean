import proofs.HeritableCompositions.FiniteLaw
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort

namespace SerialTransferSelection
open HeritableCompositions FiniteCopy

noncomputable def uniformFiniteLaw (α : Type*) [Fintype α] [Nonempty α] : FiniteLaw α where
  mass := fun _ => (Fintype.card α : ℝ)⁻¹
  nonneg := fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast (Fintype.card_ne_zero : Fintype.card α ≠ 0))

abbrev TransferSubset (L M : ℕ) := {S : Finset (Fin L) // S.card=M}

theorem transfer_subset_nonempty (L M : ℕ) (hM : M ≤ L) : Nonempty (TransferSubset L M) := by
  classical
  have h : M ≤ (Finset.univ : Finset (Fin L)).card := by simpa using hM
  obtain ⟨S,_,hS⟩ := Finset.exists_subset_card_eq h
  exact ⟨S,hS⟩

noncomputable def uniformTransferLaw (L M : ℕ) (hM : M ≤ L) : FiniteLaw (TransferSubset L M) := by
  classical
  letI := transfer_subset_nonempty L M hM
  exact uniformFiniteLaw _

/-- Exactly M intact cells, ordered by original index; no tag/readout enters selection. -/
def retainSubset {α : Type*} (L M : ℕ) (cells : Fin L → α) (S : TransferSubset L M) : List α :=
  (S.val.sort (· ≤ ·)).map cells

theorem retainSubset_length {α : Type*} (L M : ℕ) (cells : Fin L → α) (S : TransferSubset L M) :
    (retainSubset L M cells S).length=M := by
  simp [retainSubset,S.property]

theorem retainSubset_mem {α : Type*} (L M : ℕ) (cells : Fin L → α) (S : TransferSubset L M)
    (c : α) (hc : c ∈ retainSubset L M cells S) : ∃ i ∈ S.val, cells i=c := by
  simpa only [retainSubset,List.mem_map,Finset.mem_sort] using hc

end SerialTransferSelection

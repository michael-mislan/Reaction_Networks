import proofs.SerialTransferSelection.TransferPhysical

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

/-- All unselected intact cells go to the explicitly recorded discard stream. -/
def discardedCells {α : Type*} (L M : ℕ) (cells : Fin L → α) (S : TransferSubset L M) : List α :=
  (S.valᶜ.sort (· ≤ ·)).map cells

theorem discardedCells_length {α : Type*} (L M : ℕ) (cells : Fin L → α) (S : TransferSubset L M) :
    (discardedCells L M cells S).length=L-M := by
  simp only [discardedCells,List.length_map,Finset.length_sort]
  rw [Finset.card_compl,S.property,Fintype.card_fin]

/-- Exact accounting for any molecular coordinate, size material or cell count. -/
theorem retained_discarded_quantity {α : Type*} (L M : ℕ) (cells : Fin L → α)
    (S : TransferSubset L M) (F : α → ℕ) :
    ((retainSubset L M cells S).map F).sum+((discardedCells L M cells S).map F).sum =
      ∑ i, F (cells i) := by
  have hs (A : Finset (Fin L)) : ((A.sort (· ≤ ·)).map (fun i => F (cells i))).sum =
      ∑ i ∈ A, F (cells i) := by
    have h := ((Finset.sort_perm_toList A (· ≤ ·)).map (fun i => F (cells i))).sum_eq
    simpa only [Finset.sum_map_toList] using h
  simp only [retainSubset,discardedCells,List.map_map,Function.comp_def]
  rw [hs,hs]
  exact Finset.sum_add_sum_compl S.val _

theorem actual_transfer_material_balance (M : ℕ) (s : PopulationState)
    (S : TransferSubset s.live.length M) (F : TaggedCell → ℕ) :
    ((exchangeSelectedMedium M s S).live.map F).sum+
      ((discardedCells s.live.length M (selectedCell s) S).map F).sum=(s.live.map F).sum := by
  have h := retained_discarded_quantity s.live.length M (selectedCell s) S F
  have hs : (∑ i : Fin s.live.length, F (selectedCell s i))=(s.live.map F).sum := by
    simpa only [selectedCell,List.ofFn_getElem_eq_map] using
      (List.sum_ofFn (f := fun i : Fin s.live.length => F s.live[i.val])).symm
  exact h.trans hs

end SerialTransferSelection

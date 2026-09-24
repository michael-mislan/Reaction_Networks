import proofs.RAFQueryCompilation.IndexedFamily

namespace RAFQueryCompilation.ModuleFamily
open RAF

theorem indexed_hub_incident {n : ℕ} (r : Fin (n*2+1)) :
    moleculeCode n (some none) ∈ (indexedSource n).inputs r ∪ (indexedSource n).outputs r := by
  obtain ⟨s,rfl⟩ := (reactionCode n).surjective r
  cases s <;> simp [indexedSource,source]

def indexedColumn {n : ℕ} (r : Fin (n*2+1)) (x : Fin (n*2+1+1)) : ℝ :=
  (if x ∈ (indexedSource n).outputs r then 1 else 0)-
    (if x ∈ (indexedSource n).inputs r then 1 else 0)

theorem indexed_column_relabels {n : ℕ} (r : Reaction n) (x : Molecule n) :
    indexedColumn (reactionCode n r) (moleculeCode n x) = column r x := by
  simp [indexedColumn,indexedSource,column]

theorem indexed_no_common_positive_ray {n : ℕ} {r s : Fin (n*2+1)} (hne : r ≠ s)
    {a : ℝ} (ha : 0 < a) : ¬(∀ x, indexedColumn r x = a*indexedColumn s x) := by
  intro h
  have hd : (reactionCode n).symm r ≠ (reactionCode n).symm s :=
    fun he => hne ((reactionCode n).symm.injective he)
  apply no_common_positive_ray hd ha
  intro x
  have hh := h (moleculeCode n x)
  simpa [indexedColumn,indexedSource,column] using hh

end RAFQueryCompilation.ModuleFamily

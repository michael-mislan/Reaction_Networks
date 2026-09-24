import proofs.RAFQueryCompilation.StateTransition

namespace RAFQueryCompilation
open RAF
variable {M R : Type*} [DecidableEq M] [DecidableEq R]

theorem patch_products_subset (Q : CRS M R) (E removed added : Finset R)
    (hr : removed ⊆ E) (ha : added ⊆ E) :
    (removed ∪ added).biUnion Q.outputs ⊆ E.biUnion Q.outputs := by
  intro x hx
  rcases Finset.mem_biUnion.mp hx with ⟨r,hm,hx⟩
  exact Finset.mem_biUnion.mpr ⟨r,(Finset.union_subset hr ha) hm,hx⟩

theorem local_delta_subset (E oldInside localAnswer : Finset R)
    (ho : oldInside ⊆ E) (hl : localAnswer ⊆ E) :
    oldInside \ localAnswer ⊆ E ∧ localAnswer \ oldInside ⊆ E :=
  ⟨Finset.sdiff_subset.trans ho, Finset.sdiff_subset.trans hl⟩

/-- Distinct written coordinates, separated by the three mutable arrays.
Reads, repeated local counting, sorting and physical copying cost extra. -/
def patchCoordinates (Q : CRS M R) (E D removed added : Finset R) : ℕ :=
  E.card + D.card + ((removed ∪ added).biUnion Q.outputs).card

theorem patchCoordinates_le (Q : CRS M R) (E D removed added : Finset R)
    (hd : D ⊆ E) (hr : removed ⊆ E) (ha : added ⊆ E) :
    patchCoordinates Q E D removed added ≤ 2*E.card + (E.biUnion Q.outputs).card := by
  have hD := Finset.card_le_card hd
  have hO := Finset.card_le_card (patch_products_subset Q E removed added hr ha)
  unfold patchCoordinates
  omega

theorem patchCounts_outside_region {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (counts : Vector ℕ n) (E removed added : Finset (Fin m))
    (hr : removed ⊆ E) (ha : added ⊆ E) (x : Fin n)
    (hx : x ∉ E.biUnion Q.outputs) :
    (patchCounts Q counts removed added)[x.val] = counts[x.val] := by
  have hn : x ∉ (removed ∪ added).biUnion Q.outputs :=
    fun h => hx (patch_products_subset Q E removed added hr ha h)
  rw [patchCounts, modifyVector_get]
  simp only [hn, if_false]

theorem accepted_patch_footprint {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (E D localAnswer : Finset (Fin m)) (oldMask : Fin m → Bool)
    (hd : D ⊆ E) (hl : localAnswer ⊆ E) :
    patchCoordinates Q E D (maskRegion E oldMask \ localAnswer)
      (localAnswer \ maskRegion E oldMask) ≤ 2*E.card + (E.biUnion Q.outputs).card := by
  have hs : maskRegion E oldMask ⊆ E := Finset.filter_subset _ _
  exact patchCoordinates_le Q E D _ _ hd
    (Finset.sdiff_subset.trans hs) (Finset.sdiff_subset.trans hl)

end RAFQueryCompilation

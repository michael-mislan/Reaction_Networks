import proofs.RAFQueryCompilation.Outside

namespace RAFQueryCompilation
open RAF RAF.Frankl

variable {M R : Type*} [DecidableEq M] [Fintype M] [DecidableEq R]

/-- Supply the products of an already generated reaction set as food. -/
def residualSource (Q : CRS M R) (O : Finset R) : CRS M R :=
  { Q with food := Q.food ∪ O.biUnion Q.outputs }

omit [DecidableEq R] in
theorem finiteClosure_le_closed (Q : CRS M R) (S : Finset R) (B : Finset M)
    (hf : Q.food ⊆ B) (hc : closureStep Q S B ⊆ B) :
    finiteClosure Q S ⊆ B :=
  settle_le_closed _ (fun _ _ h => closureStep_mono Q (Finset.Subset.refl S) h)
    _ _ _ hf hc

omit [DecidableEq R] in
theorem outputs_subset_finiteClosure (Q : CRS M R) (S : Finset R) {r : R}
    (hr : r ∈ S) (hi : Q.inputs r ⊆ finiteClosure Q S) :
    Q.outputs r ⊆ finiteClosure Q S := by
  intro x hx
  rw [← finiteClosure_fixed Q S]
  simp only [closureStep, Finset.mem_union, Finset.mem_biUnion]
  exact Or.inr ⟨r, hr, by simpa [Enabled, hi] using hx⟩

/-- A generated outside set can be replaced by its products in molecular closure.
No catalytic ordering assumption is used. -/
theorem residual_closure (Q : CRS M R) (O S : Finset R)
    (hO : FoodGenerated Q O) :
    finiteClosure (residualSource Q O) S = finiteClosure Q (O ∪ S) := by
  have hout : O.biUnion Q.outputs ⊆ finiteClosure Q (O ∪ S) := by
    intro x hx
    obtain ⟨r, hr, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨k, hk⟩ := hO r hr
    have hi : Q.inputs r ⊆ finiteClosure Q (O ∪ S) := hk.trans ((closureAt_subset_finiteClosure Q O k).trans
      (finiteClosure_mono Q Finset.subset_union_left))
    exact outputs_subset_finiteClosure Q (O ∪ S) (Finset.mem_union_left S hr) hi hx
  apply Finset.Subset.antisymm
  · apply finiteClosure_le_closed
    · exact Finset.union_subset (food_subset_finiteClosure Q (O ∪ S)) hout
    · have h := closureStep_mono Q (S := S) (T := O ∪ S)
        Finset.subset_union_right (Finset.Subset.refl (finiteClosure Q (O ∪ S)))
      rw [finiteClosure_fixed] at h
      simpa only [closureStep, residualSource, Enabled] using h
  · apply finiteClosure_le_closed
    · exact Finset.subset_union_left.trans
        (food_subset_finiteClosure (residualSource Q O) S)
    · intro x hx
      simp only [closureStep, Finset.mem_union, Finset.mem_biUnion] at hx
      rcases hx with hx | ⟨r, hr, hx⟩
      · exact hx
      · by_cases he : Enabled Q (finiteClosure (residualSource Q O) S) r
        · have ho : x ∈ Q.outputs r := by simpa [he] using hx
          rcases hr with hr | hr
          · apply food_subset_finiteClosure (residualSource Q O) S
            exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r, hr, ho⟩)
          · exact outputs_subset_finiteClosure (residualSource Q O) S hr he ho
        · simp [he] at hx

end RAFQueryCompilation

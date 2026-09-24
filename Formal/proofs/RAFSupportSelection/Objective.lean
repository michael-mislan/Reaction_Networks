import proofs.RAFSupportSelection.SelectedCone

namespace RAFSupportSelection
open RAFQueryCompilation
variable {R : Type*} [DecidableEq R] [Fintype R]

theorem selectedCone_mono_parents (S K : Finset R) (p q : R → Finset R)
    (hp : ∀ r ∈ S, p r ⊆ q r) :
    selectedCone S p K ⊆ selectedCone S q K := by
  apply selectedCone_le S p K (selectedCone S q K) (selectedCone_seed S q K)
  intro r hr hh
  obtain ⟨t, ht⟩ := hh
  obtain ⟨htp, htD⟩ := Finset.mem_inter.mp ht
  rw [← selectedCone_fixed S q K]
  exact Finset.mem_union_right _ (Finset.mem_filter.mpr
    ⟨hr, t, Finset.mem_inter.mpr ⟨hp r hr htp, htD⟩⟩)

/-- Weighted singleton reachability written by target reaction. -/
def weightedReach (S : Finset R) (p : R → Finset R) (w : R → ℕ) : ℕ :=
  ∑ r ∈ S, ∑ k ∈ S.filter (fun k => r ∈ selectedCone S p {k}), w k

theorem weightedReach_mono (S : Finset R) (p q : R → Finset R) (w : R → ℕ)
    (hp : ∀ r ∈ S, p r ⊆ q r) : weightedReach S p w ≤ weightedReach S q w := by
  apply Finset.sum_le_sum
  intro r _
  apply Finset.sum_le_sum_of_subset
  intro k hk
  obtain ⟨hkS, hkr⟩ := Finset.mem_filter.mp hk
  exact Finset.mem_filter.mpr ⟨hkS, selectedCone_mono_parents S {k} p q hp hkr⟩

/-- Transposing the incidence sum proves that this is precisely weighted
descendant cardinality, including each deleted reaction itself. -/
theorem weightedReach_eq_cones (S : Finset R) (p : R → Finset R) (w : R → ℕ) :
    weightedReach S p w = ∑ k ∈ S, w k * (selectedCone S p {k}).card := by
  unfold weightedReach
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  have he : S.filter (fun r => r ∈ selectedCone S p {k}) = selectedCone S p {k} := by
    ext r
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨selectedCone_subset S p {k} h, h⟩⟩
  rw [← Finset.sum_filter, he]
  simp [Nat.mul_comm]

end RAFSupportSelection

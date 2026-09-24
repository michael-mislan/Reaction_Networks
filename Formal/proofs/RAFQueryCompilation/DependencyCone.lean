import proofs.RAFQueryCompilation.CachedBoundary

namespace RAFQueryCompilation
open RAF
variable {M R : Type*} [DecidableEq M] [Fintype M] [DecidableEq R] [Fintype R]

def dependencyStep (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (E : Finset R) : Finset R :=
  E ∪ Finset.univ.filter (fun r => ∃ e ∈ E, ∃ x ∈ Q.outputs e,
    x ∉ Q.food ∧ (x ∈ Q.inputs r ∨ C x r))

def dependencyCone (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (D : Finset R) : Finset R :=
  settle (dependencyStep Q C) (Fintype.card R) D

omit [Fintype M] in
theorem edits_subset_cone (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (D : Finset R) : D ⊆ dependencyCone Q C D :=
  subset_settle _ (fun _ => Finset.subset_union_left) _ _

omit [Fintype M] in
theorem dependencyCone_fixed (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (D : Finset R) :
    dependencyStep Q C (dependencyCone Q C D) = dependencyCone Q C D :=
  settle_grow_fixed _ (fun _ => Finset.subset_union_left) _ _ (by omega)

omit [Fintype M] in
theorem dependencyCone_independent (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (D : Finset R) :
    OutsideIndependent Q C (dependencyCone Q C D) := by
  intro e he r hr x hx hn
  by_contra hf
  apply hr
  rw [← dependencyCone_fixed Q C D]
  exact Finset.mem_union_right _ (Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, e, he, x, hx, hf, hn⟩)

omit [Fintype M] [Fintype R] in
theorem outside_agree_of_edit_cover (A B D E : Finset R)
    (hc : ∀ r, (r ∈ A ↔ r ∈ B) ∨ r ∈ D) (hd : D ⊆ E) : A \ E = B \ E := by
  ext r
  simp only [Finset.mem_sdiff]
  rcases hc r with h | h
  · rw [h]
  · have he := hd h
    simp [he]

def compiledUpdate (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (oldAnswer B D : Finset R) : Finset R :=
  let E := dependencyCone Q C D
  (oldAnswer \ E) ∪ evaluate (withFood Q (cachedFood Q C oldAnswer E)) C (B ∩ E)

/-- The executable finite cone evaluator answers every covered availability edit. -/
theorem compiledUpdate_correct (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (A B D : Finset R)
    (hc : ∀ r, (r ∈ A ↔ r ∈ B) ∨ r ∈ D) :
    compiledUpdate Q C (evaluate Q C A) B D = evaluate Q C B := by
  exact (evaluate_cached_cone_update Q C A B (dependencyCone Q C D)
    (dependencyCone_independent Q C D)
    (outside_agree_of_edit_cover A B D _ hc (edits_subset_cone Q C D))).symm

end RAFQueryCompilation

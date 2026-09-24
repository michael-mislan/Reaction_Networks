import proofs.RAFQueryCompilation.Closure

namespace RAFQueryCompilation
open RAF RAF.Frankl

variable {M R : Type*} [DecidableEq M] [Fintype M] [DecidableEq R]

def executablePrune (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (S : Finset R) : Finset R :=
  S.filter (fun r => Q.inputs r ⊆ finiteClosure Q S ∧
    ∃ x ∈ finiteClosure Q S, C x r)

omit [DecidableEq R] in
theorem executablePrune_eq (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (S : Finset R) :
    executablePrune Q C S = prune Q C S := by
  ext r
  simp only [executablePrune, Finset.mem_filter, mem_prune, supported_iff_finite]

def evaluate (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (A : Finset R) : Finset R :=
  settle (executablePrune Q C) A.card A

theorem evaluate_subset (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (A : Finset R) : evaluate Q C A ⊆ A := by
  apply settle_subset
  intro S
  rw [executablePrune_eq]
  exact prune_subset Q C S

theorem evaluate_fixed (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (A : Finset R) :
    prune Q C (evaluate Q C A) = evaluate Q C A := by
  rw [← executablePrune_eq]
  apply settle_shrink_fixed _ _ _ _ le_rfl
  intro S
  rw [executablePrune_eq]
  exact prune_subset Q C S

theorem raf_subset_evaluate (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] {A S : Finset R}
    (hs : S ⊆ A) (hr : IsRAF Q C S) : S ⊆ evaluate Q C A := by
  apply fixed_subset_settle _ _ _ _ _ hs
  · rw [executablePrune_eq]
    exact ((isRAF_iff_nonempty_prune_eq Q C S).mp hr).2
  · intro T U h
    simp only [executablePrune_eq]
    exact prune_mono Q C h

/-- Exact literal source semantics, without enumerating any RAF family. -/
theorem evaluate_spec (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (A : Finset R) :
    evaluate Q C A ⊆ A ∧
    (evaluate Q C A = ∅ ∨ IsRAF Q C (evaluate Q C A)) ∧
    ∀ S ⊆ A, IsRAF Q C S → S ⊆ evaluate Q C A := by
  refine ⟨evaluate_subset Q C A, ?_, fun S hs hr => raf_subset_evaluate Q C hs hr⟩
  by_cases h : (evaluate Q C A).Nonempty
  · exact Or.inr ((isRAF_iff_nonempty_prune_eq Q C _).mpr ⟨h, evaluate_fixed Q C A⟩)
  · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp h)

theorem evaluate_mem_iff (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (A : Finset R) (r : R) :
    r ∈ evaluate Q C A ↔ ∃ S ⊆ A, IsRAF Q C S ∧ r ∈ S := by
  constructor
  · intro hr
    refine ⟨evaluate Q C A, evaluate_subset Q C A, ?_, hr⟩
    exact (isRAF_iff_nonempty_prune_eq Q C _).mpr ⟨⟨r, hr⟩, evaluate_fixed Q C A⟩
  · rintro ⟨S, hs, hraf, hr⟩
    exact raf_subset_evaluate Q C hs hraf hr

end RAFQueryCompilation

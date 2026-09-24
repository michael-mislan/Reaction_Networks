import proofs.RAFQueryCompilation.ResidualRAF

namespace RAFQueryCompilation
open RAF RAF.Frankl
variable {M R : Type*} [DecidableEq M] [Fintype M] [DecidableEq R]

/-- Exact maxRAF update after arbitrary availability changes inside a forward-closed
dependency region. Both deletions and restorations are allowed. -/
theorem evaluate_cone_update (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (A B E : Finset R)
    (hind : OutsideIndependent Q C E) (hab : A \ E = B \ E) :
    evaluate Q C B = (evaluate Q C A \ E) ∪
      evaluate (residualSource Q (evaluate Q C A \ E)) C (B ∩ E) := by
  have heq := outside_unchanged Q C hind hab
  apply evaluate_residual Q C B (evaluate Q C A \ E) (B ∩ E)
  · rw [evaluate_outside Q C hind A]
    exact evaluate_fixed Q C (A \ E)
  · rw [heq]
    exact Finset.sdiff_subset.trans (evaluate_subset Q C B)
  · exact Finset.inter_subset_left
  · intro r hr
    by_cases hre : r ∈ E
    · exact Finset.mem_union_right _
        (Finset.mem_inter.mpr ⟨evaluate_subset Q C B hr, hre⟩)
    · apply Finset.mem_union_left
      rw [heq]
      exact Finset.mem_sdiff.mpr ⟨hr, hre⟩

end RAFQueryCompilation

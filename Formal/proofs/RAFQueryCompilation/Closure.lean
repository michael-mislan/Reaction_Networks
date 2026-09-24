import proofs.RAFQueryCompilation.FiniteIteration
import proofs.RAF.Frankl.Semantics

namespace RAFQueryCompilation
open RAF RAF.Frankl

variable {M R : Type*} [DecidableEq M] [Fintype M]

def finiteClosure (Q : CRS M R) (S : Finset R) : Finset M :=
  settle (closureStep Q S) (Fintype.card M) Q.food

omit [Fintype M] in
theorem closureStep_inflationary (Q : CRS M R) (S : Finset R)
    (A : Finset M) : A ⊆ closureStep Q S A := Finset.subset_union_left

theorem finiteClosure_fixed (Q : CRS M R) (S : Finset R) :
    closureStep Q S (finiteClosure Q S) = finiteClosure Q S :=
  settle_grow_fixed _ (closureStep_inflationary Q S) _ _ (by omega)

theorem food_subset_finiteClosure (Q : CRS M R) (S : Finset R) :
    Q.food ⊆ finiteClosure Q S :=
  subset_settle _ (closureStep_inflationary Q S) _ _

theorem closureAt_subset_finiteClosure (Q : CRS M R) (S : Finset R) (k : ℕ) :
    closureAt Q S k ⊆ finiteClosure Q S := by
  induction k with
  | zero => exact food_subset_finiteClosure Q S
  | succ k ih =>
      have h := closureStep_mono Q (Finset.Subset.refl S) ih
      simpa [closureAt, finiteClosure_fixed] using h

omit [Fintype M] in
theorem closureAt_eq_iterate (Q : CRS M R) (S : Finset R) (k : ℕ) :
    closureAt Q S k = ((closureStep Q S)^[k]) Q.food := by
  induction k with
  | zero => rfl
  | succ k ih => simp [closureAt, Function.iterate_succ_apply', ih]

theorem finiteClosure_eq_some_stage (Q : CRS M R) (S : Finset R) :
    ∃ k, finiteClosure Q S = closureAt Q S k := by
  obtain ⟨k, hk⟩ := settle_eq_some_iterate (closureStep Q S) (Fintype.card M) Q.food
  exact ⟨k, hk.trans (closureAt_eq_iterate Q S k).symm⟩

theorem finiteClosure_mono (Q : CRS M R) {S T : Finset R} (h : S ⊆ T) :
    finiteClosure Q S ⊆ finiteClosure Q T := by
  obtain ⟨k, hk⟩ := finiteClosure_eq_some_stage Q S
  rw [hk]
  exact (closureAt_mono_reactions Q h k).trans (closureAt_subset_finiteClosure Q T k)

theorem supported_iff_finite (Q : CRS M R) (C : Catalysis M R)
    (S : Finset R) (r : R) :
    Supported Q C S r ↔ Q.inputs r ⊆ finiteClosure Q S ∧
      ∃ x ∈ finiteClosure Q S, C x r := by
  constructor
  · rintro ⟨⟨k, hk⟩, x, j, hx, hc⟩
    exact ⟨hk.trans (closureAt_subset_finiteClosure Q S k),
      x, closureAt_subset_finiteClosure Q S j hx, hc⟩
  · rintro ⟨hi, x, hx, hc⟩
    obtain ⟨k, hk⟩ := finiteClosure_eq_some_stage Q S
    rw [hk] at hi hx
    exact ⟨⟨k, hi⟩, x, k, hx, hc⟩

end RAFQueryCompilation

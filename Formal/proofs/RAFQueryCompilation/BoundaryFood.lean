import proofs.RAFQueryCompilation.ConeUpdate

namespace RAFQueryCompilation
open RAF RAF.Frankl
variable {M R : Type*} [DecidableEq M] [Fintype M] [DecidableEq R]

def withFood (Q : CRS M R) (F : Finset M) : CRS M R := { Q with food := F }

def Needed (Q : CRS M R) (C : Catalysis M R) (A : Finset R) (x : M) : Prop :=
  ∃ r ∈ A, x ∈ Q.inputs r ∨ C x r

omit [Fintype M] [DecidableEq R] in
theorem closureAt_food_agree (Q : CRS M R) (C : Catalysis M R)
    (F G : Finset M) (A S : Finset R) (hsa : S ⊆ A)
    (hfood : ∀ x, Needed Q C A x → (x ∈ F ↔ x ∈ G)) (k : ℕ) :
    ∀ x, Needed Q C A x →
      (x ∈ closureAt (withFood Q F) S k ↔ x ∈ closureAt (withFood Q G) S k) := by
  induction k with
  | zero => exact hfood
  | succ k ih =>
      intro x hx
      have hen : ∀ r ∈ S,
          Enabled (withFood Q F) (closureAt (withFood Q F) S k) r ↔
          Enabled (withFood Q G) (closureAt (withFood Q G) S k) r := by
        intro r hr
        constructor
        · intro he y hy
          exact (ih y ⟨r, hsa hr, Or.inl hy⟩).mp (he hy)
        · intro he y hy
          exact (ih y ⟨r, hsa hr, Or.inl hy⟩).mpr (he hy)
      simp only [closureAt, closureStep, Finset.mem_union, Finset.mem_biUnion]
      apply or_congr (ih x hx)
      apply exists_congr
      intro r
      apply and_congr_right
      intro hr
      by_cases hf : Enabled (withFood Q F) (closureAt (withFood Q F) S k) r
      · have hg := (hen r hr).mp hf
        simp only [if_pos hf, if_pos hg]
        rfl
      · have hg : ¬ Enabled (withFood Q G) (closureAt (withFood Q G) S k) r :=
          fun h => hf ((hen r hr).mpr h)
        simp only [if_neg hf, if_neg hg]

omit [Fintype M] [DecidableEq R] in
theorem supported_food_agree (Q : CRS M R) (C : Catalysis M R)
    (F G : Finset M) (A S : Finset R) (hsa : S ⊆ A)
    (hfood : ∀ x, Needed Q C A x → (x ∈ F ↔ x ∈ G)) {r : R} (hr : r ∈ S) :
    Supported (withFood Q F) C S r ↔ Supported (withFood Q G) C S r := by
  have hi : ∀ k, (Q.inputs r ⊆ closureAt (withFood Q F) S k) ↔
      (Q.inputs r ⊆ closureAt (withFood Q G) S k) := by
    intro k
    constructor
    · intro h x hx
      exact (closureAt_food_agree Q C F G A S hsa hfood k x
        ⟨r, hsa hr, Or.inl hx⟩).mp (h hx)
    · intro h x hx
      exact (closureAt_food_agree Q C F G A S hsa hfood k x
        ⟨r, hsa hr, Or.inl hx⟩).mpr (h hx)
  constructor
  · rintro ⟨⟨k, hk⟩, x, j, hx, hc⟩
    exact ⟨⟨k, (hi k).mp hk⟩, x, j,
      (closureAt_food_agree Q C F G A S hsa hfood j x
        ⟨r, hsa hr, Or.inr hc⟩).mp hx, hc⟩
  · rintro ⟨⟨k, hk⟩, x, j, hx, hc⟩
    exact ⟨⟨k, (hi k).mpr hk⟩, x, j,
      (closureAt_food_agree Q C F G A S hsa hfood j x
        ⟨r, hsa hr, Or.inr hc⟩).mpr hx, hc⟩

theorem evaluate_food_agree (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (F G : Finset M) (A : Finset R)
    (hfood : ∀ x, Needed Q C A x → (x ∈ F ↔ x ∈ G)) :
    evaluate (withFood Q F) C A = evaluate (withFood Q G) C A := by
  apply Finset.Subset.antisymm
  · apply supported_subset_evaluate _ C (evaluate_subset _ C A)
    intro r hr
    exact (supported_food_agree Q C F G A _ (evaluate_subset _ C A) hfood hr).mp
      (fixed_supported _ C (evaluate_fixed _ C A) r hr)
  · apply supported_subset_evaluate _ C (evaluate_subset _ C A)
    intro r hr
    exact (supported_food_agree Q C F G A _ (evaluate_subset _ C A) hfood hr).mpr
      (fixed_supported _ C (evaluate_fixed _ C A) r hr)

end RAFQueryCompilation

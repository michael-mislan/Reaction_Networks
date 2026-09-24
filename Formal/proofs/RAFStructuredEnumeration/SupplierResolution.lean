import proofs.RAFQueryCompilation.Closure

namespace RAFStructuredEnumeration
open RAF RAF.Frankl RAFQueryCompilation
variable {M R : Type*} [DecidableEq M] [DecidableEq R]

/-- Product thinning preserves all reaction identifiers, inputs and food. -/
def thin (Q : CRS M R) (p : M → Option R) : CRS M R where
  inputs := Q.inputs
  food := Q.food
  outputs r := (Q.outputs r).filter (fun x => x ∈ Q.food ∨ p x = some r)

theorem thin_closure_subset (Q : CRS M R) (p : M → Option R)
    (S : Finset R) (k : ℕ) : closureAt (thin Q p) S k ⊆ closureAt Q S k := by
  induction k with
  | zero => exact Finset.Subset.rfl
  | succ k ih =>
    intro x hx
    simp only [closureAt, closureStep, Finset.mem_union, Finset.mem_biUnion] at hx ⊢
    rcases hx with hx | ⟨r, hr, hx⟩
    · exact Or.inl (ih hx)
    · right
      refine ⟨r, hr, ?_⟩
      by_cases he : Enabled (thin Q p) (closureAt (thin Q p) S k) r
      · have hi : Enabled Q (closureAt Q S k) r := fun y hy => ih (he hy)
        have hot : x ∈ (thin Q p).outputs r := by simpa only [if_pos he] using hx
        have ho : x ∈ Q.outputs r := (Finset.mem_filter.mp hot).1
        simpa [hi] using ho
      · simp [he] at hx

theorem thin_raf_sound (Q : CRS M R) (C D : Catalysis M R)
    (p : M → Option R) (hC : ∀ x r, D x r → C x r) (S : Finset R)
    (h : IsRAF (thin Q p) D S) : IsRAF Q C S := by
  refine ⟨h.1, ?_, ?_⟩
  · intro r hr
    obtain ⟨k, hk⟩ := h.2.1 r hr
    exact ⟨k, hk.trans (thin_closure_subset Q p S k)⟩
  · intro r hr
    obtain ⟨x, k, hx, hc⟩ := h.2.2 r hr
    exact ⟨x, k, thin_closure_subset Q p S k hx, hC x r hc⟩

omit [DecidableEq R] in
theorem closureAt_mono_stage (Q : CRS M R) (S : Finset R) :
    Monotone (closureAt Q S) := by
  apply monotone_nat_of_le_succ
  intro k
  exact Finset.subset_union_left

omit [DecidableEq R] in
/-- A single producer works at every stage at which a nonfood molecule is available. -/
theorem earliest_producer (Q : CRS M R) (S : Finset R) (x : M)
    (hn : x ∉ Q.food) (hg : ∃ k, x ∈ closureAt Q S k) :
    ∃ r ∈ S, x ∈ Q.outputs r ∧
      ∀ k, x ∈ closureAt Q S (k + 1) → Q.inputs r ⊆ closureAt Q S k := by
  classical
  let n := Nat.find hg
  have hn0 : n ≠ 0 := by
    intro he
    have hx := Nat.find_spec hg
    rw [show Nat.find hg = 0 from he] at hx
    exact hn hx
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hx : x ∈ closureAt Q S (j + 1) := by
    have hx := Nat.find_spec hg
    change x ∈ closureAt Q S n at hx
    rw [hj] at hx
    exact hx
  have hold : x ∉ closureAt Q S j := Nat.find_min hg (by omega)
  simp only [closureAt, closureStep, Finset.mem_union, Finset.mem_biUnion] at hx
  rcases hx with hx | ⟨r, hr, hx⟩
  · exact False.elim (hold hx)
  · by_cases he : Enabled Q (closureAt Q S j) r
    · refine ⟨r, hr, by simpa [he] using hx, ?_⟩
      intro k hk
      have hle : n ≤ k + 1 := Nat.find_min' hg hk
      exact he.trans (closureAt_mono_stage Q S (by omega))
    · simp [he] at hx

/-- Outside the generated nonfood molecules an arbitrary fallback is retained. -/
noncomputable def earliestChoice (Q : CRS M R) (S : Finset R)
    (fallback : M → Option R) (x : M) : Option R := by
  classical
  exact if h : x ∉ Q.food ∧ ∃ k, x ∈ closureAt Q S k then
    some (earliest_producer Q S x h.1 h.2).choose else fallback x

omit [DecidableEq R] in
theorem earliestChoice_spec (Q : CRS M R) (S : Finset R)
    (fallback : M → Option R) (x : M) (hn : x ∉ Q.food)
    (hg : ∃ k, x ∈ closureAt Q S k) :
    ∃ r ∈ S, earliestChoice Q S fallback x = some r ∧ x ∈ Q.outputs r ∧
      ∀ k, x ∈ closureAt Q S (k + 1) → Q.inputs r ⊆ closureAt Q S k := by
  classical
  have h := (earliest_producer Q S x hn hg).choose_spec
  exact ⟨_, h.1, by simp [earliestChoice, hn, hg], h.2⟩

theorem earliestChoice_closure (Q : CRS M R) (S : Finset R)
    (fallback : M → Option R) (k : ℕ) :
    closureAt (thin Q (earliestChoice Q S fallback)) S k = closureAt Q S k := by
  apply Finset.Subset.antisymm (thin_closure_subset _ _ _ _)
  induction k with
  | zero => exact Finset.Subset.rfl
  | succ k ih =>
    intro x hx
    by_cases hf : x ∈ Q.food
    · exact closureAt_mono_stage (thin Q (earliestChoice Q S fallback)) S
        (Nat.zero_le (k + 1)) hf
    · obtain ⟨r, hr, hp, ho, hi⟩ := earliestChoice_spec Q S fallback x hf ⟨k+1, hx⟩
      have he : Enabled (thin Q (earliestChoice Q S fallback))
          (closureAt (thin Q (earliestChoice Q S fallback)) S k) r :=
        (hi k hx).trans ih
      simp only [closureAt, closureStep, Finset.mem_union, Finset.mem_biUnion]
      right
      refine ⟨r, hr, ?_⟩
      rw [if_pos he]
      exact Finset.mem_filter.mpr ⟨ho, Or.inr hp⟩

end RAFStructuredEnumeration

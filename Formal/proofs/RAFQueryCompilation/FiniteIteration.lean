import Mathlib

namespace RAFQueryCompilation

variable {α : Type*} [DecidableEq α]

/-- Stop at a fixed point or after the supplied finite fuel. -/
def settle (f : Finset α → Finset α) : ℕ → Finset α → Finset α
  | 0, S => S
  | n + 1, S => if f S = S then S else settle f n (f S)

theorem settle_shrink_fixed (f : Finset α → Finset α)
    (hf : ∀ S, f S ⊆ S) (n : ℕ) (S : Finset α) (hn : S.card ≤ n) :
    f (settle f n S) = settle f n S := by
  induction n generalizing S with
  | zero =>
      have hz : S = ∅ := Finset.card_eq_zero.mp (by omega)
      subst S
      exact Finset.eq_empty_iff_forall_notMem.mpr (by
        intro x hx
        exact Finset.notMem_empty x (hf ∅ hx))
  | succ n ih =>
      by_cases h : f S = S
      · simp [settle, h]
      · have hlt := Finset.card_lt_card
          (Finset.ssubset_iff_subset_ne.mpr ⟨hf S, h⟩)
        simpa [settle, h] using ih (f S) (by omega)

theorem settle_grow_fixed [Fintype α] (f : Finset α → Finset α)
    (hf : ∀ S, S ⊆ f S) (n : ℕ) (S : Finset α)
    (hn : Fintype.card α ≤ S.card + n) :
    f (settle f n S) = settle f n S := by
  induction n generalizing S with
  | zero =>
      have hc := Finset.card_le_univ (f S)
      have he : f S = S :=
        (Finset.eq_of_subset_of_card_le (hf S) (by omega)).symm
      exact he
  | succ n ih =>
      by_cases h : f S = S
      · simp [settle, h]
      · have hne : S ≠ f S := Ne.symm h
        have hlt := Finset.card_lt_card
          (Finset.ssubset_iff_subset_ne.mpr ⟨hf S, hne⟩)
        simpa [settle, h] using ih (f S) (by omega)

theorem settle_subset (f : Finset α → Finset α) (hf : ∀ S, f S ⊆ S)
    (n : ℕ) (S : Finset α) : settle f n S ⊆ S := by
  induction n generalizing S with
  | zero => exact Finset.Subset.refl _
  | succ n ih =>
      by_cases h : f S = S
      · simp [settle, h]
      · simpa [settle, h] using (ih (f S)).trans (hf S)

theorem subset_settle (f : Finset α → Finset α) (hf : ∀ S, S ⊆ f S)
    (n : ℕ) (S : Finset α) : S ⊆ settle f n S := by
  induction n generalizing S with
  | zero => exact Finset.Subset.refl _
  | succ n ih =>
      by_cases h : f S = S
      · simp [settle, h]
      · simpa [settle, h] using (hf S).trans (ih (f S))

theorem settle_le_closed (f : Finset α → Finset α) (hm : Monotone f)
    (n : ℕ) (S B : Finset α) (hs : S ⊆ B) (hb : f B ⊆ B) :
    settle f n S ⊆ B := by
  induction n generalizing S with
  | zero => exact hs
  | succ n ih =>
      by_cases h : f S = S
      · simpa [settle, h] using hs
      · simpa [settle, h] using ih (f S) ((hm hs).trans hb)

theorem fixed_subset_settle (f : Finset α → Finset α) (hm : Monotone f)
    (n : ℕ) (S B : Finset α) (hs : B ⊆ S) (hb : f B = B) :
    B ⊆ settle f n S := by
  induction n generalizing S with
  | zero => exact hs
  | succ n ih =>
      by_cases h : f S = S
      · simpa [settle, h] using hs
      · have hx : B ⊆ f S := by rw [← hb]; exact hm hs
        simpa [settle, h] using ih (f S) hx

theorem settle_eq_some_iterate (f : Finset α → Finset α) (n : ℕ)
    (S : Finset α) : ∃ k, settle f n S = (f^[k]) S := by
  induction n generalizing S with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
      by_cases h : f S = S
      · exact ⟨0, by simp [settle, h]⟩
      · obtain ⟨k, hk⟩ := ih (f S)
        exact ⟨k + 1, by simpa [settle, h, Function.iterate_succ_apply] using hk⟩

end RAFQueryCompilation

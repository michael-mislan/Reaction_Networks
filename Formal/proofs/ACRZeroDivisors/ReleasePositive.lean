import proofs.ACRZeroDivisors.TriangularRelease
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp

namespace ACRZeroDivisors

theorem triangular_zero_iff {A : Type*} [CommRing A] {n : ℕ} (E : Fin (n+1) → A) :
    (∀ j, triangularDifferences E j = 0) ↔ ∀ j, E j = 0 := by
  constructor
  · intro h j
    induction j using Fin.induction with
    | zero => exact h 0
    | succ j hj =>
        have hh := h j.succ
        simpa [triangularDifferences,hj] using hh
  · intro h j
    refine Fin.cases (h 0) (fun i => ?_) j
    simp [triangularDifferences,h]

theorem release_steady_iff {σ : Type*} {n : ℕ}
    (f : σ → ℝ) (F : ℝ) (rates y : Fin (n+1) → ℝ)
    (hr : ∀ j, rates j ≠ 0) (w : σ → Fin (n+1) → ℝ) :
    ((∀ i, f i - ∑ j, w i j * (F-rates j*y j) = 0) ∧
      ∀ j, triangularDifferences (fun j => F-rates j*y j) j = 0) ↔
    (∀ i, f i = 0) ∧ ∀ j, y j = F / rates j := by
  rw [triangular_zero_iff]
  constructor
  · rintro ⟨hf,he⟩
    refine ⟨?_,?_⟩
    · intro i
      simpa only [he,mul_zero,Finset.sum_const_zero,sub_zero] using hf i
    · intro j
      apply (eq_div_iff (hr j)).mpr
      have h := sub_eq_zero.mp (he j)
      simpa only [mul_comm] using h.symm
  · rintro ⟨hf,hy⟩
    have he : ∀ j, F-rates j*y j=0 := by
      intro j
      rw [hy j,mul_div_cancel₀ F (hr j),sub_self]
    exact ⟨fun i => by simp only [he,mul_zero,Finset.sum_const_zero,sub_zero,hf],he⟩

/-- Unique positive intermediate reconstruction at each positive-flux old state. -/
theorem release_unique_positive {σ : Type*} {n : ℕ}
    (f : σ → ℝ) (F : ℝ) (hF : 0 < F) (rates : Fin (n+1) → ℝ)
    (hr : ∀ j, 0 < rates j) (w : σ → Fin (n+1) → ℝ) (hf : ∀ i, f i = 0) :
    ∃! y : Fin (n+1) → ℝ, (∀ j, 0 < y j) ∧
      (∀ i, f i - ∑ j, w i j * (F-rates j*y j) = 0) ∧
      ∀ j, triangularDifferences (fun j => F-rates j*y j) j = 0 := by
  refine ⟨fun j => F/rates j,?_,?_⟩
  · exact ⟨fun j => div_pos hF (hr j),
      (release_steady_iff f F rates _ (fun j => ne_of_gt (hr j)) w).mpr ⟨hf,fun _ => rfl⟩⟩
  · intro y hy
    funext j
    exact ((release_steady_iff f F rates y (fun j => ne_of_gt (hr j)) w).mp hy.2).2 j

end ACRZeroDivisors

import Mathlib

namespace FutileCycle
open Matrix

def SignedIncidence {I J : Type*} (A : Matrix I J ℤ) : Prop :=
  (∀ i j, A i j = 0 ∨ A i j = 1 ∨ A i j = -1) ∧
  (∀ j i k, A i j = 1 → A k j = 1 → i = k) ∧
  (∀ j i k, A i j = -1 → A k j = -1 → i = k)

theorem SignedIncidence.submatrix {I J K L : Type*} {A : Matrix I J ℤ}
    (h : SignedIncidence A) (f : K → I) (g : L → J) (hf : Function.Injective f) :
    SignedIncidence (A.submatrix f g) := by
  exact ⟨fun i j => h.1 (f i) (g j),
    fun j i k hi hk => hf (h.2.1 (g j) (f i) (f k) hi hk),
    fun j i k hi hk => hf (h.2.2 (g j) (f i) (f k) hi hk)⟩

theorem incidence_column_sum {I J : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I J ℤ} (h : SignedIncidence A) (j : J)
    (a b : I) (ha : A a j = 1) (hb : A b j = -1) : ∑ i, A i j = 0 := by
  have hab : a ≠ b := by intro e; subst b; omega
  have heq : ∀ i, A i j = (if i = a then 1 else 0) - (if i = b then 1 else 0) := by
    intro i
    by_cases hia : i = a
    · subst i; simp [ha, hab]
    by_cases hib : i = b
    · subst i; simp [hb, Ne.symm hab]
    rcases h.1 i j with hi | hi | hi
    · simp [hi, hia, hib]
    · exact False.elim (hia (h.2.1 j i a hi ha))
    · exact False.elim (hib (h.2.2 j i b hi hb))
  simp_rw [heq, Finset.sum_sub_distrib]
  simp

theorem incidence_det_bound (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (h : SignedIncidence A) : A.det = 0 ∨ A.det = 1 ∨ A.det = -1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hs : ∃ j i, ∀ k, k ≠ i → A k j = 0
    · obtain ⟨j, i, hs⟩ := hs
      have hd := Matrix.det_succ_column A j
      rw [Fintype.sum_eq_single i] at hd
      · have hm := ih (A.submatrix i.succAbove j.succAbove)
          (h.submatrix _ _ Fin.succAbove_right_injective)
        have he := h.1 i j
        have hp : (-1 : ℤ) ^ (i.val + j.val) = 1 ∨
            (-1 : ℤ) ^ (i.val + j.val) = -1 := by
          exact neg_one_pow_eq_or ℤ _
        rcases hm with hm | hm | hm <;> rcases he with he | he | he <;>
          rcases hp with hp | hp <;> simp_all
      · intro k hk
        simp [hs k hk]
    · have hz : ∀ j, ∑ i, A i j = 0 := by
        intro j
        have hn : ∀ i, ∃ k, k ≠ i ∧ A k j ≠ 0 := by
          intro i
          have := not_exists.mp (not_exists.mp hs j) i
          push Not at this
          exact this
        obtain ⟨a, _, ha⟩ := hn 0
        obtain ⟨b, hba, hb⟩ := hn a
        rcases h.1 a j with ha0 | ha1 | ham
        · exact False.elim (ha ha0)
        · rcases h.1 b j with hb0 | hb1 | hbm
          · exact False.elim (hb hb0)
          · exact False.elim (hba (h.2.1 j b a hb1 ha1))
          · exact incidence_column_sum h j a b ha1 hbm
        · rcases h.1 b j with hb0 | hb1 | hbm
          · exact False.elim (hb hb0)
          · exact incidence_column_sum h j b a hb1 ham
          · exact False.elim (hba (h.2.2 j b a hbm ham))
      left
      by_contra hd
      have hv : (fun _ : Fin (n+1) => (1 : ℤ)) ᵥ* A = 0 := by
        ext j
        simpa [Matrix.vecMul, dotProduct] using hz j
      have he := Matrix.eq_zero_of_vecMul_eq_zero hd hv
      have := congrFun he 0
      norm_num at this

end FutileCycle

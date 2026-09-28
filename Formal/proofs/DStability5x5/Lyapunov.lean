import proofs.DUnstableCores.DScaling

/-!
# Diagonal Lyapunov stability implies D-stability

If `p` is a strictly positive weight vector such that the symmetric matrix
`diag(p) A + Aᵀ diag(p)` is negative definite, then `A` is D-stable for right scaling:
every `A · diag(d)` with `d > 0` has all eigenvalues in the open left half-plane.

Proof.  Let `(A · diag d) v = λ v` with `v ≠ 0`, and put `x = diag(d) Re v`,
`y = diag(d) Im v`.  Taking real and imaginary parts, `A x = a Re v - b Im v` and
`A y = a Im v + b Re v` where `λ = a + b i`.  Hence

  `xᵀ (diag(p) A + Aᵀ diag(p)) x + yᵀ (diag(p) A + Aᵀ diag(p)) y
      = 2 a ∑ᵢ pᵢ dᵢ |vᵢ|²`.

The left side is negative because `(x, y) ≠ 0`, and the weighted sum is positive, so `a < 0`.
-/

open Finset

namespace DStability5x5

open DUnstableCores

/-- The symmetrised quadratic form `xᵀ (diag(p) A + Aᵀ diag(p)) x` equals
`2 ∑ᵢ pᵢ xᵢ (A x)ᵢ`. -/
theorem diagLyapunov_form_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (p x : Fin n → ℝ) :
    ∑ i, ∑ j, x i * (p i * A i j + A j i * p j) * x j
      = 2 * ∑ i, p i * x i * ∑ j, A i j * x j := by
  have h1 : ∑ i, ∑ j, x i * (p i * A i j + A j i * p j) * x j
      = ∑ i, ∑ j, p i * x i * (A i j * x j) + ∑ i, ∑ j, x i * A j i * p j * x j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h2 : ∑ i, ∑ j, x i * A j i * p j * x j = ∑ i, ∑ j, p i * x i * (A i j * x j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h3 : ∑ i, ∑ j, p i * x i * (A i j * x j) = ∑ i, p i * x i * ∑ j, A i j * x j := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  rw [h1, h2, h3]
  ring

/-- Under the Lyapunov hypothesis the quadratic form is nonpositive everywhere. -/
theorem diagLyapunov_form_nonpos {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (p : Fin n → ℝ)
    (hQ : ∀ x : Fin n → ℝ, x ≠ 0 → ∑ i, ∑ j, x i * (p i * A i j + A j i * p j) * x j < 0)
    (x : Fin n → ℝ) : ∑ i, ∑ j, x i * (p i * A i j + A j i * p j) * x j ≤ 0 := by
  by_cases hx : x = 0
  · subst hx
    simp
  · exact (hQ x hx).le

/-- **Diagonal Lyapunov criterion.**  If `diag(p) A + Aᵀ diag(p)` is negative definite for a
strictly positive `p`, then `A` is D-stable (for right diagonal scaling). -/
theorem dStable_of_diagLyapunov {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i)
    (hQ : ∀ x : Fin n → ℝ, x ≠ 0 → ∑ i, ∑ j, x i * (p i * A i j + A j i * p j) * x j < 0) :
    DStable A := by
  intro d hd lam v heig
  obtain ⟨hv, hev⟩ := heig
  obtain ⟨x, hx⟩ : ∃ x : Fin n → ℝ, ∀ j, x j = d j * (v j).re := ⟨_, fun _ => rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : Fin n → ℝ, ∀ j, y j = d j * (v j).im := ⟨_, fun _ => rfl⟩
  have hsum : ∀ i, ∑ j, ((A i j * d j : ℝ) : ℂ) * v j = lam * v i := by
    intro i
    have h := hev i
    simp only [Matrix.mulVec, dotProduct, complexify, rightScale] at h
    exact h
  have hre : ∀ i, ∑ j, A i j * x j = lam.re * (v i).re - lam.im * (v i).im := by
    intro i
    have h := congrArg Complex.re (hsum i)
    rw [Complex.re_sum, Complex.mul_re] at h
    simp only [Complex.re_ofReal_mul] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro j _
    rw [hx]
    ring
  have him : ∀ i, ∑ j, A i j * y j = lam.re * (v i).im + lam.im * (v i).re := by
    intro i
    have h := congrArg Complex.im (hsum i)
    rw [Complex.im_sum, Complex.mul_im] at h
    simp only [Complex.im_ofReal_mul] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro j _
    rw [hy]
    ring
  -- the weighted energy identity
  have hS : (∑ i, p i * x i * ∑ j, A i j * x j) + (∑ i, p i * y i * ∑ j, A i j * y j)
      = lam.re * ∑ i, p i * d i * ((v i).re ^ 2 + (v i).im ^ 2) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hre i, him i, hx i, hy i]
    ring
  -- a nonzero coordinate
  obtain ⟨i0, hi0⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  have hri : (v i0).re ≠ 0 ∨ (v i0).im ≠ 0 := by
    by_contra h
    push Not at h
    apply hi0
    apply Complex.ext
    · simp [h.1]
    · simp [h.2]
  have hW : 0 < ∑ i, p i * d i * ((v i).re ^ 2 + (v i).im ^ 2) := by
    apply Finset.sum_pos'
    · intro i _
      have := hp i
      have := hd i
      positivity
    · refine ⟨i0, Finset.mem_univ _, ?_⟩
      have hpos : 0 < (v i0).re ^ 2 + (v i0).im ^ 2 := by
        rcases hri with h | h
        · have := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h))
          nlinarith [sq_nonneg (v i0).im]
        · have := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h))
          nlinarith [sq_nonneg (v i0).re]
      exact mul_pos (mul_pos (hp i0) (hd i0)) hpos
  -- the quadratic forms
  have hqx := diagLyapunov_form_eq A p x
  have hqy := diagLyapunov_form_eq A p y
  have hqx0 := diagLyapunov_form_nonpos A p hQ x
  have hqy0 := diagLyapunov_form_nonpos A p hQ y
  have hstrict : ∑ i, ∑ j, x i * (p i * A i j + A j i * p j) * x j
      + ∑ i, ∑ j, y i * (p i * A i j + A j i * p j) * y j < 0 := by
    rcases hri with h | h
    · have hxne : x ≠ 0 := by
        intro hx0
        have h1 : x i0 = 0 := by rw [hx0]; rfl
        rw [hx i0] at h1
        rcases mul_eq_zero.mp h1 with h2 | h2
        · exact (hd i0).ne' h2
        · exact h h2
      have := hQ x hxne
      linarith
    · have hyne : y ≠ 0 := by
        intro hy0
        have h1 : y i0 = 0 := by rw [hy0]; rfl
        rw [hy i0] at h1
        rcases mul_eq_zero.mp h1 with h2 | h2
        · exact (hd i0).ne' h2
        · exact h h2
      have := hQ y hyne
      linarith
  have hneg : lam.re * ∑ i, p i * d i * ((v i).re ^ 2 + (v i).im ^ 2) < 0 := by
    rw [← hS]
    linarith
  by_contra hc
  have hc' : 0 ≤ lam.re := not_lt.mp hc
  have := mul_nonneg hc' hW.le
  linarith

end DStability5x5

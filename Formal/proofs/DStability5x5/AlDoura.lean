import proofs.DStability5x5.Lyapunov

/-!
# D-stability of the Al-Doura refinery-column matrix

`M = -G⁺(0)` for the 4×4 Al-Doura column model.  With the positive weight
`p = (2/5, 2/5, 81/10, 4/5)` the symmetric matrix `Q = -(diag(p) M + Mᵀ diag(p))` is positive
definite; an exact rational `L D Lᵀ` factorisation (unit lower-triangular `L`, positive
diagonal `D`) gives

  `xᵀ (diag(p) M + Mᵀ diag(p)) x = -(∑ₖ Dₖ (∑ᵢ Lᵢₖ xᵢ)²)`,

which is negative for `x ≠ 0` because the linear forms are triangular.  The diagonal
Lyapunov criterion `dStable_of_diagLyapunov` then gives D-stability.
-/

noncomputable section

open Finset

namespace DStability5x5

open DUnstableCores

/-- `M = -G⁺(0)` for the Al-Doura refinery column. -/
def alDouraM : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-23, -13/25, -1413/100, -53/100;
     -57/20, -42/25, -89/10, -14/25;
     141/50, 9/50, -13, -6/25;
     -31/10, -27/200, 71/5, -9/10]

/-- The diagonal Lyapunov weight. -/
def alDouraP : Fin 4 → ℝ := ![2/5, 2/5, 81/10, 4/5]

theorem alDouraP_pos : ∀ i, 0 < alDouraP i := by
  intro i
  fin_cases i <;> simp [alDouraP]

/-- Exact `L D Lᵀ` identity for the symmetrised Lyapunov form. -/
theorem alDoura_form_eq (x : Fin 4 → ℝ) :
    ∑ i, ∑ j, x i * (alDouraP i * alDouraM i j + alDouraM j i * alDouraP j) * x j
      = -(92/5 * (x 0 + 337/4600 * x 1 - 1719/1840 * x 2 + 673/4600 * x 3) ^ 2
          + 1432031/1150000 * (x 1 + 7731115/2864062 * x 2 + 154999/1432031 * x 3) ^ 2
          + 26559441707/143203100 * (x 2 - 5201746482/132797208535 * x 3) ^ 2
          + 12399801384084/16599651066875 * x 3 ^ 2) := by
  simp [Fin.sum_univ_four, alDouraM, alDouraP]
  ring

theorem alDoura_form_neg (x : Fin 4 → ℝ) (hx : x ≠ 0) :
    ∑ i, ∑ j, x i * (alDouraP i * alDouraM i j + alDouraM j i * alDouraP j) * x j < 0 := by
  rw [alDoura_form_eq]
  obtain ⟨y0, hy0⟩ : ∃ y : ℝ, y = x 0 + 337/4600 * x 1 - 1719/1840 * x 2 + 673/4600 * x 3 :=
    ⟨_, rfl⟩
  obtain ⟨y1, hy1⟩ : ∃ y : ℝ, y = x 1 + 7731115/2864062 * x 2 + 154999/1432031 * x 3 :=
    ⟨_, rfl⟩
  obtain ⟨y2, hy2⟩ : ∃ y : ℝ, y = x 2 - 5201746482/132797208535 * x 3 := ⟨_, rfl⟩
  rw [← hy0, ← hy1, ← hy2]
  have s0 := sq_nonneg y0
  have s1 := sq_nonneg y1
  have s2 := sq_nonneg y2
  have s3 := sq_nonneg (x 3)
  by_contra hc
  have hc' := not_lt.mp hc
  have z3 : x 3 ^ 2 = 0 := by linarith
  have z2 : y2 ^ 2 = 0 := by linarith
  have z1 : y1 ^ 2 = 0 := by linarith
  have z0 : y0 ^ 2 = 0 := by linarith
  rw [pow_eq_zero_iff two_ne_zero] at z0 z1 z2 z3
  apply hx
  funext k
  fin_cases k <;> simp <;> linarith

theorem alDouraM_dStable : DStable alDouraM :=
  dStable_of_diagLyapunov alDouraM alDouraP alDouraP_pos alDoura_form_neg

/-- **The Al-Doura column matrix `M = -G⁺(0)` is D-stable.** -/
theorem alDoura_dStable :
    DStable (!![-23, -13/25, -1413/100, -53/100;
                -57/20, -42/25, -89/10, -14/25;
                141/50, 9/50, -13, -6/25;
                -31/10, -27/200, 71/5, -9/10] : Matrix (Fin 4) (Fin 4) ℝ) :=
  alDouraM_dStable

end DStability5x5

end

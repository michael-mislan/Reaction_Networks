import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace ACRZeroDivisors

theorem reactor_characteristic (D ell delta p q k3 z : ℝ) :
    Matrix.det !![z+D+ell+p+q, D+k3, D-delta;
                  -p, z, 0; -q, -k3, z+delta] =
    z^3+(D+ell+delta+p+q)*z^2+
      (delta*(D+ell)+p*(delta+k3+D)+D*q)*z+D*p*(delta+k3) := by
  rw [Matrix.det_fin_three]
  simp
  ring

theorem reactor_hurwitz (D ell delta p q k3 : ℝ)
    (hD : 0 < D) (hl : 0 ≤ ell) (hd : 0 < delta)
    (hp : 0 < p) (hq : 0 < q) (hk : 0 < k3) :
    0 < D+ell+delta+p+q ∧
    0 < delta*(D+ell)+p*(delta+k3+D)+D*q ∧
    0 < D*p*(delta+k3) ∧
    D*p*(delta+k3) <
      (D+ell+delta+p+q)*(delta*(D+ell)+p*(delta+k3+D)+D*q) := by
  have h1 : D < D+ell+delta+p+q := by linarith
  have h2 : p*(delta+k3) < delta*(D+ell)+p*(delta+k3+D)+D*q := by nlinarith [mul_pos hd hD, mul_nonneg hd.le hl, mul_pos hp hD, mul_pos hD hq]
  have ht : 0 < p*(delta+k3) := by positivity
  refine ⟨by positivity, by positivity, by positivity, ?_⟩
  have := mul_lt_mul h1 h2.le ht (by positivity : 0 ≤ D+ell+delta+p+q)
  nlinarith

end ACRZeroDivisors

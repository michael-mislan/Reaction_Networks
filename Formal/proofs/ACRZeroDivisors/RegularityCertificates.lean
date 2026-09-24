import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace ACRZeroDivisors

/-- Jacobian minor of `(f₁,f₃,f₅,f₆,f₇)` of the EnvZ/OmpR field in the columns
`(x₁,x₃,x₅,x₆,x₇)`. Entries are the literal partial derivatives. -/
def envZMinor (k1 k4 k5 k6 k7 k8 k9 x2 x4 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![-k1, 0, 0, k6, 0;
     0, -(k4*x4), 0, k5, 0;
     0, 0, -(k7*x2), k6, k8;
     0, k4*x4, 0, -(k5+k6), 0;
     0, 0, k7*x2, 0, -(k8+k9)]

theorem envZ_regular_minor (k1 k4 k5 k6 k7 k8 k9 x2 x4 : ℝ) :
    (envZMinor k1 k4 k5 k6 k7 k8 k9 x2 x4).det = -(k1*k4*k6*k7*k9*x2*x4) := by
  simp [envZMinor, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

theorem envZ_regular_minor_ne_zero (k1 k4 k5 k6 k7 k8 k9 x2 x4 : ℝ)
    (h1 : 0 < k1) (h4 : 0 < k4) (h6 : 0 < k6) (h7 : 0 < k7) (h9 : 0 < k9)
    (hx2 : 0 < x2) (hx4 : 0 < x4) :
    (envZMinor k1 k4 k5 k6 k7 k8 k9 x2 x4).det ≠ 0 := by
  rw [envZ_regular_minor]
  have : 0 < k1*k4*k6*k7*k9*x2*x4 := by positivity
  linarith

/-- Nominal loaded-reactor Jacobian (µM, min) at `ℓ = 1/50`. -/
def reactorJ : Matrix (Fin 3) (Fin 3) ℚ :=
  !![-1/5, -3/50, 1/25; 17/200, 0, 0; 17/200, 1/20, -1/20]

/-- Solution of the Lyapunov equation `Jᵀ P + P J = -1`. -/
def reactorP : Matrix (Fin 3) (Fin 3) ℚ :=
  !![95/4, 4075/142, 3025/142;
     4075/142, 57115/1207, 1735/71;
     3025/142, 1735/71, 1920/71]

theorem reactor_lyapunov :
    reactorJ.transpose * reactorP + reactorP * reactorJ = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reactorJ, reactorP, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num

theorem reactor_lyapunov_minors :
    (0 : ℚ) < 95/4 ∧
    (0 : ℚ) < (95/4)*(57115/1207) - (4075/142)*(4075/142) ∧
    reactorP.det = 401489125/171394 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [Matrix.det_fin_three]
  simp [reactorP]
  norm_num

def reactorPinv : Matrix (Fin 3) (Fin 3) ℚ :=
  !![4678958/16059565, -350285/3211913, -420646/3211913;
     -350285/3211913, 2583847/32119130, 212262/16059565;
     -420646/3211913, 212262/16059565, 2058901/16059565]

theorem reactor_P_inverse : reactorP * reactorPinv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reactorP, reactorPinv, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num

/-- The cubic term of `dV/dt`: with `R(u) = (1/20) u_a (-(u_b+u_c), u_b, u_c)`,
`(P u)·R(u) = (1/20) u_a · uᵀ M u` for the displayed symmetric `M`. -/
theorem reactor_cubic_form (ua ub uc : ℝ) :
    ((95/4)*ua + (4075/142)*ub + (3025/142)*uc) * (-(1/20)*ua*(ub+uc)) +
    ((4075/142)*ua + (57115/1207)*ub + (1735/71)*uc) * ((1/20)*ua*ub) +
    ((3025/142)*ua + (1735/71)*ub + (1920/71)*uc) * ((1/20)*ua*uc) =
    (1/20)*ua*(2*(1405/568)*ua*ub - 2*(695/568)*ua*uc + (44955/2414)*ub^2
      - 2*(40/71)*ub*uc + (815/142)*uc^2) := by
  ring

/-- Frobenius bound `‖M‖_F² < 400` and the three diagonal entries of `P⁻¹`. -/
theorem reactor_ellipsoid_constants :
    (2*(1405/568 : ℚ)^2 + 2*(695/568)^2 + (44955/2414)^2 + 2*(40/71)^2 + (815/142)^2 < 400) ∧
    ((4678958/16059565 : ℚ) * (1/5) < 1/16) ∧
    ((2583847/32119130 : ℚ) * (1/5) < (127/1000)^2) ∧
    ((2058901/16059565 : ℚ) * (1/5) < (161/1000)^2) := by
  norm_num

end ACRZeroDivisors

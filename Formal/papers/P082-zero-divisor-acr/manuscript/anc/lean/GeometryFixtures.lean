import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace ACRZeroDivisors

/-- The (a,b) Jacobian minor of (b(a-2),c(a-3)+b) at (2,1,1). -/
theorem necessity_regular_minor : Matrix.det (!![1,0;1,1] : Matrix (Fin 2) (Fin 2) ℝ)=1 := by
  norm_num [Matrix.det_fin_two]

/-- The (t,u) minor of (v-tu,u-tv) at (1,1,1). -/
theorem order_regular_minor : Matrix.det (!![-1,-1;-1,1] : Matrix (Fin 2) (Fin 2) ℝ) = -2 := by
  norm_num [Matrix.det_fin_two]

theorem reactor_interval_floor : (147/100 : ℝ) < 15415907/10428000 := by norm_num

theorem three_stage_yield : ((100/101 : ℝ)^3) = 1000000/1030301 := by norm_num

end ACRZeroDivisors

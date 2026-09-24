import Mathlib

namespace CompositionalMemory

/-- A local exponential estimate inside a recovery region and nonpositive
drift outside it give a global generator ceiling. -/
theorem exponential_generator_envelope (g E a α N lam r K C F : ℝ)
    (hα : 0 ≤ α) (hN : 0 < N) (hlam : 0 < lam) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hraw : g ≤ α*(-lam*N*r^2/2+K+α*C/N+N*F^2/lam)*Real.exp (α*N*E))
    (houter : a ≤ E → g ≤ 0) :
    g ≤ α*(K+α*C/N+N*F^2/lam)*Real.exp (α*N*a) := by
  have hcoef : 0 ≤ α*(K+α*C/N+N*F^2/lam) := by positivity
  by_cases he : E ≤ a
  · have hdrop : α*(-lam*N*r^2/2+K+α*C/N+N*F^2/lam) ≤
        α*(K+α*C/N+N*F^2/lam) := by
      apply mul_le_mul_of_nonneg_left _ hα
      have hnon : 0 ≤ lam*N*r^2/2 := by positivity
      linarith only [hnon]
    exact hraw.trans ((mul_le_mul_of_nonneg_right hdrop (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left he (mul_nonneg hα hN.le))) hcoef))
  · exact (houter (le_of_not_ge he)).trans (mul_nonneg hcoef (Real.exp_pos _).le)

end CompositionalMemory

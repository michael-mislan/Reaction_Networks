import Mathlib

namespace CompositionalMemory

/-- The same two annular budgets control the interior ceiling coefficient. -/
theorem recovery_ceiling_coefficient (α N lam rho F K C : ℝ)
    (hα : 0 ≤ α) (hN : 0 ≤ N) (hlam : 0 < lam)
    (hforce : F^2 ≤ lam^2*rho/8) (hcopy : K+α*C/N ≤ lam*N*rho/8) :
    α*(K+α*C/N+N*F^2/lam) ≤ α*lam*N*rho/4 := by
  have hf : N*F^2/lam ≤ lam*N*rho/8 := (div_le_iff₀ hlam).mpr (by
    nlinarith only [mul_le_mul_of_nonneg_left hforce hN])
  have hh := mul_le_mul_of_nonneg_left (add_le_add hcopy hf) hα
  nlinarith only [hh]

theorem recovery_plateau_bound (α N lam rho F K C core : ℝ)
    (hα : 0 < α) (hN : 0 < N) (hlam : 0 < lam) (hrho : 0 < rho)
    (hforce : F^2 ≤ lam^2*rho/8) (hcopy : K+α*C/N ≤ lam*N*rho/8) :
    (α*(K+α*C/N+N*F^2/lam)*Real.exp (α*N*core)+
      (α*lam*N*rho/4)*Real.exp (α*N*core))/(α*lam*N*rho/4) ≤
        2*Real.exp (α*N*core) := by
  apply (div_le_iff₀ (by positivity : 0 < α*lam*N*rho/4)).mpr
  have hh := mul_le_mul_of_nonneg_right
    (recovery_ceiling_coefficient α N lam rho F K C hα.le hN.le hlam hforce hcopy)
    (Real.exp_pos (α*N*core)).le
  nlinarith only [hh]

/-- A fixed recovery time gives exponential accuracy with no module-count
dependence in the exponent. A positive gap b-core makes the bound decay. -/
theorem recovery_probability_exponential (p k α N lam rho a b core t : ℝ)
    (hk : 0 ≤ k) (hα : 0 ≤ α) (hN : 0 ≤ N) (hcore : 0 ≤ core)
    (ht : 4*a ≤ lam*rho*t)
    (hevent : Real.exp (α*N*b)*p ≤
      k*(Real.exp (-(α*lam*N*rho/4)*t)*Real.exp (α*N*a)+2*Real.exp (α*N*core))) :
    p ≤ 3*k*Real.exp (-α*N*(b-core)) := by
  have htime : -(α*lam*N*rho/4)*t+α*N*a ≤ 0 := by
    have hh := mul_le_mul_of_nonneg_left ht (mul_nonneg hα hN)
    nlinarith only [hh]
  have hfirst : Real.exp (-(α*lam*N*rho/4)*t)*Real.exp (α*N*a) ≤ 1 := by
    rw [← Real.exp_add]
    exact Real.exp_le_one_iff.mpr htime
  have hsecond : 1 ≤ Real.exp (α*N*core) := Real.one_le_exp_iff.mpr (by positivity)
  have hsum : k*(Real.exp (-(α*lam*N*rho/4)*t)*Real.exp (α*N*a)+2*Real.exp (α*N*core)) ≤
      3*k*Real.exp (α*N*core) := by
    have hh := mul_le_mul_of_nonneg_left (hfirst.trans hsecond) hk
    nlinarith only [hh]
  have heq : Real.exp (α*N*b)*(3*k*Real.exp (-α*N*(b-core)))=3*k*Real.exp (α*N*core) := by
    calc
      _ = 3*k*(Real.exp (α*N*b)*Real.exp (-α*N*(b-core))) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  exact (mul_le_mul_iff_right₀ (Real.exp_pos (α*N*b))).mp
    ((hevent.trans hsum).trans_eq heq.symm)

end CompositionalMemory

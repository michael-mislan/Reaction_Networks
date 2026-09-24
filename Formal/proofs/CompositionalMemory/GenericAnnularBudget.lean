import proofs.CompositionalMemory.GenericFixedScale

namespace CompositionalMemory

/-- A radius lower bound, small force and sufficiently large copy scale
turn the local exponential budget into a uniform negative annular bound. -/
theorem fixed_scale_annular_budget (α N lam r rho F K C : ℝ)
    (hα : 0 ≤ α) (hN : 0 < N) (hlam : 0 < lam)
    (hr : rho ≤ r^2) (hforce : F^2 ≤ lam^2*rho/8)
    (hcopy : K+α*C/N ≤ lam*N*rho/8) :
    α*(-lam*N*r^2/2+K+α*C/N+N*F^2/lam) ≤ -α*lam*N*rho/4 := by
  have hf : N*F^2/lam ≤ lam*N*rho/8 := by
    apply (div_le_iff₀ hlam).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hforce hN.le]
  have hrad := mul_le_mul_of_nonneg_left hr (mul_nonneg hlam.le hN.le)
  have hi : -lam*N*r^2/2+K+α*C/N+N*F^2/lam ≤ -lam*N*rho/4 := by
    nlinarith only [hf,hrad,hcopy]
  convert mul_le_mul_of_nonneg_left hi hα using 1
  ring

end CompositionalMemory

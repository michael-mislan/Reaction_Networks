import proofs.CompositionalMemory.ExponentialMoments
import Mathlib

namespace CompositionalMemory

theorem dissipation_young (lam r F : ℝ) (hlam : 0 < lam) :
    F*r ≤ lam*r^2/4+F^2/lam := by
  apply le_of_mul_le_mul_right (a := lam) _ hlam
  rw [add_mul,div_mul_cancel₀ _ (ne_of_gt hlam)]
  nlinarith only [sq_nonneg (lam*r-2*F)]

/-- Uniform module-quality version of the exponential generator estimate.
All inputs are reaction energy increments and their rate-weighted moments. -/
theorem generic_exponential_budget {ι : Type*} [Fintype ι]
    (rate delta : ι → ℝ) (α N lam r F K B C : ℝ)
    (hα : 0 ≤ α) (hN : 0 < N) (hlam : 0 < lam)
    (hrate : ∀ j, 0 ≤ rate j) (hsmall : ∀ j, |α*N*delta j| ≤ 1)
    (hd : ∑ j, rate j*delta j ≤ -lam*r^2+F*r+K/N)
    (hv : ∑ j, rate j*(delta j)^2 ≤ B*r^2/N+C/N^3)
    (habsorb : α*B ≤ lam/4) :
    (∑ j, rate j*(Real.exp (α*N*delta j)-1)) ≤
      α*(-lam*N*r^2/2+K+α*C/N+N*F^2/lam) := by
  have hs := exponential_sum_le_two_moments rate delta (α*N) hrate hsmall
  have hdr := mul_le_mul_of_nonneg_left hd (mul_nonneg hα hN.le)
  have hvr := mul_le_mul_of_nonneg_left hv (sq_nonneg (α*N))
  have he : α*N*(-lam*r^2+F*r+K/N)+(α*N)^2*(B*r^2/N+C/N^3) =
      α*(-lam*N*r^2+N*F*r+K+α*B*N*r^2+α*C/N) := by
    field_simp
    ring
  have ha := mul_le_mul_of_nonneg_right habsorb (mul_nonneg hN.le (sq_nonneg r))
  have hy := mul_le_mul_of_nonneg_left (dissipation_young lam r F hlam) hN.le
  have hi : -lam*N*r^2+N*F*r+K+α*B*N*r^2+α*C/N ≤
      -lam*N*r^2/2+K+α*C/N+N*F^2/lam := by
    simp only [div_eq_mul_inv] at hy ⊢
    nlinarith only [ha,hy]
  exact hs.trans ((add_le_add hdr hvr).trans (he.trans_le (mul_le_mul_of_nonneg_left hi hα)))

end CompositionalMemory

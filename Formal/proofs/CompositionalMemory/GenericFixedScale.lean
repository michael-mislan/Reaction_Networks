import proofs.CompositionalMemory.GenericExponentialBudget

namespace CompositionalMemory

theorem rescaled_small_condition (α N v X Y : ℝ)
    (hα : 0 ≤ α) (hN : 0 < N) (hv : N ≤ v) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hs : α*(X+Y/N) ≤ 1) : (α*N/v)*(X+Y/v) ≤ 1 := by
  have hv0 : 0 < v := hN.trans_le hv
  have hb : α*N/v ≤ α := (div_le_iff₀ hv0).mpr (mul_le_mul_of_nonneg_left hv hα)
  have hc : X+Y/v ≤ X+Y/N := add_le_add le_rfl (div_le_div_of_nonneg_left hY hN hv)
  exact (mul_le_mul hb hc (by positivity) hα).trans hs

theorem fixed_scale_exponential_of_moments {ι : Type*} [Fintype ι]
    (rate delta : ι → ℝ) (α N v lam r F K B C : ℝ)
    (hα : 0 ≤ α) (hN : 0 < N) (hv : N ≤ v) (hlam : 0 < lam)
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hrate : ∀ j, 0 ≤ rate j) (hsmall : ∀ j, |α*N*delta j| ≤ 1)
    (hd : ∑ j, rate j*delta j ≤ -lam*r^2+F*r+K/v)
    (hvar : ∑ j, rate j*(delta j)^2 ≤ B*r^2/v+C/v^3)
    (habsorb : α*B ≤ lam/4) :
    (∑ j, rate j*(Real.exp (α*N*delta j)-1)) ≤
      α*(-lam*N*r^2/2+K+α*C/N+N*F^2/lam) := by
  have hd' := hd.trans (add_le_add le_rfl (div_le_div_of_nonneg_left hK hN hv))
  have hcubes : N^3 ≤ v^3 := pow_le_pow_left₀ hN.le hv 3
  have hvar' := hvar.trans (add_le_add
    (div_le_div_of_nonneg_left (mul_nonneg hB (sq_nonneg r)) hN hv)
    (div_le_div_of_nonneg_left hC (pow_pos hN 3) hcubes))
  exact generic_exponential_budget rate delta α N lam r F K B C
    hα hN hlam hrate hsmall hd' hvar' habsorb

end CompositionalMemory

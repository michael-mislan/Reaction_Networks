import proofs.CompositionalMemory.GenericLocalSmall
import proofs.CompositionalMemory.GenericFixedScale

namespace CompositionalMemory

/-- The fixed-birth-scale exponential generator estimate for the explicit modular
architecture, derived from reactions and uniform module-quality bounds. -/
theorem generic_local_fixed_scale_generator {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    {k : ℕ} (hk : 1 ≤ k) (i : Fin k)
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hQ : ∀ x y, Q x y=Q y x)
    (y u b : V) (ν : ι → V) (a : ι → ℝ) (z w : Fin k → ℝ)
    (α N v γ κ lam r A P R F U Z L : ℝ)
    (hN : 0 < N) (hNv : N ≤ v) (hP : 0 ≤ P) (hα : 0 ≤ α) (hlam : 0 < lam) (hγ : 0 ≤ γ) (hR : 0 ≤ R)
    (hU : 0 ≤ U) (hZ : 0 ≤ Z) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (ha : ∀ j, 0 ≤ a j) (hA : ∑ j, a j ≤ A)
    (hcross : ∀ j, |Q y (ν j)| ≤ P*r) (hquad : ∀ j, |Q (ν j) (ν j)| ≤ R)
    (hd : 2*Q y (∑ j, a j • ν j) ≤ -lam*r^2+F*r)
    (hw : ∀ j, 0 ≤ w j) (hz : ∀ j, 0 ≤ z j ∧ z j ≤ Z)
    (hrow : ∑ j, w j ≤ κ)
    (hop : ∀ x q, |Q x q| ≤ L*‖x‖*‖q‖)
    (hy : ‖y‖ ≤ r) (hu : ‖u‖ ≤ U) (hb : ‖b‖ ≤ 1)
    (hsres : α*(2*(P*r)+R/N) ≤ 1)
    (hscouple : α*(2*L*r*(U+1)+L*(U+1)^2/N) ≤ 1)
    (habsorb : α*(8*A*P^2+8*L^2*γ*Z*(U+1)^2+16*L^2*Z*κ) ≤ lam/4) :
    let rate := localChannelRate a γ v z w i
    let jump := localChannelJump ν u b v i
    (∑ j, rate j*(Real.exp (α*N*(Q (y+jump j) (y+jump j)-Q y y))-1)) ≤
      α*(-lam*N*r^2/2+(A*R+L*γ*Z*(U+1)^2+2*L*Z*κ)+
        α*(2*A*R^2+2*L^2*γ*Z*(U+1)^4+4*L^2*Z*κ)/N+
        N*(F+2*L*γ*Z*(U+1)+4*L*Z*κ)^2/lam) := by
  have hv : 0 < v := hN.trans_le hNv
  have hA0 : 0 ≤ A := (Finset.sum_nonneg (fun j _ => ha j)).trans hA
  have hκ0 : 0 ≤ κ := (Finset.sum_nonneg (fun j _ => hw j)).trans hrow
  have hmom := generic_local_energy_moments hk i Q hQ y u b ν a z w
    v γ κ lam r A P R F U Z L hv hγ hR hU hZ hL hr ha hA hcross hquad hd
    hw hz hrow hop hy hu hb
  have hs := generic_local_jump_small hk i Q hQ y u b ν (α*N/v) v L r U P R
    hv (by positivity) hL hr hU hop hy hu hb hcross hquad
    (rescaled_small_condition α N v (2*(P*r)) R hα hN hNv (by positivity) hR hsres)
    (rescaled_small_condition α N v (2*L*r*(U+1)) (L*(U+1)^2) hα hN hNv
      (by positivity) (by positivity) hscouple)
  have he : α*N/v*v=α*N := by field_simp
  have hs' (j) : |α*N*(Q (y+localChannelJump ν u b v i j)
      (y+localChannelJump ν u b v i j)-Q y y)| ≤ 1 := by
    simpa only [he] using hs j
  have hrate (j) : 0 ≤ localChannelRate a γ v z w i j := by
    rcases j with j | j
    · exact mul_nonneg hv.le (ha j)
    · rcases j with j | j
      · exact mul_nonneg (mul_nonneg hγ hv.le) (hz j).1
      · rcases j with j | j
        · exact mul_nonneg hv.le (mul_nonneg (hw j) (hz i).1)
        · exact mul_nonneg hv.le (mul_nonneg (hw j) (hz j).1)
  exact fixed_scale_exponential_of_moments (localChannelRate a γ v z w i)
    (fun j => Q (y+localChannelJump ν u b v i j) (y+localChannelJump ν u b v i j)-Q y y)
    α N v lam r (F+2*L*γ*Z*(U+1)+4*L*Z*κ)
    (A*R+L*γ*Z*(U+1)^2+2*L*Z*κ)
    (8*A*P^2+8*L^2*γ*Z*(U+1)^2+16*L^2*Z*κ)
    (2*A*R^2+2*L^2*γ*Z*(U+1)^4+4*L^2*Z*κ)
    hα hN hNv hlam (by positivity) (by positivity) (by positivity)
    hrate hs' hmom.1 hmom.2 habsorb

end CompositionalMemory

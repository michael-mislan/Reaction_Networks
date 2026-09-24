import proofs.CompositionalMemory.GenericLocalObservable
import proofs.CompositionalMemory.GenericGeneratorEnvelope

namespace CompositionalMemory

/-- The fixed-birth-scale exponential generator estimate for the explicit modular
architecture, derived from reactions and uniform module-quality bounds. -/
theorem generic_local_generator_envelope {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    {k : ℕ} (hk : 1 ≤ k) (i : Fin k)
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hQ : ∀ x y, Q x y=Q y x)
    (y u b : V) (ν : ι → V) (a : ι → ℝ) (z w : Fin k → ℝ)
    (α N v γ κ lam r rho M A P R F U Z L : ℝ)
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
    (habsorb : α*(8*A*P^2+8*L^2*γ*Z*(U+1)^2+16*L^2*Z*κ) ≤ lam/4)
    (hM : 0 < M) (hrho0 : 0 ≤ rho) (henergy : Q y y ≤ M*r^2)
    (hforce : (F+2*L*γ*Z*(U+1)+4*L*Z*κ)^2 ≤ lam^2*rho/8)
    (hcopy : (A*R+L*γ*Z*(U+1)^2+2*L*Z*κ)+
      α*(2*A*R^2+2*L^2*γ*Z*(U+1)^4+4*L^2*Z*κ)/N ≤ lam*N*rho/8) :
    let rate := localChannelRate a γ v z w i
    let jump := localChannelJump ν u b v i
    (∑ j, rate j*(Real.exp (α*N*Q (y+jump j) (y+jump j))-Real.exp (α*N*Q y y))) ≤
      α*((A*R+L*γ*Z*(U+1)^2+2*L*Z*κ)+
        α*(2*A*R^2+2*L^2*γ*Z*(U+1)^4+4*L^2*Z*κ)/N+
        N*(F+2*L*γ*Z*(U+1)+4*L*Z*κ)^2/lam)*Real.exp (α*N*(M*rho)) := by
  have hA0 : 0 ≤ A := (Finset.sum_nonneg (fun j _ => ha j)).trans hA
  have hκ0 : 0 ≤ κ := (Finset.sum_nonneg (fun j _ => hw j)).trans hrow
  have hratio := generic_local_fixed_scale_generator hk i Q hQ y u b ν a z w
    α N v γ κ lam r A P R F U Z L hN hNv hP hα hlam hγ hR hU hZ hL hr
    ha hA hcross hquad hd hw hz hrow hop hy hu hb hsres hscouple habsorb
  have hraw := exponential_observable_of_ratio (localChannelRate a γ v z w i)
    (fun j => Q (y+localChannelJump ν u b v i j) (y+localChannelJump ν u b v i j))
    (Q y y) (α*N) _ hratio
  apply exponential_generator_envelope _ (Q y y) (M*rho) α N lam r
    (A*R+L*γ*Z*(U+1)^2+2*L*Z*κ)
    (2*A*R^2+2*L^2*γ*Z*(U+1)^4+4*L^2*Z*κ)
    (F+2*L*γ*Z*(U+1)+4*L*Z*κ)
    hα hN hlam (by positivity) (by positivity) hraw
  intro he
  have hrr : rho ≤ r^2 := (mul_le_mul_iff_right₀ hM).mp (he.trans henergy)
  have h := generic_local_annular_observable hk i Q hQ y u b ν a z w
    α N v γ κ lam r rho A P R F U Z L hN hNv hP hα hlam hγ hR hU hZ hL hr
    ha hA hcross hquad hd hw hz hrow hop hy hu hb hsres hscouple habsorb hrr hforce hcopy
  have hcoef : -α*lam*N*rho/4 ≤ 0 := by
    have hn : 0 ≤ α*lam*N*rho/4 := by positivity
    nlinarith only [hn]
  exact h.trans (mul_nonpos_of_nonpos_of_nonneg hcoef (Real.exp_pos _).le)

end CompositionalMemory

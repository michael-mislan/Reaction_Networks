import proofs.CompositionalMemory.GenericCountEnvelope
import proofs.CompositionalMemory.GenericCountAnnulus

namespace CompositionalMemory

/-- Affine exponential recovery drift for the literal count architecture. -/
theorem general_count_recovery_drift {k d : ℕ} {ι : Type*} [Fintype ι]
    (hk : 1 ≤ k) (consume produce : Fin k → ι → Fin d → ℕ)
    (coeff : Fin k → ι → ℝ) (z : Fin d) (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (hdiag : ∀ j, w j j=0) (hsym : ∀ j l, w j l=w l j)
    (s : GeneralCountState k d) (hm : 0 < s.2) (i : Fin k)
    (center : Fin d → ℝ) :
    let v := (s.2:ℝ)/k
    let u := generalConcentration s i
    let y := u-center
    let ν := fun j a => (produce i j a:ℝ)-(consume i j a:ℝ)
    ∀ (Q : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) →ₗ[ℝ] ℝ)
      (α N κ lam r rho M A P R U Z L D : ℝ),
    (∀ x q, Q x q=Q q x) →
    0 < N → N ≤ v → 0 ≤ P → 0 ≤ α → 0 < lam → 0 ≤ γ → 0 ≤ R →
    0 ≤ U → 0 ≤ Z → 0 ≤ L → 0 ≤ r →
    (∀ j, 0 ≤ coeff i j) →
    (∑ j, coeff i j*U^(∑ a, consume i j a)) ≤ A →
    (∑ j, (coeff i j*(∑ a, consume i j a:ℕ)^2*(U+1)^(∑ a, consume i j a))*‖ν j‖) ≤ D →
    (∀ a, (s.1 i a:ℝ)/v ≤ U) →
    (∀ j, |Q y (ν j)| ≤ P*r) → (∀ j, |Q (ν j) (ν j)| ≤ R) →
    2*Q y (∑ j, (coeff i j*(∏ a, ((s.1 i a:ℝ)/v)^(consume i j a))) • ν j) ≤ -lam*r^2 →
    (∀ j, 0 ≤ w i j) →
    (∀ j, 0 ≤ generalConcentration s j z ∧ generalConcentration s j z ≤ Z) →
    (∑ j, w i j) ≤ κ →
    (∀ x q, |Q x q| ≤ L*‖x‖*‖q‖) → ‖y‖ ≤ r → ‖u‖ ≤ U →
    α*(2*(P*r)+R/N) ≤ 1 →
    α*(2*L*r*(U+1)+L*(U+1)^2/N) ≤ 1 →
    α*(8*A*P^2+8*L^2*γ*Z*(U+1)^2+16*L^2*Z*κ) ≤ lam/4 →
    0 < M → 0 ≤ rho → Q y y ≤ M*r^2 →
    (2*L*D/N+2*L*γ*Z*(U+1)+4*L*Z*κ)^2 ≤ lam^2*rho/8 →
    (A*R+L*γ*Z*(U+1)^2+2*L*Z*κ)+
      α*(2*A*R^2+2*L^2*γ*Z*(U+1)^4+4*L^2*Z*κ)/N ≤ lam*N*rho/8 →
    reactionGenerator (generalGlobalNext consume produce z)
      (generalGlobalRate consume coeff z γ w)
      (fun t => Real.exp (α*N*Q (generalConcentration t i-center)
        (generalConcentration t i-center))) s ≤
      (-α*lam*N*rho/4)*Real.exp (α*N*Q y y)+(α*((A*R+L*γ*Z*(U+1)^2+2*L*Z*κ)+
        α*(2*A*R^2+2*L^2*γ*Z*(U+1)^4+4*L^2*Z*κ)/N+
        N*(2*L*D/N+2*L*γ*Z*(U+1)+4*L*Z*κ)^2/lam)+α*lam*N*rho/4)*Real.exp (α*N*(M*rho)) := by
  classical
  intro v u y ν Q α N κ lam r rho M A P R U Z L D hQ hN hNv hP hα hlam hγ hR
    hU hZ hL hr hc hA hD hcoord hcross hquad hd hw hz hrow hop hy hu
    hsres hscouple habsorb hM hrho henergy hforce hcopy
  have henv := general_count_generator_envelope hk consume produce coeff z γ w hdiag hsym s hm i
    center Q α N κ lam r rho M A P R U Z L D hQ hN hNv hP hα hlam hγ hR
    hU hZ hL hr hc hA hD hcoord hcross hquad hd hw hz hrow hop hy hu
    hsres hscouple habsorb hM hrho henergy hforce hcopy
  let decay := α*lam*N*rho/4
  have hdecay : 0 ≤ decay := by dsimp [decay]; positivity
  by_cases he : Q y y ≤ M*rho
  · have hexp : Real.exp (α*N*Q y y) ≤ Real.exp (α*N*(M*rho)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left he (mul_nonneg hα hN.le))
    have hh := mul_le_mul_of_nonneg_left hexp hdecay
    dsimp [decay] at hh
    nlinarith only [henv,hh]
  · have hrr : rho ≤ r^2 := (mul_le_mul_iff_right₀ hM).mp ((le_of_not_ge he).trans henergy)
    have hann := general_count_annular_generator hk consume produce coeff z γ w hdiag hsym s hm i
      center Q α N κ lam r rho A P R U Z L D hQ hN hNv hP hα hlam hγ hR
      hU hZ hL hr hc hA hD hcoord hcross hquad hd hw hz hrow hop hy hu
      hsres hscouple habsorb hrr hforce hcopy
    have hA0 : 0 ≤ A := (Finset.sum_nonneg (fun j _ =>
      mul_nonneg (hc j) (pow_nonneg hU _))).trans hA
    have hκ0 : 0 ≤ κ := (Finset.sum_nonneg (fun j _ => hw j)).trans hrow
    have hpos : 0 ≤ (α*((A*R+L*γ*Z*(U+1)^2+2*L*Z*κ)+
        α*(2*A*R^2+2*L^2*γ*Z*(U+1)^4+4*L^2*Z*κ)/N+
        N*(2*L*D/N+2*L*γ*Z*(U+1)+4*L*Z*κ)^2/lam)+α*lam*N*rho/4)*
          Real.exp (α*N*(M*rho)) := by positivity
    exact hann.trans (le_add_of_nonneg_right hpos)

end CompositionalMemory

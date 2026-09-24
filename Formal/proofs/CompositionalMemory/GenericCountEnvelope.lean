import proofs.CompositionalMemory.GenericGlobalGenerator
import proofs.CompositionalMemory.GenericMassActionBounds
import proofs.CompositionalMemory.GenericLocalEnvelope

namespace CompositionalMemory

/-- An exponential generator ceiling for the literal count architecture, with
ordinary mass-action propensities. The deterministic hypothesis concerns the
macroscopic reaction polynomial; its finite-copy correction is derived. -/
theorem general_count_generator_envelope {k d : ℕ} {ι : Type*} [Fintype ι]
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
      α*((A*R+L*γ*Z*(U+1)^2+2*L*Z*κ)+
        α*(2*A*R^2+2*L^2*γ*Z*(U+1)^4+4*L^2*Z*κ)/N+
        N*(2*L*D/N+2*L*γ*Z*(U+1)+4*L*Z*κ)^2/lam)*Real.exp (α*N*(M*rho)) := by
  classical
  intro v u y ν Q α N κ lam r rho M A P R U Z L D hQ hN hNv hP hα hlam hγ hR
    hU hZ hL hr hc hA hD hcoord hcross hquad hd hw hz hrow hop hy hu
    hsres hscouple habsorb hM hrho henergy hforce hcopy
  let a := fun j => countReactionDensity (coeff i j) v (consume i j) (s.1 i)
  let b := fun a : Fin d => if a=z then (1:ℝ) else 0
  have hv : 0 < v := hN.trans_le hNv
  have ha (j) : 0 ≤ a j := count_reaction_density_nonneg _ _ _ _ (hc j) hv.le
  have hactivity : ∑ j, a j ≤ A := (Finset.sum_le_sum (fun j _ =>
    count_reaction_density_le _ _ _ _ _ (hc j) hv hcoord)).trans hA
  have hdrift := mass_action_dissipation_at_birth_scale Q y ν (consume i) (s.1 i)
    (coeff i) N v U L r lam D hN hNv hU hL hr hc hcoord hop hy hD hd
  have hb : ‖b‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
    intro a
    dsimp [b]
    split_ifs <;> norm_num
  have hlocal := generic_local_generator_envelope hk i Q hQ y u b ν a
    (fun j => generalConcentration s j z) (w i) α N v γ κ lam r rho M A P R
    (2*L*D/N) U Z L hN hNv hP hα hlam hγ hR hU hZ hL hr ha hactivity
    hcross hquad hdrift hw hz hrow hop hy hu hb hsres hscouple habsorb
    hM hrho henergy hforce hcopy
  rw [general_global_generator_local hk consume produce coeff z γ w hdiag hsym s hm i
    (fun x => Real.exp (α*N*Q (x-center) (x-center)))]
  simpa only [a,b,v,u,y,ν,add_sub_right_comm] using hlocal

end CompositionalMemory

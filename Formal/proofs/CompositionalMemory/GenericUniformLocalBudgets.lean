import proofs.CompositionalMemory.GenericUniformParameters

namespace CompositionalMemory

theorem exists_uniform_local_budgets (lam rho A P R D U Z L rmax : ℝ)
    (hlam : 0 < lam) (hrho : 0 < rho)
    (hA : 0 ≤ A) (hP : 0 ≤ P) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hU : 0 ≤ U) (hZ : 0 ≤ Z) (hL : 0 ≤ L) (hrmax : 0 ≤ rmax) :
    ∃ α δ N0 : ℝ, 0 < α ∧ 0 < δ ∧ δ ≤ 1 ∧ 1 ≤ N0 ∧
    ∀ N r γ κ : ℝ, N0 ≤ N → 0 ≤ r → r ≤ rmax →
      0 ≤ γ → γ ≤ δ → 0 ≤ κ → κ ≤ δ →
      α*(2*(P*r)+R/N) ≤ 1 ∧
      α*(2*L*r*(U+1)+L*(U+1)^2/N) ≤ 1 ∧
      α*(8*A*P^2+8*L^2*γ*Z*(U+1)^2+16*L^2*Z*κ) ≤ lam/4 ∧
      (2*L*D/N+2*L*γ*Z*(U+1)+4*L*Z*κ)^2 ≤ lam^2*rho/8 ∧
      (A*R+L*γ*Z*(U+1)^2+2*L*Z*κ)+
        α*(2*A*R^2+2*L^2*γ*Z*(U+1)^4+4*L^2*Z*κ)/N ≤ lam*N*rho/8 := by
  let K := A*R+L*Z*(U+1)^2+2*L*Z
  let B := 8*A*P^2+8*L^2*Z*(U+1)^2+16*L^2*Z
  let C := 2*A*R^2+2*L^2*Z*(U+1)^4+4*L^2*Z
  obtain ⟨α,hα,hS,hT,hB⟩ := exists_uniform_exponential_parameter lam
    (2*(P*rmax)+R) (2*L*rmax*(U+1)+L*(U+1)^2) B hlam
    (by positivity) (by positivity) (by dsimp [B]; positivity)
  obtain ⟨δ,N0,hδ,hδ1,hN01,hbudget⟩ := exists_uniform_force_copy_parameters
    α lam rho (2*L*D) (2*L*Z*(U+1)+4*L*Z) K C hα.le hlam hrho
    (by positivity) (by positivity) (by dsimp [K]; positivity) (by dsimp [C]; positivity)
  refine ⟨α,δ,N0,hα,hδ,hδ1,hN01,?_⟩
  intro N r γ κ hN hr hrr hγ hγδ hκ hκδ
  have hN1 : 1 ≤ N := hN01.trans hN
  have hNp : 0 < N := by linarith
  have hγ1 : γ ≤ 1 := hγδ.trans hδ1
  have hκ1 : κ ≤ 1 := hκδ.trans hδ1
  have hdiv (X : ℝ) (hX : 0 ≤ X) : X/N ≤ X := (div_le_iff₀ hNp).mpr (by
    nlinarith only [mul_le_mul_of_nonneg_left hN1 hX])
  have hs : 2*(P*r)+R/N ≤ 2*(P*rmax)+R := by
    nlinarith only [mul_le_mul_of_nonneg_left hrr (show 0 ≤ 2*P by positivity),hdiv R hR]
  have ht : 2*L*r*(U+1)+L*(U+1)^2/N ≤ 2*L*rmax*(U+1)+L*(U+1)^2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hrr (show 0 ≤ 2*L*(U+1) by positivity),
      hdiv (L*(U+1)^2) (by positivity)]
  have hb : 8*A*P^2+8*L^2*γ*Z*(U+1)^2+16*L^2*Z*κ ≤ B := by
    dsimp [B]
    nlinarith only [mul_le_mul_of_nonneg_left hγ1 (show 0 ≤ 8*L^2*Z*(U+1)^2 by positivity),
      mul_le_mul_of_nonneg_left hκ1 (show 0 ≤ 16*L^2*Z by positivity)]
  have hk : A*R+L*γ*Z*(U+1)^2+2*L*Z*κ ≤ K := by
    dsimp [K]
    nlinarith only [mul_le_mul_of_nonneg_left hγ1 (show 0 ≤ L*Z*(U+1)^2 by positivity),
      mul_le_mul_of_nonneg_left hκ1 (show 0 ≤ 2*L*Z by positivity)]
  have hc : 2*A*R^2+2*L^2*γ*Z*(U+1)^4+4*L^2*Z*κ ≤ C := by
    dsimp [C]
    nlinarith only [mul_le_mul_of_nonneg_left hγ1 (show 0 ≤ 2*L^2*Z*(U+1)^4 by positivity),
      mul_le_mul_of_nonneg_left hκ1 (show 0 ≤ 4*L^2*Z by positivity)]
  have hf : 2*L*D/N+2*L*γ*Z*(U+1)+4*L*Z*κ ≤
      2*L*D/N+(2*L*Z*(U+1)+4*L*Z)*δ := by
    nlinarith only [mul_le_mul_of_nonneg_left hγδ (show 0 ≤ 2*L*Z*(U+1) by positivity),
      mul_le_mul_of_nonneg_left hκδ (show 0 ≤ 4*L*Z by positivity)]
  have hf2 := (sq_le_sq₀ (show 0 ≤ 2*L*D/N+2*L*γ*Z*(U+1)+4*L*Z*κ by positivity)
    (show 0 ≤ 2*L*D/N+(2*L*Z*(U+1)+4*L*Z)*δ by positivity)).mpr hf
  exact ⟨(mul_le_mul_of_nonneg_left hs hα.le).trans hS,
    (mul_le_mul_of_nonneg_left ht hα.le).trans hT,
    (mul_le_mul_of_nonneg_left hb hα.le).trans hB,
    hf2.trans (hbudget N hN).1,
    (add_le_add hk (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc hα.le) hNp.le)).trans
      (hbudget N hN).2⟩

end CompositionalMemory

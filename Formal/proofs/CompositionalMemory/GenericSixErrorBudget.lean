import proofs.CompositionalMemory.GenericGenerationBudget

namespace CompositionalMemory

theorem exists_generation_exponent (α g₀ g₁ gr δ C : ℝ)
    (hα : 0 < α) (hg₀ : 0 < g₀) (hg₁ : 0 < g₁) (hgr : 0 < gr)
    (hδ : 0 < δ) (hC : 0 < C) :
    ∃ cgen : ℝ, 0 < cgen ∧ cgen ≤ α*g₀/2 ∧ cgen ≤ α*g₁/2 ∧
      cgen ≤ α*gr ∧ cgen ≤ 1/125 ∧ cgen ≤ 9/4000 ∧ cgen ≤ δ^2/C := by
  let cgen := min (α*g₀/2) (min (α*g₁/2) (min (α*gr) (min (1/125) (min (9/4000) (δ^2/C)))))
  have hp : 0 < cgen := by dsimp [cgen]; positivity
  have h₀ : cgen ≤ α*g₀/2 := min_le_left _ _
  have hrest : cgen ≤ min (α*g₁/2) (min (α*gr) (min (1/125) (min (9/4000) (δ^2/C)))) := min_le_right _ _
  have h₁ := hrest.trans (min_le_left _ _)
  have hrest₂ := hrest.trans (min_le_right _ _)
  have h₂ := hrest₂.trans (min_le_left _ _)
  have hrest₃ := hrest₂.trans (min_le_right _ _)
  have h₃ := hrest₃.trans (min_le_left _ _)
  have hrest₄ := hrest₃.trans (min_le_right _ _)
  exact ⟨cgen,hp,h₀,h₁,h₂,h₃,hrest₄.trans (min_le_left _ _),hrest₄.trans (min_le_right _ _)⟩

/-- Combine the six derived generation errors into one uniform exponential. -/
theorem generation_six_error_bound
    (p k d N α H t₀ t₁ core recover parent birth outer δ C ceiling cgen : ℝ)
    (hk : 1 ≤ k) (hd : 0 ≤ d) (hN : 0 ≤ N) (hα : 0 < α) (hH : 0 ≤ H)
    (ht₀ : 0 ≤ t₀) (ht₁ : 0 ≤ t₁)
    (hcore : core < recover) (hrec : recover < parent) (hparent : parent < birth) (hbirth : birth < outer)
    (hceiling : ceiling ≤ (α*H*N/4)*Real.exp (α*N*core))
    (hc₀ : cgen ≤ α*(outer-birth)/2) (hc₁ : cgen ≤ α*(parent-recover)/2)
    (hcr : cgen ≤ α*(recover-core)) (hce : cgen ≤ 1/125) (hcl : cgen ≤ 9/4000)
    (hcp : cgen ≤ δ^2/C)
    (hraw : p ≤ (k*(Real.exp (α*N*birth)+t₀*ceiling)/Real.exp (α*N*outer)+
      (Real.exp (-(k*N)/125)+3*k*Real.exp (-α*N*(recover-core))))+
      (k*(Real.exp (α*N*recover)+t₁*ceiling)/Real.exp (α*N*parent)+
      Real.exp (-9*(k*N)/4000)+2*k*d*Real.exp (-2*N*δ^2/(2*C)))) :
    p ≤ k*(7+2*d+(H/2)*(t₀/(outer-birth)+t₁/(parent-recover)))*Real.exp (-cgen*N) := by
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hg₀ : 0 < outer-birth := sub_pos.mpr hbirth
  have hg₁ : 0 < parent-recover := sub_pos.mpr hrec
  have hr₀ : Real.exp (-α*N*(outer-birth)/2) ≤ Real.exp (-cgen*N) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_right hc₀ hN]
  have hr₁ : Real.exp (-α*N*(parent-recover)/2) ≤ Real.exp (-cgen*N) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_right hc₁ hN]
  have h₀ := (generation_exit_exponential k α N H t₀ birth outer core ceiling hk0 hα hN hH ht₀
    (hcore.trans (hrec.trans hparent)).le hbirth hceiling).trans
    (mul_le_mul_of_nonneg_left hr₀ (show 0 ≤ k*(1+t₀*H/(2*(outer-birth))) by positivity))
  have h₁ := (generation_exit_exponential k α N H t₁ recover parent core ceiling hk0 hα hN hH ht₁
    hcore.le hrec hceiling).trans
    (mul_le_mul_of_nonneg_left hr₁ (show 0 ≤ k*(1+t₁*H/(2*(parent-recover))) by positivity))
  have hkn : N ≤ k*N := by nlinarith only [mul_le_mul_of_nonneg_right hk hN]
  have he : Real.exp (-(k*N)/125) ≤ k*Real.exp (-cgen*N) := by
    have hh : Real.exp (-(k*N)/125) ≤ Real.exp (-cgen*N) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hkn,mul_le_mul_of_nonneg_right hce hN]
    exact hh.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hk (Real.exp_pos _).le)
  have hl : Real.exp (-9*(k*N)/4000) ≤ k*Real.exp (-cgen*N) := by
    have hh : Real.exp (-9*(k*N)/4000) ≤ Real.exp (-cgen*N) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hkn,mul_le_mul_of_nonneg_right hcl hN]
    exact hh.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hk (Real.exp_pos _).le)
  have hrr : 3*k*Real.exp (-α*N*(recover-core)) ≤ 3*k*Real.exp (-cgen*N) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_right hcr hN]
  have hp : 2*k*d*Real.exp (-2*N*δ^2/(2*C)) ≤ 2*k*d*Real.exp (-cgen*N) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have heq : -2*N*δ^2/(2*C)=-(δ^2/C)*N := by ring
    rw [heq]
    nlinarith only [mul_le_mul_of_nonneg_right hcp hN]
  have hsum := hraw.trans
    (add_le_add (add_le_add h₀ (add_le_add he hrr)) (add_le_add (add_le_add h₁ hl) hp))
  convert hsum using 1
  field_simp
  ring

end CompositionalMemory

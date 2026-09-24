import proofs.CoreCouplingGlobal.ResponseGradients

namespace CoreCouplingGlobal

noncomputable def responsePhi (H : ℝ) : ℝ :=
  2*(20001/10000)*H/(16+Real.sqrt (256+8*(20001/10000)*H))

theorem responsePhi_quadratic (H : ℝ) (hH : 0 ≤ H) :
    16*responsePhi H+2*(responsePhi H)^2 = (20001/10000)*H := by
  have hd : 0 ≤ 256+8*(20001/10000:ℝ)*H := by positivity
  have hs := Real.sq_sqrt hd
  have hn : 16+Real.sqrt (256+8*(20001/10000:ℝ)*H) ≠ 0 := by positivity
  dsimp [responsePhi]
  generalize Real.sqrt (256+8*(20001/10000:ℝ)*H) = t at hs hn ⊢
  field_simp
  linear_combination -10000*H*hs

theorem responsePhi_bounds (H : ℝ) (hH : 0 ≤ H) (hH' : H ≤ 1536/7) :
    0 ≤ responsePhi H ∧ responsePhi H ≤ 12 := by
  have hp : 0 ≤ responsePhi H := by dsimp [responsePhi]; positivity
  have hq := responsePhi_quadratic H hH
  exact ⟨hp,by nlinarith [sq_nonneg (responsePhi H-12)]⟩

/-- The H response gives a strictly dissipative gradient, including K=0. -/
theorem H_gradient_secant (H z : ℝ) (hH : 0 ≤ H) (hH' : H ≤ 1536/7)
    (hz : 0 ≤ z) (hz' : z ≤ 12) :
    ∃ n, 1/4000 ≤ n ∧
      3*(responseLog (responsePhi H)-responseLog z) =
        -n*(16*z+2*z^2-(20001/10000)*H) := by
  obtain ⟨hp,hp'⟩ := responsePhi_bounds H hH hH'
  obtain ⟨m,hm,_,heq⟩ := responseLog_secant z (responsePhi H) hz hz' hp hp'
  have hq := responsePhi_quadratic H hH
  have hd : 0 < 16+2*(z+responsePhi H) := by positivity
  refine ⟨3*m/(16+2*(z+responsePhi H)),?_,?_⟩
  · apply (le_div_iff₀ hd).2
    linarith
  · rw [heq]
    field_simp
    linear_combination 10000*hq

end CoreCouplingGlobal

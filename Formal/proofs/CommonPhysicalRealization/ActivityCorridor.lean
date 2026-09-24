import proofs.CommonPhysicalRealization.Supplies

namespace CommonPhysicalRealization
noncomputable section

theorem activity_ratio_bounds (rho aF aP eta : ℝ)
    (hr : 0 < rho) (hr1 : rho < 1) (he : 0 ≤ eta)
    (hf : 1-rho ≤ aF) (hf' : aF ≤ 1+rho)
    (hp : 1-rho ≤ aP) (hp' : aP ≤ 1+rho) :
    eta*((1-rho)/(1+rho)) ≤ eta*(aP/aF) ∧
      eta*(aP/aF) ≤ eta*((1+rho)/(1-rho)) := by
  have hf0 : 0 < aF := by linarith
  have hlo : (1-rho)/(1+rho) ≤ aP/aF :=
    div_le_div₀ (by linarith) hp (by linarith) hf'
  have hhi : aP/aF ≤ (1+rho)/(1-rho) :=
    div_le_div₀ (by linarith) hp' (by linarith) hf
  exact ⟨mul_le_mul_of_nonneg_left hlo he,mul_le_mul_of_nonneg_left hhi he⟩

theorem activity_force_bound (rho aF aP : ℝ)
    (hr : 0 < rho) (hr1 : rho < 1)
    (hf : 1-rho ≤ aF) (hf' : aF ≤ 1+rho)
    (hp : 1-rho ≤ aP) (hp' : aP ≤ 1+rho) :
    |Real.log (aF/aP)| ≤ Real.log ((1+rho)/(1-rho)) := by
  have hf0 : 0 < aF := by linarith
  have hp0 : 0 < aP := by linarith
  have ha := activity_ratio_bounds rho aF aP 1 hr hr1 (by norm_num) hf hf' hp hp'
  have hb := activity_ratio_bounds rho aP aF 1 hr hr1 (by norm_num) hp hp' hf hf'
  simp only [one_mul] at ha hb
  have hu := Real.log_le_log (div_pos hf0 hp0) hb.2
  have hl := Real.log_le_log (div_pos hp0 hf0) ha.2
  have heq : Real.log (aP/aF)= -Real.log (aF/aP) := by
    rw [Real.log_div (ne_of_gt hp0) (ne_of_gt hf0),Real.log_div (ne_of_gt hf0) (ne_of_gt hp0)]
    ring
  rw [heq] at hl
  exact abs_le.mpr ⟨by linarith,hu⟩

theorem bath_stock_sizing (R F P B rho : ℝ) (hR : 0 < R) (hr : 0 < rho)
    (hF : |F-R| ≤ B) (hP : |P-R| ≤ B) (hstock : B/rho ≤ R) :
    (1-rho ≤ F/R ∧ F/R ≤ 1+rho) ∧ (1-rho ≤ P/R ∧ P/R ≤ 1+rho) := by
  have hb : B ≤ rho*R := by have := (div_le_iff₀ hr).mp hstock; linarith
  exact ⟨stock_tolerance R F B rho hR hF hb,stock_tolerance R P B rho hR hP hb⟩

end
end CommonPhysicalRealization

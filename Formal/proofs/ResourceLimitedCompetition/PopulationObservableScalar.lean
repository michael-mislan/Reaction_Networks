import proofs.ResourceLimitedCompetition.PopulationLogBounds

namespace ResourceLimitedCompetition

noncomputable def oddsJumpH (N BH BL : ℝ) : ℝ :=
  (N/1000)*(-Real.log (1+1/BH)+(3/5)*Real.log (1+1/(BH+BL)))

noncomputable def oddsJumpL (N BH BL : ℝ) : ℝ :=
  (N/1000)*(Real.log (1+1/BL)+(3/5)*Real.log (1+1/(BH+BL)))

theorem exponential_two_jump_bound (rH rL vH vL : ℝ) (hH : 0 ≤ rH) (hL : 0 ≤ rL)
    (hvH : |vH| ≤ 1) (hvL : |vL| ≤ 1) :
    rH*(Real.exp vH-1)+rL*(Real.exp vL-1) ≤
      rH*vH+rL*vL+(rH*vH^2+rL*vL^2) := by
  have h1 := mul_le_mul_of_nonneg_left
    (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hvH)).2 hH
  have h2 := mul_le_mul_of_nonneg_left
    (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hvL)).2 hL
  nlinarith only [h1,h2]

theorem odds_jump_abs_bounds (N BH BL : ℝ) (hN : 1000 ≤ N) (hBH : N ≤ BH) (hBL : N ≤ BL) :
    |oddsJumpH N BH BL| ≤ 1/625 ∧ |oddsJumpL N BH BL| ≤ 1/625 ∧
      BH*|oddsJumpH N BH BL| ≤ N/625 ∧ BL*|oddsJumpL N BH BL| ≤ N/625 := by
  have hn : 0 < N := by linarith only [hN]
  have hbh : 0 < BH := hn.trans_le hBH
  have hbl : 0 < BL := hn.trans_le hBL
  obtain ⟨_,hh,hhn⟩ := membrane_log_bounds BH (hN.trans hBH)
  obtain ⟨_,hl,hln⟩ := membrane_log_bounds BL (hN.trans hBL)
  obtain ⟨_,hw,hwn⟩ := membrane_log_bounds (BH+BL) (by linarith only [hN,hBH,hBL])
  have hwH : BH*Real.log (1+1/(BH+BL)) ≤ 1 := by
    nlinarith only [hw,mul_nonneg hbl.le hwn]
  have hwL : BL*Real.log (1+1/(BH+BL)) ≤ 1 := by
    nlinarith only [hw,mul_nonneg hbh.le hwn]
  have habsH : |oddsJumpH N BH BL| ≤
      (N/1000)*(Real.log (1+1/BH)+(3/5)*Real.log (1+1/(BH+BL))) := by
    unfold oddsJumpH
    rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ N/1000)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (abs_add_le _ _).trans_eq (by rw [abs_neg,abs_of_nonneg hhn,abs_of_nonneg (by positivity)])
  have habsL : |oddsJumpL N BH BL| =
      (N/1000)*(Real.log (1+1/BL)+(3/5)*Real.log (1+1/(BH+BL))) := by
    unfold oddsJumpL
    apply abs_of_nonneg
    positivity
  have hweightedH : BH*|oddsJumpH N BH BL| ≤ N/625 := by
    have h := mul_le_mul_of_nonneg_left habsH hbh.le
    have h1 := mul_le_mul_of_nonneg_left hh hn.le
    have h2 := mul_le_mul_of_nonneg_left hwH hn.le
    nlinarith only [h,h1,h2]
  have hweightedL : BL*|oddsJumpL N BH BL| ≤ N/625 := by
    rw [habsL]
    have h1 := mul_le_mul_of_nonneg_left hl hn.le
    have h2 := mul_le_mul_of_nonneg_left hwL hn.le
    nlinarith only [h1,h2]
  have hsmallH : |oddsJumpH N BH BL| ≤ 1/625 := by
    have h := mul_le_mul_of_nonneg_right hBH (abs_nonneg (oddsJumpH N BH BL))
    apply le_of_mul_le_mul_left (a := N) _ hn
    nlinarith only [h,hweightedH]
  have hsmallL : |oddsJumpL N BH BL| ≤ 1/625 := by
    have h := mul_le_mul_of_nonneg_right hBL (abs_nonneg (oddsJumpL N BH BL))
    apply le_of_mul_le_mul_left (a := N) _ hn
    nlinarith only [h,hweightedL]
  exact ⟨hsmallH,hsmallL,hweightedH,hweightedL⟩

end ResourceLimitedCompetition

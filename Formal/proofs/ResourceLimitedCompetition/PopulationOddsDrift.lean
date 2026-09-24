import proofs.ResourceLimitedCompetition.PopulationObservableScalar

namespace ResourceLimitedCompetition

theorem population_jump_variance (N B a v : ℝ) (hB : 0 ≤ B) (ha : 0 ≤ a)
    (hamax : a ≤ 3) (hv : |v| ≤ 1/625) (hweighted : B*|v| ≤ N/625) :
    a*B*v^2 ≤ 3*N/390625 := by
  have hsq : v^2 ≤ (1/625)*|v| := by
    calc
      v^2 = |v| * |v| := by rw [← pow_two,sq_abs]
      _ ≤ (1/625)*|v| := mul_le_mul_of_nonneg_right hv (abs_nonneg v)
  have hr := mul_le_mul_of_nonneg_left hsq (mul_nonneg ha hB)
  have hb := mul_le_mul_of_nonneg_right hamax (mul_nonneg hB (abs_nonneg v))
  nlinarith only [hr,hb,hweighted]

theorem population_odds_scalar_drift (N BH BL aH aL : ℝ)
    (hN : 1000 ≤ N) (hBH : N ≤ BH) (hBL : N ≤ BL)
    (haH : (297/100 : ℝ) ≤ aH ∧ aH ≤ 3)
    (haL : (99/100 : ℝ) ≤ aL ∧ aL ≤ 101/100) :
    aH*BH*(Real.exp (oddsJumpH N BH BL)-1)+
      aL*BL*(Real.exp (oddsJumpL N BH BL)-1) ≤ 0 := by
  have hn : 0 ≤ N := by linarith only [hN]
  have hbh : 0 ≤ BH := hn.trans hBH
  have hbl : 0 ≤ BL := hn.trans hBL
  have hh : 0 ≤ aH := by linarith only [haH.1]
  have hl : 0 ≤ aL := by linarith only [haL.1]
  obtain ⟨hvH,hvL,hwH,hwL⟩ := odds_jump_abs_bounds N BH BL hN hBH hBL
  have hvarH := population_jump_variance N BH aH (oddsJumpH N BH BL) hbh hh haH.2 hvH hwH
  have hvarL := population_jump_variance N BL aL (oddsJumpL N BH BL) hbl hl
    (by linarith only [haL.2]) hvL hwL
  obtain ⟨hrel,htotal,_⟩ := population_log_drift BH BL aH aL (hN.trans hBH) (hN.trans hBL) haH haL
  have hlinear : aH*BH*oddsJumpH N BH BL+aL*BL*oddsJumpL N BH BL ≤ -3*N/20000 := by
    have h1 := mul_le_mul_of_nonneg_left hrel hn
    have h2 := mul_le_mul_of_nonneg_left htotal hn
    unfold oddsJumpH oddsJumpL
    nlinarith only [h1,h2]
  have h := exponential_two_jump_bound (aH*BH) (aL*BL) (oddsJumpH N BH BL) (oddsJumpL N BH BL)
    (mul_nonneg hh hbh) (mul_nonneg hl hbl)
    (hvH.trans (by norm_num)) (hvL.trans (by norm_num))
  nlinarith only [h,hlinear,hvarH,hvarL,hn]

end ResourceLimitedCompetition

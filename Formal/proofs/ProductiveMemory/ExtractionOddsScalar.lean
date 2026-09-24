import proofs.ResourceLimitedCompetition.PopulationOddsDrift
import proofs.ResourceLimitedCompetition.DeadlineScalar

namespace ProductiveMemory
open ResourceLimitedCompetition
set_option Elab.async false

theorem extraction_population_log_drift (BH BL aH aL : ℝ) (hBH : 1000 ≤ BH) (hBL : 1000 ≤ BL)
    (haH : (288/100 : ℝ) ≤ aH ∧ aH ≤ 3)
    (haL : (97/100 : ℝ) ≤ aL ∧ aL ≤ 1) :
    (187/100 : ℝ) ≤ aH*BH*Real.log (1+1/BH)-aL*BL*Real.log (1+1/BL) ∧
      (aH*BH+aL*BL)*Real.log (1+1/(BH+BL)) ≤ 3 ∧
      (24/25 : ℝ) ≤ (aH*BH+aL*BL)*Real.log (1+1/(BH+BL)) := by
  obtain ⟨hh,hhmax,_⟩ := membrane_log_bounds BH hBH
  obtain ⟨_,hlmax,hlnon⟩ := membrane_log_bounds BL hBL
  obtain ⟨hw,hwmax,hwnon⟩ := membrane_log_bounds (BH+BL) (by linarith only [hBH,hBL])
  have hBhpos : 0 ≤ BH := by linarith only [hBH]
  have hBlpos : 0 ≤ BL := by linarith only [hBL]
  have hH := mul_le_mul haH.1 hh (by norm_num : (0:ℝ) ≤ 999/1000) (by linarith only [haH.1])
  have hL := mul_le_mul haL.2 hlmax (mul_nonneg hBlpos hlnon) (by norm_num : (0:ℝ) ≤ 1)
  have hupper : aH*BH+aL*BL ≤ 3*(BH+BL) := by
    have h1 := mul_le_mul_of_nonneg_right haH.2 hBhpos
    have h2 := mul_le_mul_of_nonneg_right haL.2 hBlpos
    nlinarith only [h1,h2,hBlpos]
  have hlower : (97/100 : ℝ)*(BH+BL) ≤ aH*BH+aL*BL := by
    have h1 := mul_le_mul_of_nonneg_right haH.1 hBhpos
    have h2 := mul_le_mul_of_nonneg_right haL.1 hBlpos
    nlinarith only [h1,h2,hBhpos]
  have hWU := mul_le_mul_of_nonneg_right hupper hwnon
  have hWL := mul_le_mul_of_nonneg_right hlower hwnon
  constructor
  · nlinarith only [hH,hL]
  constructor
  · nlinarith only [hWU,hwmax]
  · nlinarith only [hWL,hw]

theorem extraction_odds_scalar_drift (N BH BL aH aL : ℝ)
    (hN : 1000 ≤ N) (hBH : N ≤ BH) (hBL : N ≤ BL)
    (haH : (288/100 : ℝ) ≤ aH ∧ aH ≤ 3)
    (haL : (97/100 : ℝ) ≤ aL ∧ aL ≤ 1) :
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
  obtain ⟨hrel,htotal,_⟩ := extraction_population_log_drift BH BL aH aL (hN.trans hBH) (hN.trans hBL) haH haL
  have hlinear : aH*BH*oddsJumpH N BH BL+aL*BL*oddsJumpL N BH BL ≤ -7*N/100000 := by
    have h1 := mul_le_mul_of_nonneg_left hrel hn
    have h2 := mul_le_mul_of_nonneg_left htotal hn
    unfold oddsJumpH oddsJumpL
    nlinarith only [h1,h2]
  have h := exponential_two_jump_bound (aH*BH) (aL*BL) (oddsJumpH N BH BL) (oddsJumpL N BH BL)
    (mul_nonneg hh hbh) (mul_nonneg hl hbl)
    (hvH.trans (by norm_num)) (hvL.trans (by norm_num))
  nlinarith only [h,hlinear,hvarH,hvarL,hn]

theorem extraction_deadline_scalar_drift (N W R : ℝ) (hN : 1000 ≤ N) (hW : N ≤ W)
    (hRmin : (97/100)*W ≤ R) (hRmax : R ≤ 3*W) :
    R*(Real.exp (deadlineJump N W)-1) ≤ -(9/10000)*N := by
  have hn : 0 < N := by linarith only [hN]
  have hw : 0 < W := hn.trans_le hW
  have hr : 0 ≤ R := by linarith only [hRmin,hw]
  obtain ⟨hlogmin,hlogmax,hlognon⟩ := membrane_log_bounds W (hN.trans hW)
  have habs : |deadlineJump N W|=(N/1000)*Real.log (1+1/W) := by
    unfold deadlineJump
    rw [neg_mul,abs_neg,abs_of_nonneg (by positivity)]
  have hweighted : W*|deadlineJump N W| ≤ N/1000 := by
    rw [habs]
    have h := mul_le_mul_of_nonneg_left hlogmax hn.le
    nlinarith only [h]
  have hsmall : |deadlineJump N W| ≤ 1/1000 := by
    have h := mul_le_mul_of_nonneg_right hW (abs_nonneg (deadlineJump N W))
    apply le_of_mul_le_mul_left (a := N) _ hn
    nlinarith only [h,hweighted]
  have hlinear : R*deadlineJump N W ≤ -(24/25000)*N := by
    have h1 := mul_le_mul_of_nonneg_right hRmin hlognon
    have h2 : (24/25 : ℝ) ≤ R*Real.log (1+1/W) := by nlinarith only [h1,hlogmin]
    have h3 := mul_le_mul_of_nonneg_left h2 hn.le
    unfold deadlineJump
    nlinarith only [h3]
  have hsq : (deadlineJump N W)^2 ≤ (1/1000)*|deadlineJump N W| := by
    calc
      (deadlineJump N W)^2 = |deadlineJump N W| * |deadlineJump N W| := by rw [← pow_two,sq_abs]
      _ ≤ (1/1000)*|deadlineJump N W| :=
        mul_le_mul_of_nonneg_right hsmall (abs_nonneg (deadlineJump N W))
  have hvar : R*(deadlineJump N W)^2 ≤ 3*N/1000000 := by
    have h1 := mul_le_mul_of_nonneg_left hsq hr
    have h2 := mul_le_mul_of_nonneg_right hRmax (abs_nonneg (deadlineJump N W))
    nlinarith only [h1,h2,hweighted]
  have ht := mul_le_mul_of_nonneg_left
    (abs_le.mp (Real.abs_exp_sub_one_sub_id_le (hsmall.trans (by norm_num)))).2 hr
  nlinarith only [ht,hlinear,hvar,hn]


end ProductiveMemory

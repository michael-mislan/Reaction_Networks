import proofs.ResourceLimitedCompetition.PopulationLogBounds

namespace ResourceLimitedCompetition

noncomputable def deadlineJump (N W : ℝ) : ℝ := -(N/1000)*Real.log (1+1/W)

theorem deadline_scalar_drift (N W R : ℝ) (hN : 1000 ≤ N) (hW : N ≤ W)
    (hRmin : (99/100)*W ≤ R) (hRmax : R ≤ 3*W) :
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
  have hlinear : R*deadlineJump N W ≤ -(49/50000)*N := by
    have h1 := mul_le_mul_of_nonneg_right hRmin hlognon
    have h2 : (49/50 : ℝ) ≤ R*Real.log (1+1/W) := by nlinarith only [h1,hlogmin]
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

end ResourceLimitedCompetition

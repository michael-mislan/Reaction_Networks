import proofs.ResourceLimitedCompetition.PopulationOddsDrift

namespace SerialTransferSelection
open ResourceLimitedCompetition

/-- Rate investigation: an actual discrete scalar generator bound, not yet a source mission theorem. -/
theorem minority_growth_scalar_barrier (N H L aH aL : ℝ)
    (hN : 1000 ≤ N) (hH : N ≤ H) (hL : N ≤ L)
    (haH : (297/100 : ℝ) ≤ aH ∧ aH ≤ 3)
    (haL : (99/100 : ℝ) ≤ aL ∧ aL ≤ 101/100) :
    let vH := (N/1000)*((8/25)*Real.log (1+1/(H+L)))
    let vL := (N/1000)*(-Real.log (1+1/L)+(8/25)*Real.log (1+1/(H+L)))
    aH*H*(Real.exp vH-1)+aL*L*(Real.exp vL-1) ≤ 0 := by
  dsimp only
  let vH := (N/1000)*((8/25)*Real.log (1+1/(H+L)))
  let vL := (N/1000)*(-Real.log (1+1/L)+(8/25)*Real.log (1+1/(H+L)))
  change aH*H*(Real.exp vH-1)+aL*L*(Real.exp vL-1) ≤ 0
  have hn : 0 < N := by linarith
  have hh : 0 < H := hn.trans_le hH
  have hl : 0 < L := hn.trans_le hL
  have hah : 0 ≤ aH := by linarith [haH.1]
  have hal : 0 ≤ aL := by linarith [haL.1]
  obtain ⟨hll,hlu,hln⟩ := membrane_log_bounds L (hN.trans hL)
  obtain ⟨_,hwu,hwn⟩ := membrane_log_bounds (H+L) (by linarith)
  have hwh : H*Real.log (1+1/(H+L)) ≤ 1 := by nlinarith [mul_nonneg hl.le hwn]
  have hwl : L*Real.log (1+1/(H+L)) ≤ 1 := by nlinarith [mul_nonneg hh.le hwn]
  have habH : |vH|=(N/1000)*((8/25)*Real.log (1+1/(H+L))) := by
    dsimp [vH]
    apply abs_of_nonneg
    positivity
  have habL : |vL| ≤ (N/1000)*(Real.log (1+1/L)+(8/25)*Real.log (1+1/(H+L))) := by
    dsimp [vL]
    rw [abs_mul,abs_of_pos (by positivity : 0 < N/1000)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (abs_add_le _ _).trans_eq (by rw [abs_neg,abs_of_nonneg hln,abs_of_nonneg (by positivity)])
  have hwH : H*|vH| ≤ N/625 := by
    rw [habH]
    have h := mul_le_mul_of_nonneg_left hwh hn.le
    nlinarith
  have hwL : L*|vL| ≤ N/625 := by
    have h := mul_le_mul_of_nonneg_left habL hl.le
    have h1 := mul_le_mul_of_nonneg_left hlu hn.le
    have h2 := mul_le_mul_of_nonneg_left hwl hn.le
    nlinarith
  have hvH : |vH| ≤ 1/625 := by
    have h := mul_le_mul_of_nonneg_right hH (abs_nonneg vH)
    nlinarith
  have hvL : |vL| ≤ 1/625 := by
    have h := mul_le_mul_of_nonneg_right hL (abs_nonneg vL)
    nlinarith
  have hvarH := population_jump_variance N H aH vH hh.le hah haH.2 hvH hwH
  have hvarL := population_jump_variance N L aL vL hl.le hal (by linarith [haL.2]) hvL hwL
  have htotal := (population_log_drift H L aH aL (hN.trans hH) (hN.trans hL) haH haL).2.1
  have hlow := mul_le_mul haL.1 hll (by norm_num : (0 : ℝ) ≤ 999/1000) hal
  have hlinear : aH*H*vH+aL*L*vL ≤ -(2901/100000000)*N := by
    have ht := mul_le_mul_of_nonneg_left htotal hn.le
    have hb := mul_le_mul_of_nonneg_left hlow hn.le
    dsimp [vH,vL]
    nlinarith only [ht,hb]
  have he := exponential_two_jump_bound (aH*H) (aL*L) vH vL (by positivity) (by positivity)
    (hvH.trans (by norm_num)) (hvL.trans (by norm_num))
  nlinarith only [he,hlinear,hvarH,hvarL,hn]

end SerialTransferSelection

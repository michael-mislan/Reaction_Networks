import proofs.ProductiveRecovery.Source

namespace ProductiveRecovery
noncomputable section

theorem guarded_growth (r d : ℝ) (c : State) (hc : Nonneg c)
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (hA : 9/10 ≤ A c) (hB : 9/10 ≤ B c) (hY : Y c ≤ 1/2500) :
    (2/3)*Y c ≤ Y (field r d c) := by
  obtain ⟨ha, hb, hx⟩ := material_to_food c hc
  have hu : 10117/11250 ≤ c 0 := by linarith
  have hw : 787/875 ≤ c 1 := by linarith
  have hx' : c 2 ≤ 1/2500 := hx.trans hY
  have hxx : c 2^2 ≤ (1/2500)*c 2 := by
    nlinarith [mul_nonneg (hc 2) (sub_nonneg.mpr hx')]
  have him : 0 ≤ ((1/500000000)+d*(1/8000000000))*c 0*c 1 :=
    mul_nonneg (mul_nonneg (by positivity) (hc 0)) (hc 1)
  have hu' := mul_nonneg (sub_nonneg.mpr hu) (hc 2)
  have hw' := mul_nonneg (sub_nonneg.mpr hw) (hc 3)
  have hd'' := mul_nonneg (sub_nonneg.mpr hd') (hc 2)
  have hrlo := mul_nonneg (sub_nonneg.mpr hr) (hc 5)
  have hrhi := mul_nonneg (sub_nonneg.mpr hr') (sq_nonneg (c 2))
  rw [weighted_drift]
  dsimp [Y]
  nlinarith [hc 2, hc 3, hc 4]

theorem global_positive_drift_false :
    Y (field 19 (1/25) ![0,0,1,0,0,0]) < 0 := by
  rw [weighted_drift]
  change ((1/500000000:ℝ)+(1/25)*(1/8000000000))*0*0 +
    ((5/2)*0-1-(1/25)-(1/5000000000))*1 +
    ((11/2)*0-(29/8))*0 + (11/10)*0 + (19/5-13/5)*0 - (19/5)*1^2 < 0
  norm_num

theorem gross_service_bound (d : ℝ) (c : State) (hc : Nonneg c)
    (hd' : d ≤ 1/25) (hA : A c ≤ 11/10) (hB : B c ≤ 11/10) :
    d*c 2+d*(1/8000000000)*c 0*c 1 ≤ 9/200 := by
  have hu : c 0 ≤ 11/10 := by
    dsimp [A] at hA
    linarith [hc 2,hc 3,hc 4,hc 5]
  have hw : c 1 ≤ 11/10 := by
    dsimp [B] at hB
    linarith [hc 2,hc 3,hc 4,hc 5]
  have hx : c 2 ≤ 11/10 := by
    dsimp [A] at hA
    linarith [hc 0,hc 3,hc 4,hc 5]
  have huw : c 0*c 1 ≤ (11/10)*(11/10) := mul_le_mul hu hw (hc 1) (by norm_num)
  have hx' := mul_le_mul hd' hx (hc 2) (by norm_num : (0:ℝ) ≤ 1/25)
  have hs := mul_le_mul hd' huw (mul_nonneg (hc 0) (hc 1)) (by norm_num : (0:ℝ) ≤ 1/25)
  nlinarith

end
end ProductiveRecovery

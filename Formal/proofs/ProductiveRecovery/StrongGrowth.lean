import proofs.ProductiveRecovery.WeightedGrowth

namespace ProductiveRecovery
noncomputable section

theorem parameterized_drift (r d beta : ℝ) (c : State) (hc : Nonneg c)
    (hr' : r ≤ 21) (hd' : d ≤ 1/25)
    (hA : 9/10 ≤ A c) (hB : 9/10 ≤ B c) (hY : Y c ≤ beta) :
    ((1/500000000)+d*(1/8000000000))*c 0*c 1 +
      (163/300-1/5000000000-(389/45)*beta)*c 2 +
      (23/40-(55/7)*beta)*c 3 + (1/6)*c 4 + (r/5-19/5)*c 5 ≤
      Y (field r d c) - (2/3)*Y c := by
  obtain ⟨ha,hb,hx⟩ := material_to_food c hc
  have hu : 9/10-(16/9)*beta ≤ c 0 := by linarith
  have hw : 9/10-(10/7)*beta ≤ c 1 := by linarith
  have hxx : c 2^2 ≤ beta*c 2 := by
    nlinarith [mul_nonneg (hc 2) (sub_nonneg.mpr (hx.trans hY))]
  have hu' := mul_nonneg (sub_nonneg.mpr hu) (hc 2)
  have hw' := mul_nonneg (sub_nonneg.mpr hw) (hc 3)
  have hd'' := mul_nonneg (sub_nonneg.mpr hd') (hc 2)
  have hrhi := mul_nonneg (sub_nonneg.mpr hr') (sq_nonneg (c 2))
  rw [weighted_drift]
  dsimp [Y]
  nlinarith

theorem strong_guarded_growth (r d : ℝ) (c : State) (hc : Nonneg c)
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (hA : 9/10 ≤ A c) (hB : 9/10 ≤ B c) (hY : Y c ≤ 1/20) :
    (2/3)*Y c ≤ Y (field r d c) := by
  obtain ⟨ha, hb, hx⟩ := material_to_food c hc
  have hu : 73/90 ≤ c 0 := by linarith
  have hw : 29/35 ≤ c 1 := by linarith
  have hx' : c 2 ≤ 1/20 := hx.trans hY
  have hxx : c 2^2 ≤ (1/20)*c 2 := by
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


end
end ProductiveRecovery

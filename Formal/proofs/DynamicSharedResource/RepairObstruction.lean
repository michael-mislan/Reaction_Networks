import proofs.DynamicSharedResource.Model

namespace DynamicSharedResource
noncomputable section

theorem repair_velocity_lower (s sigma : ℝ) (hs : 0 ≤ sigma)
    (u : State) (hu : Physical u) :
    -(sigma*(3/1000))*u 6 ≤ field s sigma u 6 := by
  have hh : 0 ≤ u 5 := hu.2.2.2.2.2.2.2.2.2.2.1
  have hp : 0 ≤ sigma*(9/12500)*u 5 :=
    mul_nonneg (mul_nonneg hs (by norm_num)) hh
  simp [field, thetaW, thetaH]
  nlinarith

theorem stationary_matched_rates (s sigma : ℝ) (hs : sigma ≠ 0)
    (u : State) : field s sigma u = 0 ↔ field s 1 u = 0 := by
  have hw : thetaW sigma u-thetaH sigma u =
      sigma*(thetaW 1 u-thetaH 1 u) := by
    unfold thetaW thetaH
    ring
  have he (h : thetaW 1 u-thetaH 1 u=0) : field s sigma u=field s 1 u := by
    have h1 : thetaW 1 u = thetaH 1 u := sub_eq_zero.mp h
    have h2 : thetaW sigma u = thetaH sigma u := by
      apply sub_eq_zero.mp
      rw [hw,h,mul_zero]
    simp [field,h1,h2]
  constructor
  · intro hz
    have hz6 := congrFun hz 6
    change thetaW sigma u-thetaH sigma u=0 at hz6
    have h : thetaW 1 u-thetaH 1 u=0 :=
      (mul_eq_zero.mp (hw.symm.trans hz6)).resolve_left hs
    rw [← he h]
    exact hz
  · intro hz
    have h := congrFun hz 6
    change thetaW 1 u-thetaH 1 u=0 at h
    rw [he h]
    exact hz

theorem repair_integrating_factor_nonneg (k : ℝ) (w : ℝ → ℝ)
    (t dw : ℝ) (hd : HasDerivAt w dw t) (hl : -k*w t ≤ dw) :
    0 ≤ deriv (fun t => Real.exp (k*t)*w t) t := by
  have he : HasDerivAt (fun t : ℝ => Real.exp (k*t)) (Real.exp (k*t)*k) t := by
    simpa using ((hasDerivAt_id t).const_mul k).exp
  have hew : HasDerivAt (fun t => Real.exp (k*t)*w t)
      (Real.exp (k*t)*k*w t+Real.exp (k*t)*dw) t := he.mul hd
  rw [hew.deriv]
  have hp := mul_nonneg (Real.exp_pos (k*t)).le (show 0 ≤ k*w t+dw by linarith)
  nlinarith

end
end DynamicSharedResource

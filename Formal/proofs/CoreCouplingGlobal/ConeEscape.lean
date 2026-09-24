import proofs.CoreCouplingGlobal.ScalarBarrier

namespace CoreCouplingGlobal

/-- A negative quadratic displacement cannot stay bounded while it dissipates
strictly relative to the squared displacement norm. No asymptotic theorem is used. -/
theorem negative_quadratic_not_globally_bounded (q dq N : ℝ → ℝ) (M η C : ℝ)
    (hM : 0 < M) (hη : 0 < η) (hC : 0 ≤ C)
    (hd : ∀ t, 0 ≤ t → HasDerivAt q (dq t) t)
    (hN : ∀ t, 0 ≤ t → 0 ≤ N t)
    (hscale : ∀ t, 0 ≤ t → -M*N t ≤ q t)
    (hdec : ∀ t, 0 ≤ t → dq t ≤ -η*N t)
    (hbounded : ∀ t, 0 ≤ t → -C ≤ q t) (h0 : q 0 < 0) : False := by
  have hupper : ∀ t, 0 ≤ t → q t ≤ q 0 := by
    apply scalar_upper_barrier q dq (q 0) hd (by rfl)
    intro t ht _
    have hn := mul_nonneg hη.le (hN t ht)
    have hh := hdec t ht
    linarith
  let κ := η*(-q 0)/M
  have hκ : 0 < κ := div_pos (mul_pos hη (neg_pos.mpr h0)) hM
  have hκM : κ*M = η*(-q 0) := by dsimp [κ]; field_simp
  have hrate : ∀ t, 0 ≤ t → dq t ≤ -κ := by
    intro t ht
    have hs := hscale t ht
    have hu := hupper t ht
    have hn : -q 0 ≤ M*N t := by linarith
    have hnη := mul_le_mul_of_nonneg_left hn hη.le
    have hdM := mul_le_mul_of_nonneg_right (hdec t ht) hM.le
    nlinarith
  have hlinear : ∀ t, 0 ≤ t → q t+κ*t ≤ q 0 := by
    apply scalar_upper_barrier (fun t => q t+κ*t) (fun t => dq t+κ) (q 0)
      (fun t ht => (hd t ht).add (by simpa only [mul_one] using (hasDerivAt_id t).const_mul κ)) (by simp)
    intro t ht _
    have hh := hrate t ht
    linarith
  let T := (C+1)/κ
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hκT : κ*T = C+1 := by dsimp [T]; field_simp
  have hlow := hbounded T hT
  have hupp := hlinear T hT
  rw [hκT] at hupp
  linarith

/-- Application form: a trajectory pair starting in the negative cone must
leave any region carrying the stated uniform quadratic bounds. -/
theorem negative_cone_forces_exit (q dq N : ℝ → ℝ) (P : ℝ → Prop) (M η C : ℝ)
    (hM : 0 < M) (hη : 0 < η) (hC : 0 ≤ C)
    (hd : ∀ t, 0 ≤ t → HasDerivAt q (dq t) t)
    (hN : ∀ t, 0 ≤ t → 0 ≤ N t)
    (hscale : ∀ t, 0 ≤ t → P t → -M*N t ≤ q t)
    (hdec : ∀ t, 0 ≤ t → P t → dq t ≤ -η*N t)
    (hbounded : ∀ t, 0 ≤ t → P t → -C ≤ q t) (h0 : q 0 < 0) :
    ∃ t : ℝ, 0 ≤ t ∧ ¬P t := by
  by_contra hn
  push Not at hn
  exact negative_quadratic_not_globally_bounded q dq N M η C hM hη hC hd hN
    (fun t ht => hscale t ht (hn t ht)) (fun t ht => hdec t ht (hn t ht))
    (fun t ht => hbounded t ht (hn t ht)) h0

end CoreCouplingGlobal

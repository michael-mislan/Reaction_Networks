import proofs.RAF1519.Refinement.CountSource

namespace RAF1519.Refinement
noncomputable section

theorem refined_weighted_drift (r d beta theta : ℝ) (c : State) :
    stock (field r d beta theta c) =
      (1/500000000)*c 0*c 1 +
      ((5/2)*c 0-1-d*(1+beta)-(1/5000000000))*c 2 +
      ((11/2)*c 1-(29/8))*c 3 + (11/10)*c 4 +
      (r/5-13/5)*c 5-(r/5)*c 2^2+d*beta/theta*c 6 := by
  simp [stock,field,ProductiveRecovery.Y,ProductiveRecovery.flux,
    free,firstFlux]; ring

theorem guarded_growth (r d theta : ℝ) (c : State) (hc : ∀ i, 0 ≤ c i)
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (ht : 0 ≤ theta) (hA : 9/10 ≤ ProductiveRecovery.A (free c))
    (hB : 9/10 ≤ ProductiveRecovery.B (free c)) (hY : stock c ≤ 3/50) :
    (2/3)*stock c ≤ stock (field r d (1/100) theta c) := by
  have hfree : ProductiveRecovery.Nonneg (free c) := by
    intro i; fin_cases i <;> simpa [free] using hc _
  obtain ⟨ha,hb,hx⟩ := ProductiveRecovery.material_to_food (free c) hfree
  change ProductiveRecovery.A (free c)-c 0 ≤ (16/9)*stock c at ha
  change ProductiveRecovery.B (free c)-c 1 ≤ (10/7)*stock c at hb
  change c 2 ≤ stock c at hx
  have hu : 119/150 ≤ c 0 := by linarith
  have hw : 57/70 ≤ c 1 := by linarith
  have hx' : c 2 ≤ 3/50 := by linarith
  have hxx : c 2^2 ≤ (3/50)*c 2 := by
    nlinarith [mul_nonneg (hc 2) (sub_nonneg.mpr hx')]
  have him : 0 ≤ (1/500000000:ℝ)*c 0*c 1 :=
    mul_nonneg (mul_nonneg (by norm_num) (hc 0)) (hc 1)
  have hret : 0 ≤ d*(1/100)/theta*c 6 :=
    mul_nonneg (div_nonneg (mul_nonneg hd (by norm_num)) ht) (hc 6)
  have hu' := mul_nonneg (sub_nonneg.mpr hu) (hc 2)
  have hw' := mul_nonneg (sub_nonneg.mpr hw) (hc 3)
  have hd'' := mul_nonneg (sub_nonneg.mpr hd') (hc 2)
  have hrlo := mul_nonneg (sub_nonneg.mpr hr) (hc 5)
  have hrhi := mul_nonneg (sub_nonneg.mpr hr') (sq_nonneg (c 2))
  rw [refined_weighted_drift]
  dsimp [stock,free,ProductiveRecovery.Y]
  nlinarith [hc 2,hc 3,hc 4]

theorem count_guarded_growth (r d V : ℝ) (c : State) (hc : ∀ i, 0 ≤ c i)
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (hV : 0 ≤ V) (hA : 9/10 ≤ ProductiveRecovery.A (free c))
    (hB : 9/10 ≤ ProductiveRecovery.B (free c)) (hY : stock c ≤ 3/50) :
    (2/3)*stock c ≤ stock (countDrift r d (1/100) (1/100) V c) := by
  rw [count_stock_correction]
  have hg := guarded_growth r d (1/100) c hc hr hr' hd hd' (by norm_num) hA hB hY
  have hp : 0 ≤ r*c 2/(5*V) := by
    exact div_nonneg (mul_nonneg (by linarith) (hc 2)) (mul_nonneg (by norm_num) hV)
  linarith
end
end RAF1519.Refinement

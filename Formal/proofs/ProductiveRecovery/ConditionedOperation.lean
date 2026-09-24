import proofs.ProductiveRecovery.StrongRepeated

namespace ProductiveRecovery
noncomputable section
open MeasureTheory Set

def serviceOver (d T : ℝ) (X : ℝ → State) : ℝ :=
  ∫ t in (0:ℝ)..T, d*X t 2+d*(1/8000000000)*X t 0*X t 1

theorem service_over_bound (r d T : ℝ) (hT : 0 ≤ T) (hd' : d ≤ 1/25)
    (X : ℝ → State) (hn : ∀ t, 0 ≤ t → Nonneg (X t))
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (field r d (X t)) t)
    (hcor : ∀ t, 0 ≤ t → A (X t) ≤ 11/10 ∧ B (X t) ≤ 11/10) :
    serviceOver d T X ≤ (9/200)*T := by
  have hg : Continuous (fun c : State => d*c 2+d*(1/8000000000)*c 0*c 1) := by fun_prop
  have hi : IntervalIntegrable (fun t => d*X t 2+d*(1/8000000000)*X t 0*X t 1) volume 0 T :=
    (hg.comp_continuousOn (show ContinuousOn X (Icc 0 T) from
      fun t ht => (hX t ht.1).continuousAt.continuousWithinAt)).intervalIntegrable_of_Icc hT
  have h := intervalIntegral.integral_mono_on hT hi
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (9/200:ℝ)) volume 0 T)
    (fun t ht => gross_service_bound d (X t) (hn t ht.1) hd' (hcor t ht.1).1 (hcor t ht.1).2)
  norm_num at h
  dsimp [serviceOver]
  nlinarith

theorem exists_conditioning (r d : ℝ) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 1/50 ≤ d) (hd' : d ≤ 1/25) (p : Intervention) (c : State) (hc : Admitted c) :
    ∃ X : ℝ → State, X 0 = pulse p c ∧
      (∀ t, 0 ≤ t → Nonneg (X t)) ∧
      (∀ t, 0 ≤ t → HasDerivAt X (field r d (X t)) t) ∧
      StrongReturned (X 12) ∧
      12+(1-p.q+p.eU) ≤ 2551/200 ∧ 12+(1-p.q+p.eW) ≤ 2551/200 ∧
      serviceOver d 12 X ≤ 27/50 := by
  obtain ⟨X,h0,hn,hX,hcor,_⟩ := exists_actual_return r d hr hr' (by linarith) hd' p c hc
  have hret := conditioning_return r d hr hr' (by linarith) hd' p c hc X h0 hn hX 12 le_rfl
  have hg := service_over_bound r d 12 (by norm_num) hd' X hn hX
    (fun t ht => ⟨(hcor t ht).1.2,(hcor t ht).2.2⟩)
  obtain ⟨_,hu,_,hw⟩ := food_feasible p
  exact ⟨X,h0,hn,hX,hret,by linarith,by linarith,by linarith⟩

end
end ProductiveRecovery

import proofs.DynamicSharedResource.OperationalCosts

namespace DynamicSharedResource.Certificate
noncomputable section
open Set MeasureTheory

theorem operational_account (u : ℝ → State)
    (h0 : InRect recoveryR (coordinates (u 0)))
    (hu : ∀ t, 0 ≤ t → HasDerivAt u (nominal (u t)) t)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, regen (3/25) (u t 0)) =
      (∫ t in a..b, HG (u t))+(∫ t in a..b, HT (u t))+W (u b)-W (u a) := by
  have hp := (every_fast_source_trajectory u h0 hu).1
  have hc : ContinuousOn u (Icc a b) := fun t ht =>
    (hu t (ha.trans ht.1)).continuousAt.continuousWithinAt
  have hR : ContinuousOn (fun t => regen (3/25) (u t 0)) (Icc a b) := by
    intro t ht
    have hd : 873/10-u t 0 ≠ 0 := by
      have hh := denominator_separated (u t) (hp t (ha.trans ht.1)).1
      linarith
    have hs : ContinuousAt (fun x : State => regen (3/25) (x 0)) (u t) := by
      unfold regen
      fun_prop (disch := assumption)
    exact (hs.comp (hu t (ha.trans ht.1)).continuousAt).continuousWithinAt
  have hG : Continuous HG := by unfold HG e0; fun_prop
  have hTr : Continuous HT := by unfold HT y; fun_prop
  have ir : IntervalIntegrable (fun t => regen (3/25) (u t 0)) volume a b :=
    hR.intervalIntegrable_of_Icc hab
  have ig : IntervalIntegrable (fun t => HG (u t)) volume a b :=
    (hG.comp_continuousOn hc).intervalIntegrable_of_Icc hab
  have it : IntervalIntegrable (fun t => HT (u t)) volume a b :=
    (hTr.comp_continuousOn hc).intervalIntegrable_of_Icc hab
  have hid : (∫ t in a..b, regen (3/25) (u t 0)-HG (u t)-HT (u t))=W (u b)-W (u a) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [uIcc_of_le hab] at ht
      exact resource_hasDerivAt (3/25) 1 u t (hu t (ha.trans ht.1))
    · exact (ir.sub ig).sub it
  rw [intervalIntegral.integral_sub (ir.sub ig) it,intervalIntegral.integral_sub ir ig] at hid
  linarith

theorem regeneration_expenditure (u : ℝ → State)
    (h0 : InRect recoveryR (coordinates (u 0)))
    (hu : ∀ t, 0 ≤ t → HasDerivAt u (nominal (u t)) t)
    (a T : ℝ) (ha : 1/250 ≤ a) (hT : 0 ≤ T) :
    (359/25)*T-1/10 ≤ ∫ t in a..(a+T), regen (3/25) (u t 0) := by
  have hw := operational_windows u h0 hu a T ha hT
  have hs := (every_fast_source_trajectory u h0 hu).2
  have hr := storage_range (coordinates (u (a+T))) (coordinates (u a))
    (hs (a+T) (by linarith)).1 (hs a ha).1
  simp only [reconstruct_coordinates] at hr
  have hi := operational_account u h0 hu a (a+T) (by linarith) (by linarith)
  have hb := abs_le.mp hr
  linarith

theorem necessary_mission_budget (u : ℝ → State)
    (h0 : InRect recoveryR (coordinates (u 0)))
    (hu : ∀ t, 0 ≤ t → HasDerivAt u (nominal (u t)) t)
    (a T B : ℝ) (ha : 1/250 ≤ a) (hT : 0 ≤ T)
    (hB : (∫ t in a..(a+T), regen (3/25) (u t 0)) ≤ B) :
    T ≤ (B+1/10)/(359/25) := by
  have h := regeneration_expenditure u h0 hu a T ha hT
  apply (le_div_iff₀ (by norm_num : (0:ℝ) < 359/25)).mpr
  linarith

end
end DynamicSharedResource.Certificate

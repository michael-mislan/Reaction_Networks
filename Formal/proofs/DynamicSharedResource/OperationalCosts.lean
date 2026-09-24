import proofs.DynamicSharedResource.OperationalCore
import proofs.DynamicSharedResource.StorageBounds

namespace DynamicSharedResource.Certificate
noncomputable section
open Set MeasureTheory

theorem operational_windows (u : ℝ → State)
    (h0 : InRect recoveryR (coordinates (u 0)))
    (hu : ∀ t, 0 ≤ t → HasDerivAt u (nominal (u t)) t)
    (a T : ℝ) (ha : 1/250 ≤ a) (hT : 0 ≤ T) :
    (207/20)*T ≤ ∫ t in a..(a+T), HG (u t) ∧
    (401/100)*T ≤ ∫ t in a..(a+T), HT (u t) := by
  have hab : a ≤ a+T := by linarith
  have hc : ContinuousOn u (Icc a (a+T)) := fun t ht =>
    (hu t (by linarith [ht.1])).continuousAt.continuousWithinAt
  have hG : Continuous HG := by unfold HG e0; fun_prop
  have hTr : Continuous HT := by unfold HT y; fun_prop
  have hiG : IntervalIntegrable (fun t => HG (u t)) volume a (a+T) :=
    (hG.comp_continuousOn hc).intervalIntegrable_of_Icc hab
  have hiT : IntervalIntegrable (fun t => HT (u t)) volume a (a+T) :=
    (hTr.comp_continuousOn hc).intervalIntegrable_of_Icc hab
  have hout := every_fast_source_trajectory u h0 hu
  have hg := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (207/20:ℝ)) volume a (a+T))
    hiG (fun t ht => (hout.1 t (by linarith [ht.1])).2.2.1)
  have ht := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (401/100:ℝ)) volume a (a+T))
    hiT (fun t ht => (hout.2 t (ha.trans ht.1)).2)
  norm_num [intervalIntegral.integral_const] at hg ht
  exact ⟨by nlinarith,by nlinarith⟩

theorem capped_deficit (f : ℝ → ℝ) (c tau T : ℝ) (hc : 0 ≤ c) (htau : 0 ≤ tau) (hT : 0 ≤ T)
    (hcont : ContinuousOn f (Icc 0 T))
    (hbound : ∀ t ∈ Icc 0 T, f t ≤ c)
    (hzero : ∀ t ∈ Icc 0 T, tau ≤ t → f t=0) :
    (∫ t in 0..T, f t) ≤ c*tau := by
  have hi := hcont.intervalIntegrable_of_Icc hT (μ := volume)
  by_cases hsmall : T ≤ tau
  · have hb := intervalIntegral.integral_mono_on hT hi
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => c) volume 0 T) hbound
    simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hb
    nlinarith
  · have hlarge : tau ≤ T := le_of_not_ge hsmall
    have hi₁ : IntervalIntegrable f volume 0 tau :=
      (hcont.mono (Icc_subset_Icc le_rfl hlarge)).intervalIntegrable_of_Icc htau
    have hi₂ : IntervalIntegrable f volume tau T :=
      (hcont.mono (Icc_subset_Icc htau le_rfl)).intervalIntegrable_of_Icc hlarge
    have hz : (∫ t in tau..T, f t)=0 := by
      apply intervalIntegral.integral_zero_ae
      filter_upwards with t ht
      rw [uIoc_of_le hlarge] at ht
      exact hzero t ⟨htau.trans ht.1.le,ht.2⟩ ht.1.le
    have hb := intervalIntegral.integral_mono_on htau hi₁
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => c) volume 0 tau)
      (fun t ht => hbound t ⟨ht.1,ht.2.trans hlarge⟩)
    have hadd := intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂
    simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hb
    rw [hz,add_zero] at hadd
    rw [← hadd]
    nlinarith

theorem operational_shortfall (u : ℝ → State)
    (h0 : InRect recoveryR (coordinates (u 0)))
    (hu : ∀ t, 0 ≤ t → HasDerivAt u (nominal (u t)) t)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in 0..T, max (10-HG (u t)) 0)=0 ∧
    (∫ t in 0..T, max (4-HT (u t)) 0) ≤ (9/25000:ℝ) := by
  have hs := every_fast_source_trajectory u h0 hu
  have hc : ContinuousOn u (Icc 0 T) := fun t ht =>
    (hu t ht.1).continuousAt.continuousWithinAt
  have hTr : Continuous (fun x : State => max (4-HT x) 0) := by
    unfold HT y
    fun_prop
  constructor
  · apply intervalIntegral.integral_zero_ae
    filter_upwards with t ht
    rw [uIoc_of_le hT] at ht
    have hg := (hs.1 t ht.1.le).2.2.1
    exact max_eq_right (by linarith)
  · have h := capped_deficit (fun t => max (4-HT (u t)) 0) (9/100) (1/250) T
      (by norm_num) (by norm_num) hT (hTr.comp_continuousOn hc)
      (by
        intro t ht
        have hh := (hs.1 t ht.1).2.2.2
        exact max_le (by linarith) (by norm_num))
      (by
        intro t _ ht
        have hh := (hs.2 t ht).2
        exact max_eq_right (by linarith))
    norm_num at h
    exact h

end
end DynamicSharedResource.Certificate

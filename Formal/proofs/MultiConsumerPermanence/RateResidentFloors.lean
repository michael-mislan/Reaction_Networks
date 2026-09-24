import proofs.MultiConsumerPermanence.RateDonorLoad

namespace MultiConsumerPermanence
open CoreCouplingGlobal CoreCouplingCAC RobustPermanence Filter Topology

theorem rate_loaded_eventually_resident_floors (r : AssemblyRates) (hr : RateBox r)
    (S : ℝ → State) (x : ℝ → ℝ) (hS : IsRateLoadedTrajectory r S x)
    (hxu : ∀ᶠ t in atTop, x t < 12) :
    ∀ᶠ t in atTop, 1 < (S t).A ∧ 2 < (S t).B ∧
      1/250 < (S t).z ∧ 1/100 < (S t).H := by
  have habs := rate_loaded_eventually_resident_absorbing r hr S x hS
  obtain ⟨T,hT⟩ := eventually_atTop.1 habs
  have hAlow : ∀ᶠ t in atTop, -(S t).A < -1 := by
    apply eventual_upper_of_linear_drift (fun t => -(S t).A)
      (fun t => -rateA r (S t).A (S t).B (S t).z)
      (max T 0) (-5) 3 (-1) (by norm_num) (by norm_num)
    · intro t ht
      exact (hS.dA t ((le_max_right _ _).trans ht)).neg
    · intro t ht
      have hp := hS.positive t ((le_max_right _ _).trans ht)
      have hs := (hT t ((le_max_left _ _).trans ht)).1
      have hh := rate_A_lower r hr (S t).A (S t).B (S t).z
        hp.1.le (by linarith [hp.2.1]) hp.2.1.le hp.2.2.1.le
      linarith only [hh]
  have hready : ∀ᶠ t in atTop, 0 ≤ t ∧ 1 ≤ (S t).A ∧
      (S t).B ≤ 34 ∧ (S t).z ≤ 12 ∧ x t ≤ 12 := by
    filter_upwards [eventually_ge_atTop (0:ℝ),hAlow,habs,hxu] with t ht hA hb hx
    have hp := hS.positive t ht
    exact ⟨ht,by linarith,by linarith [hb.1,hp.1],hb.2.2.1.le,hx.le⟩
  obtain ⟨Tz,hTz⟩ := eventually_atTop.1 hready
  have hzlow : ∀ᶠ t in atTop, -(S t).z < -(1/250) := by
    apply eventual_upper_of_linear_drift (fun t => -(S t).z)
      (fun t => -(rateZ r (S t).A (S t).B (S t).z (S t).H (x t)))
      Tz (-(9/10)) 111 (-(1/250)) (by norm_num) (by norm_num)
    · intro t ht
      exact (hS.dz t (hTz t ht).1).neg
    · intro t ht
      obtain ⟨h0,hA,hB,hz,hx⟩ := hTz t ht
      have hp := hS.positive t h0
      have hh := rate_z_lower r hr (S t).A (S t).B (S t).z (S t).H (x t)
        hA hB hp.2.2.1.le hz hp.2.2.2.le hx
      linarith only [hh]
  obtain ⟨TH,hTH⟩ := eventually_atTop.1 hzlow
  have hHlow : ∀ᶠ t in atTop, -(S t).H < -(1/100) := by
    apply eventual_upper_of_linear_drift (fun t => -(S t).H)
      (fun t => -rateH r (S t).z (S t).H)
      (max TH 0) (-(15/250)) 3 (-(1/100)) (by norm_num) (by norm_num)
    · intro t ht
      exact (hS.dH t ((le_max_right _ _).trans ht)).neg
    · intro t ht
      have hz := hTH t ((le_max_left _ _).trans ht)
      have hp := hS.positive t ((le_max_right _ _).trans ht)
      have hh := rate_H_lower r hr (S t).z (S t).H hp.2.2.1.le hp.2.2.2.le
      nlinarith only [hz,hh]
  filter_upwards [hAlow,habs,hzlow,hHlow] with t hA hb hz hH
  exact ⟨by linarith,hb.2.2.2,by linarith,by linarith⟩

end MultiConsumerPermanence

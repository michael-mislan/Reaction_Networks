import proofs.MultiConsumerPermanence.RateDonorLoad

namespace MultiConsumerPermanence
open CoreCouplingGlobal CoreCouplingCAC RobustPermanence Filter Topology

theorem reservoir_rate_z_lower (r : AssemblyRates) (hr : RateBox r) (A B z H X : ℝ)
    (hA : 1 ≤ A) (hB : B ≤ 34) (hz : 0 ≤ z) (hz' : z ≤ 12) (hH : 0 ≤ H) (hX : X ≤ 51) :
    9/10-200*z ≤ rateZ r A B z H X := by
  have hp := mul_le_mul_of_nonneg_left hA (by linarith [hr.p.1] : 0 ≤ r.p)
  have hqB := mul_le_mul_of_nonneg_left hB (by linarith [hr.q.1] : 0 ≤ r.q)
  have hqBz := mul_le_mul_of_nonneg_right hqB hz
  have hkX := mul_le_mul_of_nonneg_left hX (by linarith [hr.k.1] : 0 ≤ r.k)
  have hkXz := mul_le_mul_of_nonneg_right hkX hz
  have hzz : z^2 ≤ 12*z := by nlinarith
  have hv := mul_le_mul_of_nonneg_left hzz (by linarith [hr.v.1] : 0 ≤ r.v)
  have hsum : 34*r.q+r.u+24*r.v+51*r.k ≤ 200 := by
    linarith [hr.q.2,hr.u.2,hr.v.2,hr.k.2]
  have hsumz := mul_le_mul_of_nonneg_right hsum hz
  have hh := mul_nonneg (by linarith [hr.h1.1,hr.h2.1] : 0 ≤ r.h1+2*r.h2) hH
  dsimp [rateZ]
  nlinarith [hr.p.1]

theorem reservoir_rate_loaded_resident_floors (r : AssemblyRates) (hr : RateBox r)
    (S : ℝ → State) (x : ℝ → ℝ) (hS : IsRateLoadedTrajectory r S x)
    (hxu : ∀ᶠ t in atTop, x t < 51) :
    ∀ᶠ t in atTop, 1 < (S t).A ∧ 2 < (S t).B ∧
      1/500 < (S t).z ∧ 1/200 < (S t).H := by
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
      (S t).B ≤ 34 ∧ (S t).z ≤ 12 ∧ x t ≤ 51 := by
    filter_upwards [eventually_ge_atTop (0:ℝ),hAlow,habs,hxu] with t ht hA hb hx
    have hp := hS.positive t ht
    exact ⟨ht,by linarith,by linarith [hb.1,hp.1],hb.2.2.1.le,hx.le⟩
  obtain ⟨Tz,hTz⟩ := eventually_atTop.1 hready
  have hzlow : ∀ᶠ t in atTop, -(S t).z < -(1/500) := by
    apply eventual_upper_of_linear_drift (fun t => -(S t).z)
      (fun t => -(rateZ r (S t).A (S t).B (S t).z (S t).H (x t)))
      Tz (-(9/10)) 200 (-(1/500)) (by norm_num) (by norm_num)
    · intro t ht
      exact (hS.dz t (hTz t ht).1).neg
    · intro t ht
      obtain ⟨h0,hA,hB,hz,hx⟩ := hTz t ht
      have hp := hS.positive t h0
      have hh := reservoir_rate_z_lower r hr (S t).A (S t).B (S t).z (S t).H (x t)
        hA hB hp.2.2.1.le hz hp.2.2.2.le hx
      linarith only [hh]
  obtain ⟨TH,hTH⟩ := eventually_atTop.1 hzlow
  have hHlow : ∀ᶠ t in atTop, -(S t).H < -(1/200) := by
    apply eventual_upper_of_linear_drift (fun t => -(S t).H)
      (fun t => -rateH r (S t).z (S t).H)
      (max TH 0) (-(15/500)) 3 (-(1/200)) (by norm_num) (by norm_num)
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

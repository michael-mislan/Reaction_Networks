import proofs.RobustPermanence.RateDrift

namespace MultiConsumerPermanence
open CoreCouplingGlobal CoreCouplingCAC RobustPermanence Filter Topology

structure IsRateLoadedTrajectory (r : AssemblyRates) (S : ℝ → State) (x : ℝ → ℝ) : Prop where
  positive : ∀ t, 0 ≤ t → (S t).Positive
  load_nonnegative : ∀ t, 0 ≤ t → 0 ≤ x t
  dA : ∀ t, 0 ≤ t → HasDerivAt (fun s => (S s).A) (rateA r (S t).A (S t).B (S t).z) t
  dB : ∀ t, 0 ≤ t → HasDerivAt (fun s => (S s).B) (rateB r (S t).A (S t).B (S t).z) t
  dz : ∀ t, 0 ≤ t → HasDerivAt (fun s => (S s).z) (rateZ r (S t).A (S t).B (S t).z (S t).H (x t)) t
  dH : ∀ t, 0 ≤ t → HasDerivAt (fun s => (S s).H) (rateH r (S t).z (S t).H) t

theorem rate_loaded_eventually_resident_absorbing (r : AssemblyRates) (hr : RateBox r)
    (S : ℝ → State) (x : ℝ → ℝ) (hS : IsRateLoadedTrajectory r S x) :
    ∀ᶠ t in atTop, (S t).A+(S t).B < 34 ∧
      (S t).z+(7/4:ℝ)*(S t).H < 384 ∧ (S t).z < 12 ∧ 2 < (S t).B := by
  have hs : ∀ᶠ t in atTop, (S t).A+(S t).B < 34 := by
    apply eventual_upper_of_linear_drift (fun t => (S t).A+(S t).B)
      (fun t => rateA r (S t).A (S t).B (S t).z+rateB r (S t).A (S t).B (S t).z)
      0 (3300001/100000) (9999/10000) 34 (by norm_num) (by norm_num)
    · intro t ht
      exact (hS.dA t ht).add (hS.dB t ht)
    · intro t ht
      exact rate_total_upper r hr _ _ _ (hS.positive t ht).1.le (hS.positive t ht).2.1.le
  obtain ⟨Ts,hTs⟩ := eventually_atTop.1 hs
  have hW : ∀ᶠ t in atTop, (S t).z+(7/4:ℝ)*(S t).H < 384 := by
    apply eventual_upper_of_linear_drift (fun t => (S t).z+(7/4:ℝ)*(S t).H)
      (fun t => rateZ r (S t).A (S t).B (S t).z (S t).H (x t)+(7/4)*rateH r (S t).z (S t).H)
      (max Ts 0) (219/2) (2/7) 384 (by norm_num) (by norm_num)
    · intro t ht
      have h0 : 0 ≤ t := (le_max_right _ _).trans ht
      exact (hS.dz t h0).add ((hS.dH t h0).const_mul (7/4))
    · intro t ht
      have h0 : 0 ≤ t := (le_max_right _ _).trans ht
      have hp := hS.positive t h0
      have hs := hTs t ((le_max_left _ _).trans ht)
      exact rate_weighted_upper r hr _ _ _ _ _ hp.1.le (by linarith [hp.2.1])
        hp.2.1.le hp.2.2.1.le hp.2.2.2.le (hS.load_nonnegative t h0)
  obtain ⟨Tw,hTw⟩ := eventually_atTop.1 hW
  have hz : ∀ᶠ t in atTop, (S t).z < 12 := by
    apply eventual_upper_of_linear_drift (fun t => (S t).z)
      (fun t => rateZ r (S t).A (S t).B (S t).z (S t).H (x t))
      (max (max Ts Tw) 0) 1270 113 12 (by norm_num) (by norm_num)
    · intro t ht
      exact hS.dz t ((le_max_right _ _).trans ht)
    · intro t ht
      have h0 : 0 ≤ t := (le_max_right _ _).trans ht
      have hTs' : Ts ≤ t := (le_max_left Ts Tw).trans ((le_max_left _ _).trans ht)
      have hTw' : Tw ≤ t := (le_max_right Ts Tw).trans ((le_max_left _ _).trans ht)
      have hp := hS.positive t h0
      exact rate_z_upper r hr _ _ _ _ _ hp.1.le (by linarith [hTs t hTs',hp.2.1])
        hp.2.1.le hp.2.2.1.le hp.2.2.2.le (hS.load_nonnegative t h0) (hTw t hTw').le
  obtain ⟨Tz,hTz⟩ := eventually_atTop.1 hz
  have hB : ∀ᶠ t in atTop, -(S t).B < -2 := by
    apply eventual_upper_of_linear_drift (fun t => -(S t).B)
      (fun t => -rateB r (S t).A (S t).B (S t).z)
      (max Tz 0) (-(269/10)) (131/10) (-2) (by norm_num) (by norm_num)
    · intro t ht
      exact (hS.dB t ((le_max_right _ _).trans ht)).neg
    · intro t ht
      have hp := hS.positive t ((le_max_right _ _).trans ht)
      have hh := rate_B_lower r hr (S t).A (S t).B (S t).z hp.1.le hp.2.1.le
        (hTz t ((le_max_left _ _).trans ht)).le
      linarith only [hh]
  filter_upwards [hs,hW,hz,hB] with t htS htW htz htB
  exact ⟨htS,htW,htz,by linarith only [htB]⟩

end MultiConsumerPermanence

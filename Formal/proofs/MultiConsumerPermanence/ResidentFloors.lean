import proofs.MultiConsumerPermanence.DonorLoad
import proofs.RobustPermanence.ResidentFloors

namespace MultiConsumerPermanence
open CoreCouplingGlobal CoreCouplingCAC RobustPermanence Filter Topology

theorem loaded_eventually_resident_floors (e : ℝ) (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (S : ℝ → State) (x : ℝ → ℝ) (hS : IsLoadedResidentTrajectory e S x)
    (hxu : ∀ᶠ t in atTop, x t < 12) :
    ∀ᶠ t in atTop, 1 < (S t).A ∧ 2 < (S t).B ∧
      1/220 < (S t).z ∧ 1/100 < (S t).H := by
  have habs := loaded_eventually_resident_absorbing e he he' S x hS
  obtain ⟨T,hT⟩ := eventually_atTop.1 habs
  have hAlow : ∀ᶠ t in atTop, -(S t).A < -1 := by
    apply eventual_upper_of_linear_drift (fun t => -(S t).A)
      (fun t => -fA (flagshipRates e) (S t).A (S t).B (S t).z)
      (max T 0) (-6) 3 (-1) (by norm_num) (by norm_num)
    · intro t ht
      exact (hS.dA t ((le_max_right _ _).trans ht)).neg
    · intro t ht
      have hp := hS.positive t ((le_max_right _ _).trans ht)
      have hs := (hT t ((le_max_left _ _).trans ht)).1
      have hh := resident_A_lower_drift e (S t).A (S t).B (S t).z he he'
        hp.1.le (by linarith [hp.2.1]) hp.2.1.le hp.2.2.1.le
      linarith only [hh]
  have hready : ∀ᶠ t in atTop, 0 ≤ t ∧ 1 ≤ (S t).A ∧
      (S t).B ≤ 34 ∧ (S t).z ≤ 12 ∧ x t ≤ 12 := by
    filter_upwards [eventually_ge_atTop (0:ℝ),hAlow,habs,hxu] with t ht hA hb hx
    have hp := hS.positive t ht
    exact ⟨ht,by linarith,by linarith [hb.1,hp.1],hb.2.2.1.le,hx.le⟩
  obtain ⟨Tz,hTz⟩ := eventually_atTop.1 hready
  have hzlow : ∀ᶠ t in atTop, -(S t).z < -(1/220) := by
    apply eventual_upper_of_linear_drift (fun t => -(S t).z)
      (fun t => -(fZ (flagshipRates e) (S t).A (S t).B (S t).z (S t).H-(S t).z*x t))
      Tz (-1) 110 (-(1/220)) (by norm_num) (by norm_num)
    · intro t ht
      exact (hS.dz t (hTz t ht).1).neg
    · intro t ht
      obtain ⟨h0,hA,hB,hz,hx⟩ := hTz t ht
      have hp := hS.positive t h0
      have hh := resident_z_lower_drift e (S t).A (S t).B (S t).z (S t).H (x t)
        hA hB hp.2.2.1.le hz hp.2.2.2.le hx
      linarith only [hh]
  obtain ⟨TH,hTH⟩ := eventually_atTop.1 hzlow
  have hHlow : ∀ᶠ t in atTop, -(S t).H < -(1/100) := by
    apply eventual_upper_of_linear_drift (fun t => -(S t).H)
      (fun t => -fH (flagshipRates e) (S t).z (S t).H)
      (max TH 0) (-(16/220)) (20001/10000) (-(1/100)) (by norm_num) (by norm_num)
    · intro t ht
      exact (hS.dH t ((le_max_right _ _).trans ht)).neg
    · intro t ht
      have hz := hTH t ((le_max_left _ _).trans ht)
      dsimp [fH,flagshipRates]
      nlinarith only [hz,sq_nonneg (S t).z]
  filter_upwards [hAlow,habs,hzlow,hHlow] with t hA hb hz hH
  exact ⟨by linarith,hb.2.2.2,by linarith,by linarith⟩

end MultiConsumerPermanence

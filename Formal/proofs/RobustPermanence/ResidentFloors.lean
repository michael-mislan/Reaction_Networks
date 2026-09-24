import proofs.RobustPermanence.ConsumerAbsorber

namespace RobustPermanence
open CoreCouplingGlobal CoreCouplingCAC Filter Topology

theorem consumer_eventually_upper (e : ℝ) (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (S : ℝ → State) (x : ℝ → ℝ) (hS : IsConsumerTrajectory e S x) :
    ∀ᶠ t in atTop, x t < 12 := by
  obtain ⟨T,hT⟩ := eventually_atTop.1 (consumer_eventually_resident_absorbing e he he' S x hS)
  apply eventual_upper_of_linear_drift x (fun t => x t*((S t).z-1/2-x t))
    (max T 0) (2209/16) 12 12 (by norm_num) (by norm_num)
  · intro t ht
    exact hS.dx t ((le_max_right _ _).trans ht)
  · intro t ht
    have h0 : 0 ≤ t := (le_max_right _ _).trans ht
    have hz := (hT t ((le_max_left _ _).trans ht)).2.2.1
    have hx := hS.consumer_positive t h0
    have hh := mul_nonneg (by linarith : 0 ≤ 12-(S t).z) hx.le
    nlinarith only [hh,sq_nonneg (x t-47/4)]

theorem resident_A_lower_drift (e A B z : ℝ)
    (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (hA : 0 ≤ A) (hA' : A ≤ 34) (hB : 0 ≤ B) (hz : 0 ≤ z) :
    6-3*A ≤ fA (flagshipRates e) A B z := by
  have hAA : A^2 ≤ 34*A := by nlinarith
  have heAA := mul_le_mul_of_nonneg_left hAA he
  have heA := mul_le_mul_of_nonneg_right he' hA
  have heb := mul_nonneg he hB
  have hzb := mul_nonneg hz hB
  dsimp [fA,flagshipRates]
  nlinarith only [heAA,heA,heb,hzb,hA]

theorem resident_z_lower_drift (e A B z H x : ℝ)
    (hA : 1 ≤ A) (hB : B ≤ 34) (hz : 0 ≤ z) (hz' : z ≤ 12)
    (hH : 0 ≤ H) (hx : x ≤ 12) :
    1-110*z ≤ fZ (flagshipRates e) A B z H-z*x := by
  have hBz := mul_le_mul_of_nonneg_right hB hz
  have hxz := mul_le_mul_of_nonneg_left hx hz
  have hzz : z^2 ≤ 12*z := by nlinarith
  dsimp [fZ,flagshipRates]
  nlinarith only [hA,hBz,hxz,hzz,hH]

theorem consumer_eventually_resident_floors (e : ℝ) (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (S : ℝ → State) (x : ℝ → ℝ) (hS : IsConsumerTrajectory e S x) :
    ∀ᶠ t in atTop, 1 < (S t).A ∧ 2 < (S t).B ∧
      1/220 < (S t).z ∧ 1/100 < (S t).H := by
  have habs := consumer_eventually_resident_absorbing e he he' S x hS
  have hxu := consumer_eventually_upper e he he' S x hS
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

end RobustPermanence

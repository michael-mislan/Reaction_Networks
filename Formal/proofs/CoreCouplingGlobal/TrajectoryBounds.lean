import proofs.CoreCouplingGlobal.Absorbing
import proofs.CoreCouplingGlobal.ScalarComparison

open Filter Topology

namespace CoreCouplingGlobal
open CoreCouplingCAC

/-- Only the literal ODE and positivity are assumed; no convergence or boundedness. -/
structure IsPositiveTrajectory (e : ℝ) (X : ℝ → State) : Prop where
  positive : ∀ t, 0 ≤ t → (X t).Positive
  dA : ∀ t, 0 ≤ t → HasDerivAt (fun s => (X s).A)
    (fA (flagshipRates e) (X t).A (X t).B (X t).z) t
  dB : ∀ t, 0 ≤ t → HasDerivAt (fun s => (X s).B)
    (fB (flagshipRates e) (X t).A (X t).B (X t).z) t
  dz : ∀ t, 0 ≤ t → HasDerivAt (fun s => (X s).z)
    (fZ (flagshipRates e) (X t).A (X t).B (X t).z (X t).H) t
  dH : ∀ t, 0 ≤ t → HasDerivAt (fun s => (X s).H)
    (fH (flagshipRates e) (X t).z (X t).H) t

theorem trajectory_eventually_absorbing (e : ℝ) (he : 0 ≤ e) (heM : e ≤ 1/50000)
    (X : ℝ → State) (hX : IsPositiveTrajectory e X) :
    ∀ᶠ t in atTop, (X t).A+(X t).B < 34 ∧
      (X t).z+(7/4:ℝ)*(X t).H < 384 ∧ (X t).z < 12 ∧ 2 < (X t).B := by
  have hs : ∀ᶠ t in atTop, (X t).A+(X t).B < 34 := by
    apply eventual_upper_of_linear_drift
      (fun t => (X t).A+(X t).B)
      (fun t => fA (flagshipRates e) (X t).A (X t).B (X t).z +
        fB (flagshipRates e) (X t).A (X t).B (X t).z)
      0 33 (1-e) 34 (by linarith)
    · apply (div_lt_iff₀ (by linarith : 0<1-e)).2
      linarith
    · intro t ht
      exact (hX.dA t ht).add (hX.dB t ht)
    · intro t ht
      exact total_upper_comparison _ _ _ _ (hX.positive t ht).1.le he
  obtain ⟨Ts,hTs⟩ := eventually_atTop.1 hs
  have hW : ∀ᶠ t in atTop, (X t).z+(7/4:ℝ)*(X t).H < 384 := by
    apply eventual_upper_of_linear_drift
      (fun t => (X t).z+(7/4:ℝ)*(X t).H)
      (fun t => fZ (flagshipRates e) (X t).A (X t).B (X t).z (X t).H +
        (7/4:ℝ)*fH (flagshipRates e) (X t).z (X t).H)
      (max Ts 0) (5364/49) (2/7) 384 (by norm_num) (by norm_num)
    · intro t ht
      have h0 : 0 ≤ t := (le_max_right Ts 0).trans ht
      exact (hX.dz t h0).add ((hX.dH t h0).const_mul (7/4))
    · intro t ht
      have h0 : 0 ≤ t := (le_max_right Ts 0).trans ht
      have hp := hX.positive t h0
      have hst := hTs t ((le_max_left Ts 0).trans ht)
      exact weighted_upper_comparison _ _ _ _ _ (by linarith [hp.2.1])
        hp.2.1.le hp.2.2.1.le hp.2.2.2.le
  obtain ⟨Tw,hTw⟩ := eventually_atTop.1 hW
  have hz : ∀ᶠ t in atTop, (X t).z < 12 := by
    apply eventual_upper_of_linear_drift (fun t => (X t).z)
      (fun t => fZ (flagshipRates e) (X t).A (X t).B (X t).z (X t).H)
      (max (max Ts Tw) 0) (8878/7) (796/7) 12 (by norm_num) (by norm_num)
    · intro t ht
      exact hX.dz t ((le_max_right _ _).trans ht)
    · intro t ht
      have h0 : 0 ≤ t := (le_max_right _ _).trans ht
      have hTs' : Ts ≤ t := (le_max_left Ts Tw).trans ((le_max_left _ _).trans ht)
      have hTw' : Tw ≤ t := (le_max_right Ts Tw).trans ((le_max_left _ _).trans ht)
      have hp := hX.positive t h0
      exact z_linear_comparison _ _ _ _ _ (by linarith [hTs t hTs',hp.2.1])
        hp.2.1.le hp.2.2.1.le (hTw t hTw').le
  obtain ⟨Tz,hTz⟩ := eventually_atTop.1 hz
  have hB : ∀ᶠ t in atTop, -(X t).B < -2 := by
    apply eventual_upper_of_linear_drift (fun t => -(X t).B)
      (fun t => -fB (flagshipRates e) (X t).A (X t).B (X t).z)
      (max Tz 0) (-27) (13+e) (-2) (by positivity)
    · apply (div_lt_iff₀ (by positivity : 0<13+e)).2
      linarith
    · intro t ht
      exact (hX.dB t ((le_max_right _ _).trans ht)).neg
    · intro t ht
      have hp := hX.positive t ((le_max_right _ _).trans ht)
      exact B_linear_comparison _ _ _ _ hp.1.le hp.2.1.le
        (hTz t ((le_max_left _ _).trans ht)).le he
  filter_upwards [hs,hW,hz,hB] with t htS htW htz htB
  exact ⟨htS,htW,htz,by linarith only [htB]⟩

end CoreCouplingGlobal

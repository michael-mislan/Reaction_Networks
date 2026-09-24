import proofs.CoreCouplingCAC.ExactClassification

namespace CoreCouplingCAC
open Polynomial

theorem creation_interval_bracketed (e : ℝ) (hl : (1/200000:ℝ) ≤ e) (hr : e ≤ (1/50000:ℝ)) :
    ∃ x y w : State, x.Positive ∧ y.Positive ∧ w.Positive ∧
      Stationary (varyRates e) x ∧ Stationary (varyRates e) y ∧ Stationary (varyRates e) w ∧
      x.z < y.z ∧ y.z < w.z ∧ Set.Icc (9/10:ℝ) (11/10) x.z ∧
      Set.Icc (19/10:ℝ) (21/10) y.z ∧ Set.Icc (29/10:ℝ) (31/10) w.z := by
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ := creation_interval_signs e hl hr
  obtain ⟨z₁,hz₁,he₁⟩ := intermediate_value_Icc
    (by norm_num : (9/10:ℝ) ≤ 11/10)
    (vary_residual_continuousOn e (9/10) (11/10) (by norm_num)) ⟨h₁.le,h₂.le⟩
  obtain ⟨z₂,hz₂,he₂⟩ := intermediate_value_Icc'
    (by norm_num : (19/10:ℝ) ≤ 21/10)
    (vary_residual_continuousOn e (19/10) (21/10) (by norm_num)) ⟨h₄.le,h₃.le⟩
  obtain ⟨z₃,hz₃,he₃⟩ := intermediate_value_Icc
    (by norm_num : (29/10:ℝ) ≤ 31/10)
    (vary_residual_continuousOn e (29/10) (31/10) (by norm_num)) ⟨h₅.le,h₆.le⟩
  have hp₁ : 0 < z₁ := by linarith [hz₁.1]
  have hp₂ : 0 < z₂ := by linarith [hz₂.1]
  have hp₃ : 0 < z₃ := by linarith [hz₃.1]
  refine ⟨lift (varyRates e) z₁,lift (varyRates e) z₂,lift (varyRates e) z₃,?_,?_,?_,
    lift_stationary _ z₁ (by positivity) (by norm_num [varyRates,witnessRates]) he₁,
    lift_stationary _ z₂ (by positivity) (by norm_num [varyRates,witnessRates]) he₂,
    lift_stationary _ z₃ (by positivity) (by norm_num [varyRates,witnessRates]) he₃,?_,?_,hz₁,hz₂,hz₃⟩
  · exact witness_lift_positive z₁ hp₁ (by linarith [hz₁.2])
  · exact witness_lift_positive z₂ hp₂ (by linarith [hz₂.2])
  · exact witness_lift_positive z₃ hp₃ (by linarith [hz₃.2])
  · change z₁ < z₂
    linarith [hz₁.2,hz₂.1]
  · change z₂ < z₃
    linarith [hz₂.2,hz₃.1]

theorem exactly_three_bracketed_equilibria (e : ℝ) (hl : (1/200000:ℝ) ≤ e) (hr : e ≤ (1/50000:ℝ)) :
    ∃ x y w : State, x.Positive ∧ y.Positive ∧ w.Positive ∧
      Stationary (varyRates e) x ∧ Stationary (varyRates e) y ∧ Stationary (varyRates e) w ∧
      x.z < y.z ∧ y.z < w.z ∧ Set.Icc (9/10:ℝ) (11/10) x.z ∧
      Set.Icc (19/10:ℝ) (21/10) y.z ∧ Set.Icc (29/10:ℝ) (31/10) w.z ∧
      ∀ s : State, s.Positive → Stationary (varyRates e) s →
        (s = x ∨ s = y ∨ s = w) ∧ (countPoly e).derivative.eval (rootParameter s) ≠ 0 := by
  obtain ⟨x,y,w,hx,hy,hw,hsx,hsy,hsw,hxy,hyw,hbx,hby,hbw⟩ := creation_interval_bracketed e hl hr
  have hpx := stationary_root_parameter e hl hr x hx hsx
  have hpy := stationary_root_parameter e hl hr y hy hsy
  have hpw := stationary_root_parameter e hl hr w hw hsw
  have hP : countPoly e ≠ 0 := by
    intro h
    have hd := count_degree e (count_coeff_signs e hl hr).2.2.2.2.2.2
    rw [h,degree_zero] at hd
    norm_num at hd
  have hall := three_positive_roots_exhaust (countPoly e) hP (positive_count_bound e hl hr)
    (rootParameter x) (rootParameter y) (rootParameter w) hpx.2.1
    (rootParameter_order x y hpx.1 hpy.1 hxy) (rootParameter_order y w hpy.1 hpw.1 hyw)
    hpx.2.2 hpy.2.2 hpw.2.2
  refine ⟨x,y,w,hx,hy,hw,hsx,hsy,hsw,hxy,hyw,hbx,hby,hbw,?_⟩
  intro s hs hss
  have hps := stationary_root_parameter e hl hr s hs hss
  obtain ⟨hcases,hderiv⟩ := hall (rootParameter s) hps.2.1 hps.2.2
  refine ⟨?_,hderiv⟩
  rcases hcases with h | h | h
  · exact Or.inl (rootParameter_stationary_injective e (by linarith) s x hs hx hss hsx hps.1 hpx.1 h)
  · exact Or.inr (Or.inl (rootParameter_stationary_injective e (by linarith) s y hs hy hss hsy hps.1 hpy.1 h))
  · exact Or.inr (Or.inr (rootParameter_stationary_injective e (by linarith) s w hs hw hss hsw hps.1 hpw.1 h))

end CoreCouplingCAC

-- Final source checkpoint: bracketed existence and exhaustive classification.

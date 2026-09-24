import proofs.CoreCouplingCAC.Creation

namespace CoreCouplingCAC

noncomputable def varyRates (e : ℝ) : Rates := { witnessRates with e := e }

theorem varyRates_positive (e : ℝ) (he : 0 < e) : (varyRates e).Positive := by
  norm_num [Rates.Positive,varyRates,witnessRates,he]

theorem vary_lift (e z : ℝ) : lift (varyRates e) z = lift witnessRates z := rfl

theorem vary_residual_continuousOn (e l r : ℝ) (hl : 0 < l) :
    ContinuousOn (residual (varyRates e)) (Set.Icc l r) := by
  have hden : ∀ z ∈ Set.Icc l r, z+2 ≠ (0:ℝ) := by
    intro z hz
    linarith [hz.1]
  unfold residual reducedA reducedB reducedK
  apply ContinuousOn.add
  · apply ContinuousOn.add
    · exact continuousOn_const.sub
        (continuousOn_const.mul (continuousOn_const.div
          (continuousOn_id.add continuousOn_const) hden))
    · apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro z _
        norm_num [varyRates,witnessRates]
  · apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.pow
    apply ContinuousOn.add
    · exact continuousOn_id.mul (continuousOn_const.div
        (continuousOn_id.add continuousOn_const) hden)
    · apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro z _
        norm_num [varyRates,witnessRates]

theorem creation_interval_signs (e : ℝ) (hl : (1/200000:ℝ) ≤ e)
    (hr : e ≤ (1/50000:ℝ)) :
    residual (varyRates e) (9/10) < 0 ∧ 0 < residual (varyRates e) (11/10) ∧
    0 < residual (varyRates e) (19/10) ∧ residual (varyRates e) (21/10) < 0 ∧
    residual (varyRates e) (29/10) < 0 ∧ 0 < residual (varyRates e) (31/10) := by
  norm_num [residual,reducedA,reducedB,reducedK,varyRates,witnessRates]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Creation persists on a nonempty open interval of the actual coupling
constant; the stronger closed-interval statement is proved here. -/
theorem creation_interval (e : ℝ) (hl : (1/200000:ℝ) ≤ e) (hr : e ≤ (1/50000:ℝ)) :
    ∃ x y w : State, x.Positive ∧ y.Positive ∧ w.Positive ∧
      Stationary (varyRates e) x ∧ Stationary (varyRates e) y ∧ Stationary (varyRates e) w ∧
      x.z < y.z ∧ y.z < w.z := by
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
    lift_stationary _ z₃ (by positivity) (by norm_num [varyRates,witnessRates]) he₃,?_,?_⟩
  · exact witness_lift_positive z₁ hp₁ (by linarith [hz₁.2])
  · exact witness_lift_positive z₂ hp₂ (by linarith [hz₂.2])
  · exact witness_lift_positive z₃ hp₃ (by linarith [hz₃.2])
  · change z₁ < z₂
    linarith [hz₁.2,hz₂.1]
  · change z₂ < z₃
    linarith [hz₂.2,hz₃.1]

end CoreCouplingCAC

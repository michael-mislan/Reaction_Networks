import proofs.CoreCouplingCAC.Reduction

namespace CoreCouplingCAC

noncomputable def witnessRates : Rates := ⟨6,27,16,2,1/100000,1/10000⟩

theorem witnessRates_positive : witnessRates.Positive := by
  norm_num [Rates.Positive,witnessRates]

theorem witness_K (z : ℝ) :
    reducedK witnessRates z = (20004*z^2-159984*z)/20001 := by
  norm_num [reducedK,witnessRates]
  ring

theorem witness_lift_positive (z : ℝ) (hz : 0 < z) (hz4 : z ≤ 4) :
    (lift witnessRates z).Positive := by
  have hden : 0 < z+2 := by linarith
  have hB : 10 ≤ reducedB witnessRates z := by
    dsimp [reducedB,witnessRates]
    apply (le_div_iff₀ hden).2
    linarith
  have hK : -8*z ≤ reducedK witnessRates z := by
    rw [witness_K]
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<20001)).2
    nlinarith [sq_nonneg z]
  have hA : 0 < reducedA witnessRates z := by
    dsimp [reducedA]
    nlinarith [mul_nonneg (le_of_lt hz) (sub_nonneg.mpr hB)]
  refine ⟨hA, by dsimp [lift]; linarith, hz, ?_⟩
  dsimp [lift,reducedH,witnessRates]
  positivity

theorem residual_continuousOn (l r : ℝ) (hl : 0 < l) :
    ContinuousOn (residual witnessRates) (Set.Icc l r) := by
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
        norm_num [witnessRates]
  · apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.pow
    apply ContinuousOn.add
    · exact continuousOn_id.mul (continuousOn_const.div
        (continuousOn_id.add continuousOn_const) hden)
    · apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro z _
        norm_num [witnessRates]

theorem witness_signs :
    residual witnessRates (9/10) < 0 ∧ 0 < residual witnessRates (11/10) ∧
    0 < residual witnessRates (19/10) ∧ residual witnessRates (21/10) < 0 ∧
    residual witnessRates (29/10) < 0 ∧ 0 < residual witnessRates (31/10) := by
  norm_num [residual,reducedA,reducedB,reducedK,witnessRates]

theorem witness_three_scalar_roots :
    ∃ z₁ z₂ z₃ : ℝ,
      z₁ ∈ Set.Icc (9/10) (11/10) ∧
      z₂ ∈ Set.Icc (19/10) (21/10) ∧
      z₃ ∈ Set.Icc (29/10) (31/10) ∧
      residual witnessRates z₁ = 0 ∧ residual witnessRates z₂ = 0 ∧
      residual witnessRates z₃ = 0 := by
  rcases witness_signs with ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩
  obtain ⟨z₁,hz₁,he₁⟩ := intermediate_value_Icc
    (by norm_num : (9/10:ℝ) ≤ 11/10)
    (residual_continuousOn (9/10) (11/10) (by norm_num)) ⟨h₁.le,h₂.le⟩
  obtain ⟨z₂,hz₂,he₂⟩ := intermediate_value_Icc'
    (by norm_num : (19/10:ℝ) ≤ 21/10)
    (residual_continuousOn (19/10) (21/10) (by norm_num)) ⟨h₄.le,h₃.le⟩
  obtain ⟨z₃,hz₃,he₃⟩ := intermediate_value_Icc
    (by norm_num : (29/10:ℝ) ≤ 31/10)
    (residual_continuousOn (29/10) (31/10) (by norm_num)) ⟨h₅.le,h₆.le⟩
  exact ⟨z₁,z₂,z₃,hz₁,hz₂,hz₃,he₁,he₂,he₃⟩

/-- Three distinct strictly positive equilibria of one literal source with
strictly positive added reversible-core and degradation constants.
This theorem asserts multistationarity, not stability or convergence.
-/
theorem repaired_source_multistationary :
    ∃ x y w : State, x.Positive ∧ y.Positive ∧ w.Positive ∧
      Stationary witnessRates x ∧ Stationary witnessRates y ∧ Stationary witnessRates w ∧
      x.z < y.z ∧ y.z < w.z := by
  obtain ⟨z₁,z₂,z₃,hz₁,hz₂,hz₃,he₁,he₂,he₃⟩ := witness_three_scalar_roots
  have hp₁ : 0 < z₁ := by linarith [hz₁.1]
  have hp₂ : 0 < z₂ := by linarith [hz₂.1]
  have hp₃ : 0 < z₃ := by linarith [hz₃.1]
  refine ⟨lift witnessRates z₁,lift witnessRates z₂,lift witnessRates z₃,
    witness_lift_positive z₁ hp₁ (by linarith [hz₁.2]),
    witness_lift_positive z₂ hp₂ (by linarith [hz₂.2]),
    witness_lift_positive z₃ hp₃ (by linarith [hz₃.2]),
    lift_stationary witnessRates z₁ (by positivity) (by norm_num [witnessRates]) he₁,
    lift_stationary witnessRates z₂ (by positivity) (by norm_num [witnessRates]) he₂,
    lift_stationary witnessRates z₃ (by positivity) (by norm_num [witnessRates]) he₃,?_,?_⟩
  · change z₁ < z₂
    linarith [hz₁.2,hz₂.1]
  · change z₂ < z₃
    linarith [hz₂.2,hz₃.1]

end CoreCouplingCAC

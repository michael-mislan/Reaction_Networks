import proofs.RandomViability.CollectiveRAFProbability
import proofs.RandomViability.CollectivePhysicalMeaning
import proofs.RandomViability.ProductiveResolution

namespace RandomViability
open Filter Topology
noncomputable section

theorem collective_raf_joint_eventually_positive (volume : ℕ → ℕ)
    (hvolume : ∀ n,collectiveMinimalVolume n ≤ volume n) :
    ∀ᶠ n in atTop,0 < collectiveRAFJointProbability volume hvolume n := by
  obtain ⟨L,U,hL,_,hb⟩ := collective_raf_joint_probability_theta volume hvolume
  filter_upwards [hb,source_incidence_ge_exp_eventually] with n hn hp
  exact (mul_pos hL hp.1).trans_le hn.1

/-- Quantitative emergence in the declared literal random kinetic model.

The first regime has genuine RAF-attributed productive operation at slowly
growing volume. The second has a genuine selected RAF, collective-host
productive operation and a uniform high-volume probability order. These
observables are distinct; neither is a nonvanishing prevalence assertion.
The separate physical-meaning and disabled-control theorems bind the second
event to residence at all physical times, signed current and catalytic need.
-/
theorem random_autocatalysis_declared_regimes :
    (Tendsto productiveVolume atTop atTop ∧
      (∀ n,40 ≤ productiveVolume n) ∧
      (∀ᶠ n in atTop,0 < productiveJointProbability n) ∧
      (∀ n : ℕ,4 ≤ n →
        productiveBeta (productiveVolume n)*productiveSourceIncidence n ≤ productiveJointProbability n ∧
        productiveJointProbability n ≤ productiveUpperCoefficient (productiveVolume n)*productiveSourceIncidence n) ∧
      Tendsto (fun n => Real.log (productiveJointProbability n)/(n : ℝ)) atTop (𝓝 (-Real.log 2))) ∧
    (∀ (volume : ℕ → ℕ) (hvolume : ∀ n,collectiveMinimalVolume n ≤ volume n),
      (∀ n : ℕ,4 ≤ n →
        sourceEmptyRowMass (2-2/(n : ℝ)) n ^ 6*productiveSourceIncidence n*
          (1-24*Real.exp (-(markedNoiseRate*(volume n : ℝ)/(n : ℝ)))) ≤
            collectiveRAFJointProbability volume hvolume n ∧
        collectiveRAFJointProbability volume hvolume n ≤
          collectiveSourceUpperConstant*productiveSourceIncidence n+
            2*Real.exp (-(markedNoiseRate*(volume n : ℝ)/(n : ℝ)))) ∧
      (∃ L U : ℝ,0 < L ∧ 0 < U ∧ ∀ᶠ n in atTop,
        L*productiveSourceIncidence n ≤ collectiveRAFJointProbability volume hvolume n ∧
        collectiveRAFJointProbability volume hvolume n ≤ U*productiveSourceIncidence n) ∧
      (∀ᶠ n in atTop,0 < collectiveRAFJointProbability volume hvolume n) ∧
      Tendsto (fun n => Real.log (collectiveRAFJointProbability volume hvolume n)/(n : ℝ))
        atTop (𝓝 (-Real.log 2))) ∧
    Tendsto (fun n : ℕ => eventMass (2-2/(n : ℝ)) n FoodEscape) atTop (𝓝 0) := by
  obtain ⟨hv,hvg,hp,hb,hl,hz⟩ := random_autocatalysis_rare_event_regime
  refine ⟨⟨hv,hvg,hp,hb,hl⟩,?_,hz⟩
  intro volume hvolume
  exact ⟨collective_raf_joint_probability_bounds volume hvolume,
    collective_raf_joint_probability_theta volume hvolume,
    collective_raf_joint_eventually_positive volume hvolume,
    collective_raf_joint_logarithmic_limit volume hvolume⟩

end
end RandomViability

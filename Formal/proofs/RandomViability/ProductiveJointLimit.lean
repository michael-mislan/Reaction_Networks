import proofs.RandomViability.ProductiveFullProbability
import proofs.RandomViability.ProductiveBudgetAsymptotics
import proofs.RandomViability.ProductiveUpperAsymptotics
import proofs.PowerLawSmallRAF.SourcePrivateGateway

namespace RandomViability
open Classical Filter Topology MeasureTheory PowerLawSmallRAF
noncomputable section
set_option maxHeartbeats 60000

local instance (n : ℕ) : MeasurableSpace (PhysicalCountChannel n) := ⊤
local instance (n : ℕ) : MeasurableSingletonClass (PhysicalCountChannel n) := ⟨fun _ => trivial⟩

/-- The actual fully averaged probability along the declared joint regime.
The values below the legal horizon four are harmless placeholders. -/
def productiveJointProbability (n : ℕ) : ℝ :=
  if hn : 4 ≤ n then fullyAveragedProductiveProbability hn (productiveVolume n)
    (productive_volume_ge n) (2-2/(n : ℝ)) else 1

theorem productive_joint_probability_bounds (n : ℕ) (hn : 4 ≤ n) :
    productiveBeta (productiveVolume n)*productiveSourceIncidence n ≤ productiveJointProbability n ∧
    productiveJointProbability n ≤ productiveUpperCoefficient (productiveVolume n)*productiveSourceIncidence n := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 1 < 2-2/(n : ℝ) := by
    have hd : 2/(n : ℝ) ≤ 1/2 := (div_le_iff₀ (by linarith)).mpr (by linarith)
    linarith
  have hR : 2 ≤ sourceReactionCount n := by unfold sourceReactionCount; omega
  have hh := fully_averaged_productive_bounds hn (productiveVolume n) (productive_volume_ge n)
    (2-2/(n : ℝ)) ha
  rw [powerLawMoleculeGatewayHit_one_eq_mean_div _ _ ha hR] at hh
  simpa only [productiveJointProbability,dif_pos hn,productiveSourceIncidence,
    productiveSourceMean,productiveUpperCoefficient] using hh

theorem productive_joint_probability_eventually_pos :
    ∀ᶠ n in atTop, 0 < productiveJointProbability n := by
  filter_upwards [productive_source_mean_eventually_pos,eventually_ge_atTop 4] with n hf hn
  have hp : 0 < productiveSourceIncidence n := by
    apply div_pos hf
    exact_mod_cast (show 0 < sourceReactionCount n by unfold sourceReactionCount; omega)
  exact (mul_pos (productiveBeta_pos _ (productive_volume_ge n)) hp).trans_le
    (productive_joint_probability_bounds n hn).1

/-- Sharp logarithmic probability rate for the declared growing-volume
physical RAF operating event, with source, kinetic marks and clocks averaged.
This is not a high-reliability or uniform Theta(p_n) theorem. -/
theorem productive_joint_logarithmic_limit :
    Tendsto (fun n => Real.log (productiveJointProbability n)/(n : ℝ))
      atTop (𝓝 (-Real.log 2)) := by
  have hl := productive_beta_log_negligible.add productive_source_incidence_log_rate
  have hu := productive_upper_log_negligible.add productive_source_incidence_log_rate
  simp only [zero_add] at hl hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [productive_source_mean_eventually_pos,eventually_ge_atTop 4] with n hf hn
    have hp : 0 < productiveSourceIncidence n := by
      apply div_pos hf
      exact_mod_cast (show 0 < sourceReactionCount n by unfold sourceReactionCount; omega)
    have hb := productiveBeta_pos (productiveVolume n) (productive_volume_ge n)
    have hh := Real.log_le_log (mul_pos hb hp) (productive_joint_probability_bounds n hn).1
    rw [Real.log_mul hb.ne' hp.ne'] at hh
    simpa only [add_div] using div_le_div_of_nonneg_right hh (show (0 : ℝ) ≤ n by positivity)
  · filter_upwards [productive_source_mean_eventually_pos,productive_joint_probability_eventually_pos,
      eventually_ge_atTop 4] with n hf hq hn
    have hp : 0 < productiveSourceIncidence n := by
      apply div_pos hf
      exact_mod_cast (show 0 < sourceReactionCount n by unfold sourceReactionCount; omega)
    have hb := (productive_joint_probability_bounds n hn).2
    have hc : 0 < productiveUpperCoefficient (productiveVolume n) :=
      (mul_pos_iff_of_pos_right hp).mp (hq.trans_le hb)
    have hh := Real.log_le_log hq hb
    rw [Real.log_mul hc.ne' hp.ne'] at hh
    simpa only [add_div] using div_le_div_of_nonneg_right hh (show (0 : ℝ) ≤ n by positivity)

end
end RandomViability

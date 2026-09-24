import proofs.StartupMarked.Resolution
import proofs.RandomViability.CollectiveAsymptoticScale
import proofs.PowerLawSmallRAF.SourcePrivateGateway

namespace StartupMarked
open RandomViability PowerLawSmallRAF Filter Topology
noncomputable section
local instance channelSpace (n : ℕ) : MeasurableSpace (PhysicalCountChannel n) := ⊤
local instance channelSingleton (n : ℕ) : MeasurableSingletonClass (PhysicalCountChannel n) := ⟨fun _ => trivial⟩

theorem startup_witness_normalized_limit :
    Tendsto (fun n : ℕ => (9989/10000 : ℝ)*
      sourceEmptyRowMass (2-2/(n : ℝ)) n ^ 6 *
      (productiveSourceMean n/(n : ℝ))) atTop
      (𝓝 ((9989/10000 : ℝ)*(1/(Real.pi^2/6))^6*criticalLambda (-2))) := by
  exact (tendsto_const_nhds.mul (collective_empty_row_limit.pow 6)).mul
    productive_source_mean_normalized

theorem startup_normalized_source_lower {n : ℕ} (hn : 4 ≤ n) (V : ℕ)
    (hvolume : startupVolume n ≤ V) (a : ℝ) (ha : 1 < a) :
    let hV := (startup_volume_pos n).trans_le hvolume
    (9989/10000 : ℝ)*sourceEmptyRowMass a n ^ 6 *
      (windowZipfMean a (sourceReactionCount n)/(n : ℝ)) ≤
      ((sourceReactionCount n : ℝ)/(n : ℝ))*fullyAveragedTwoWindowProbability hn V hV a := by
  have h := (startup_quantitative_resolution hn V hvolume a ha).2.1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hR : 2 ≤ sourceReactionCount n := by unfold sourceReactionCount; omega
  have hR0 : (0 : ℝ) < sourceReactionCount n := by exact_mod_cast (show 0 < sourceReactionCount n by omega)
  rw [powerLawMoleculeGatewayHit_one_eq_mean_div a (sourceReactionCount n) ha hR] at h
  have hh := mul_le_mul_of_nonneg_left h (div_nonneg hR0.le hn0.le)
  convert hh using 1
  field_simp

end
end StartupMarked

import proofs.PowerLawSmallRAF.VanishingLowBandMean

namespace PowerLawSmallRAF
open Filter Topology
noncomputable section

theorem criticalPartialMass_full_eq : criticalPartialMass (-2) (Real.log 2) = 3/2 := by
  have hfour : Real.exp (2*Real.log 2) = 4 := by
    rw [show (2 : ℝ)*Real.log 2 = Real.log 2+Real.log 2 by ring, Real.exp_add]
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [criticalPartialMass,integral_exp_neg_mul (-2) (by norm_num)]
  simp only [neg_neg]
  rw [hfour]
  norm_num

theorem sourceFullIntensity_pos : 0 < sourceFullIntensity := by
  rw [sourceFullIntensity,criticalPartialMass_full_eq]
  positivity

theorem sourceVanishingLowMean_tendsto_atTop : Tendsto sourceVanishingLowMean atTop atTop := by
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_pos sourceFullIntensity_pos
    sourceVanishingLowMean_tendsto
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp

/-- Total retention in [0,1], asymptotically approaching one. -/
def sourceVanishingLowRetention (n : Nat) : ℝ := 1-((n+1 : Nat) : ℝ)^(-(1/8 : ℝ))

theorem sourceVanishingLowRetention_bounds (n : Nat) :
    0 ≤ sourceVanishingLowRetention n ∧ sourceVanishingLowRetention n ≤ 1 := by
  have hx : (1 : ℝ) ≤ ((n+1 : Nat) : ℝ) := by exact_mod_cast (show 1 ≤ n+1 by omega)
  have hp := Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num : -(1/8 : ℝ) ≤ 0)
  have h0 := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ ((n+1 : Nat) : ℝ)) (-(1/8 : ℝ))
  constructor <;> unfold sourceVanishingLowRetention <;> linarith

theorem sourceVanishingLowRetention_tendsto :
    Tendsto sourceVanishingLowRetention atTop (𝓝 1) := by
  have hn : Tendsto (fun n : Nat => ((n+1 : Nat) : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/8)).comp hn
  change Tendsto (fun n : Nat => 1-((n+1 : Nat) : ℝ)^(-(1/8 : ℝ))) atTop (𝓝 1)
  simpa only [sub_zero] using (tendsto_const_nhds.sub h :
    Tendsto (fun n : Nat => 1-((n+1 : Nat) : ℝ)^(-(1/8 : ℝ))) atTop (𝓝 (1-0)))

theorem sourceVanishingLowRetainedMean_tendsto :
    Tendsto (fun n => sourceVanishingLowRetention n *
      ((sourceMoleculeCount n : ℝ)/(sourceReactionCount n : ℝ))*sourceVanishingLowMean n)
      atTop (𝓝 sourceFullIntensity) := by
  simpa only [one_mul,mul_assoc,sourceFullIntensity] using
    sourceVanishingLowRetention_tendsto.mul sourceVanishingLowDensity_tendsto

end
end PowerLawSmallRAF

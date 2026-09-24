import proofs.PowerLawSmallRAF.SourceTwoBandPositiveRAF

namespace PowerLawSmallRAF
open Filter Topology
noncomputable section

def sourceTwoBandBudgetLogEnvelope (n : Nat) : ℝ :=
  Real.log 3 + 4*Real.log (n : ℝ) +
    ((shrinkingBandWidth n : ℝ)+(targetNucleusLength n : ℝ)+1)*Real.log 2

theorem sourceTwoBandBudgetLogEnvelope_relative_tendsto :
    Tendsto (fun n : Nat => sourceTwoBandBudgetLogEnvelope n/(n : ℝ)) atTop (𝓝 0) := by
  have hi : Tendsto (fun n : Nat => (1 : ℝ)/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hl := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := ((hi.const_mul (Real.log 3)).add (hl.const_mul 4)).add
    (((shrinkingBandWidth_relative_tendsto.add targetNucleusLength_relative_tendsto).add hi).mul_const (Real.log 2))
  simp only [mul_zero,zero_add,zero_mul] at h
  convert h using 1
  funext n
  unfold sourceTwoBandBudgetLogEnvelope
  simp only [Function.comp_apply,id_eq]
  ring

theorem sourceTwoBandConstructionBudget_le_exp (n : Nat) (hn : 1 ≤ n) :
    (sourceTwoBandConstructionBudget n : ℝ) ≤ Real.exp (sourceTwoBandBudgetLogEnvelope n) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn4 : (n : ℝ) ≤ (n : ℝ)^4 := le_self_pow₀ hn1 (by decide)
  have hQ : (1 : ℝ) ≤ (2 : ℝ)^(shrinkingBandWidth n) := one_le_pow₀ (by norm_num)
  have hP : (1 : ℝ) ≤ (2 : ℝ)^(targetNucleusLength n+1) := one_le_pow₀ (by norm_num)
  let Q := (2 : ℝ)^(shrinkingBandWidth n)
  let P := (2 : ℝ)^(targetNucleusLength n+1)
  have hf : (n : ℝ) ≤ (n : ℝ)^4*Q := hn4.trans
    (le_mul_of_one_le_right (by positivity) hQ)
  have hf1 : (1 : ℝ) ≤ (n : ℝ)^4*Q := hn1.trans hf
  have h1 : P ≤ (n : ℝ)^4*Q*P := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hf1) (show 0 ≤ P by positivity)]
  have h2 : (n : ℝ)^4*Q ≤ (n : ℝ)^4*Q*P := by
    nlinarith only [mul_nonneg (show 0 ≤ (n : ℝ)^4*Q by positivity) (sub_nonneg.mpr hP)]
  have h3 : (n : ℝ)*P ≤ (n : ℝ)^4*Q*P := mul_le_mul_of_nonneg_right hf (by positivity)
  have he : Real.exp (sourceTwoBandBudgetLogEnvelope n) = 3*(n : ℝ)^4*Q*P := by
    unfold sourceTwoBandBudgetLogEnvelope Q P
    rw [Real.exp_add,Real.exp_add,Real.exp_log (by norm_num : (0 : ℝ)<3),
      show (4 : ℝ)*Real.log (n : ℝ) = Real.log ((n : ℝ)^4) by norm_num [Real.log_pow],
      Real.exp_log (by positivity : (0 : ℝ)<(n : ℝ)^4)]
    rw [show ((shrinkingBandWidth n : ℝ)+(targetNucleusLength n : ℝ)+1)*Real.log 2 =
      Real.log ((2 : ℝ)^(shrinkingBandWidth n)) + Real.log ((2 : ℝ)^(targetNucleusLength n+1)) by
        rw [Real.log_pow,Real.log_pow]; push_cast; ring]
    rw [Real.exp_add,Real.exp_log (by positivity),Real.exp_log (by positivity)]
    ring
  rw [he]
  simp only [sourceTwoBandConstructionBudget,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  change P + ((n : ℝ)^3*Q+P)*(n : ℝ) ≤ 3*(n : ℝ)^4*Q*P
  nlinarith only [h1,h2,h3]

/-- The exact natural-number budget is eventually smaller than every
positive exponential scale. All floor and ceiling choices are retained. -/
theorem sourceTwoBandConstructionBudget_subexponential {c : ℝ} (hc : 0<c) :
    ∀ᶠ n : Nat in atTop, (sourceTwoBandConstructionBudget n : ℝ) < (2 : ℝ)^(c*(n : ℝ)) := by
  have hc2 : 0 < c*Real.log 2 := mul_pos hc (Real.log_pos (by norm_num))
  have hb := sourceTwoBandBudgetLogEnvelope_relative_tendsto.eventually (gt_mem_nhds hc2)
  filter_upwards [hb,eventually_ge_atTop 1] with n hh hn
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  apply (sourceTwoBandConstructionBudget_le_exp n hn).trans_lt
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ)<2)]
  apply Real.exp_lt_exp.mpr
  have h := (div_lt_iff₀ hn0).mp hh
  nlinarith only [h]

end
end PowerLawSmallRAF

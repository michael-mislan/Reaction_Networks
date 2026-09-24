import proofs.PowerLawSmallRAF.FiniteSeedRAFAssembly
import proofs.PowerLawSmallRAF.SourceTwoBandBudgetScale

namespace PowerLawSmallRAF
open RAF.Polymer Filter Topology
noncomputable section

theorem sourceFiniteSeedBudget_le_multiple (N n : Nat) :
    sourceFiniteSeedConstructionBudget N n ≤ (Fintype.card (Reaction N)+1)*sourceTwoBandConstructionBudget n := by
  have hP : 1 ≤ 2^(targetNucleusLength n+1) := Nat.one_le_pow _ _ (by omega)
  have hb : n+1 ≤ sourceTwoBandConstructionBudget n := by
    unfold sourceTwoBandConstructionBudget
    have hsum : 1 ≤ n^3*2^shrinkingBandWidth n+2^(targetNucleusLength n+1) := by omega
    calc
      n+1 = 1+1*n := by omega
      _ ≤ _ := Nat.add_le_add hP (Nat.mul_le_mul_right n hsum)
  have he : sourceFiniteSeedConstructionBudget N n = sourceTwoBandConstructionBudget n +
      Fintype.card (Reaction N)*(n+1) := by
    unfold sourceFiniteSeedConstructionBudget sourceTwoBandConstructionBudget
    ring
  rw [he]
  nlinarith [Nat.mul_le_mul_left (Fintype.card (Reaction N)) hb]

def sourceFiniteSeedBudgetLog (N n : Nat) : ℝ :=
  Real.log ((Fintype.card (Reaction N) : ℝ)+1) + sourceTwoBandBudgetLogEnvelope n

theorem sourceFiniteSeedBudgetLog_relative_tendsto (N : Nat) :
    Tendsto (fun n => sourceFiniteSeedBudgetLog N n/(n : ℝ)) atTop (𝓝 0) := by
  have hi : Tendsto (fun n : Nat => Real.log ((Fintype.card (Reaction N) : ℝ)+1)/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [sourceFiniteSeedBudgetLog,add_div,add_zero] using hi.add sourceTwoBandBudgetLogEnvelope_relative_tendsto

theorem sourceFiniteSeedBudget_le_exp (N n : Nat) (hn : 1 ≤ n) :
    (sourceFiniteSeedConstructionBudget N n : ℝ) ≤ Real.exp (sourceFiniteSeedBudgetLog N n) := by
  have hh : (sourceFiniteSeedConstructionBudget N n : ℝ) ≤
      ((Fintype.card (Reaction N) : ℝ)+1)*(sourceTwoBandConstructionBudget n : ℝ) := by
    exact_mod_cast sourceFiniteSeedBudget_le_multiple N n
  apply hh.trans
  rw [sourceFiniteSeedBudgetLog,Real.exp_add,Real.exp_log (by positivity)]
  exact mul_le_mul_of_nonneg_left (sourceTwoBandConstructionBudget_le_exp n hn) (by positivity)

theorem sourceFiniteSeedBudget_subexponential (N : Nat) {c : ℝ} (hc : 0<c) :
    ∀ᶠ n : Nat in atTop, (sourceFiniteSeedConstructionBudget N n : ℝ) < (2 : ℝ)^(c*(n : ℝ)) := by
  have hc2 : 0<c*Real.log 2 := mul_pos hc (Real.log_pos (by norm_num))
  have hb := (sourceFiniteSeedBudgetLog_relative_tendsto N).eventually (gt_mem_nhds hc2)
  filter_upwards [hb,eventually_ge_atTop 1] with n hh hn
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  apply (sourceFiniteSeedBudget_le_exp N n hn).trans_lt
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ)<2)]
  apply Real.exp_lt_exp.mpr
  have h := (div_lt_iff₀ hn0).mp hh
  nlinarith only [h]

end
end PowerLawSmallRAF

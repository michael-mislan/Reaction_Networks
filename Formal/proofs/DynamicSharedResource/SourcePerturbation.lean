import proofs.DynamicSharedResource.FastRecoveryChecks

namespace DynamicSharedResource.Certificate
noncomputable section

def sourceModal (s : ℝ) (a : State) : State := inverse.mulVec (field s 1 (reconstruct a))
def sourceAllowance (i : Fin 8) : ℝ := (13/100000:ℝ)*|inverse i 0|

theorem regen_unit_bounds (u : State) (hu : Physical u) :
    0 ≤ regen 1 (u 0) ∧ regen 1 (u 0) ≤ 130 := by
  have hd : 0 < 873/10-u 0 := by linarith [denominator_separated u hu]
  unfold regen
  constructor
  · exact div_nonneg (mul_nonneg (by norm_num) (by linarith [hu.2.1])) hd.le
  · apply (div_le_iff₀ hd).mpr
    linarith [hu.1]

theorem source_field_difference (s : ℝ) (u : State) :
    field s 1 u = nominal u + sourceVector ((s-3/25)*regen 1 (u 0)) := by
  funext i
  fin_cases i <;> simp [field,nominal,sourceVector,regen]
  ring

theorem sourceModal_difference (s : ℝ) (a : State) (i : Fin 8) :
    sourceModal s a i-modalField a i = inverse i 0*((s-3/25)*regen 1 (reconstruct a 0)) := by
  unfold sourceModal
  rw [source_field_difference,Matrix.mulVec_add]
  simp only [Pi.add_apply,transformed_source,modalField,add_sub_cancel_left]

theorem sourceModal_bound (s : ℝ) (hs : |s-3/25| ≤ (1/1000000:ℝ))
    (a : State) (ha : InCube 1 a) (i : Fin 8) :
    |sourceModal s a i-modalField a i| ≤ sourceAllowance i := by
  rw [sourceModal_difference,abs_mul,abs_mul]
  have hr := regen_unit_bounds (reconstruct a) (outer_physical a ha)
  rw [abs_of_nonneg hr.1]
  have h := mul_le_mul hs hr.2 hr.1 (by norm_num : (0:ℝ) ≤ 1/1000000)
  have hh := mul_le_mul_of_nonneg_left h (abs_nonneg (inverse i 0))
  dsimp [sourceAllowance]
  nlinarith

set_option maxHeartbeats 8000000 in
theorem robust_recovery_check (i : Fin 8) :
    faceBudget recoveryR i+sourceAllowance i < rectVelocity i := by
  fin_cases i <;>
    norm_num [faceBudget,recoveryR,rectVelocity,sourceAllowance,inverse,A,b,nb,
      Finset.sum_erase_eq_sub,Fin.sum_univ_succ]

set_option maxHeartbeats 8000000 in
theorem robust_service_check (i : Fin 8) :
    faceBudget serviceR i+sourceAllowance i < rectVelocity i := by
  fin_cases i <;>
    norm_num [faceBudget,serviceR,rectVelocity,sourceAllowance,inverse,A,b,nb,
      Finset.sum_erase_eq_sub,Fin.sum_univ_succ]

end
end DynamicSharedResource.Certificate

import proofs.DynamicSharedResource.FastOutputs

namespace DynamicSharedResource.Certificate
noncomputable section
open scoped BigOperators

def storageCoeff (j : Fin 8) : ℝ := basis 0 j-basis 1 j-basis 2 j-basis 3 j-basis 4 j
def storageRadius : ℝ := ∑ j, |storageCoeff j| * serviceR j

theorem storage_expansion (a : State) :
    W (reconstruct a)-W center = ∑ j, storageCoeff j*a j := by
  simp [W,BG,BT,reconstruct,storageCoeff,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  ring

set_option maxHeartbeats 4000000 in
theorem storage_radius_check : 2*storageRadius < (1/10:ℝ) := by
  norm_num [storageRadius,storageCoeff,serviceR,basis,Fin.sum_univ_succ]
  all_goals simp
  all_goals norm_num

theorem storage_deviation (a : State) (ha : InRect serviceR a) :
    |W (reconstruct a)-W center| ≤ storageRadius := by
  rw [storage_expansion]
  calc
    _ ≤ ∑ j, |storageCoeff j*a j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (ha j) (abs_nonneg _)

theorem storage_range (a b : State) (ha : InRect serviceR a) (hb : InRect serviceR b) :
    |W (reconstruct a)-W (reconstruct b)| ≤ (1/10:ℝ) := by
  have h₁ := storage_deviation a ha
  have h₂ := storage_deviation b hb
  have h := abs_sub_le (W (reconstruct a)) (W center) (W (reconstruct b))
  rw [abs_sub_comm (W center)] at h
  linarith [storage_radius_check]

end
end DynamicSharedResource.Certificate

import proofs.DynamicSharedResource.FastRecoveryChecks

namespace DynamicSharedResource.Certificate
noncomputable section
open scoped BigOperators

def rectG (q : State) : ℝ := (21/100)*(50-center 2-center 3-rectWidth q 2-rectWidth q 3)
def rectY (q : State) : ℝ := 101/200-center 4-rectWidth q 4
def rectV (q : State) : ℝ := center 7-rectWidth q 7
def rectT (q : State) : ℝ := (21/10)*rectY q*rectV q

theorem rect_displacement (q a : State) (ha : InRect q a) (i : Fin 8) :
    |basis.mulVec a i| ≤ rectWidth q i := by
  calc
    _ ≤ ∑ j, |basis i j*a j| := by
      simpa only [Matrix.mulVec,dotProduct] using
        Finset.abs_sum_le_sum_abs (fun j => basis i j*a j) Finset.univ
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (ha j) (abs_nonneg _)

theorem rect_service_bounds (q a : State) (ha : InRect q a)
    (hy : 0 ≤ rectY q) (hv : 0 ≤ rectV q) :
    rectG q ≤ HG (reconstruct a) ∧ rectT q ≤ HT (reconstruct a) := by
  have h2 := abs_le.mp (rect_displacement q a ha 2)
  have h3 := abs_le.mp (rect_displacement q a ha 3)
  have h4 := abs_le.mp (rect_displacement q a ha 4)
  have h7 := abs_le.mp (rect_displacement q a ha 7)
  have hyb : rectY q ≤ y (reconstruct a) := by
    dsimp [rectY,y,reconstruct]
    linarith
  have hvb : rectV q ≤ reconstruct a 7 := by
    dsimp [rectV,reconstruct]
    linarith
  constructor
  · dsimp [rectG,HG,e0,reconstruct]
    linarith
  · have hp := mul_le_mul hyb hvb hv (hy.trans hyb)
    dsimp [rectT,HT]
    nlinarith

set_option maxHeartbeats 4000000 in
theorem recovery_output_checks :
    0 ≤ rectY recoveryR ∧ 0 ≤ rectV recoveryR ∧
    (207/20:ℝ) ≤ rectG recoveryR ∧ (391/100:ℝ) ≤ rectT recoveryR := by
  norm_num [rectG,rectY,rectV,rectT,rectWidth,recoveryR,center,basis,Fin.sum_univ_succ]
  all_goals simp
  all_goals norm_num

set_option maxHeartbeats 4000000 in
theorem service_output_checks :
    0 ≤ rectY serviceR ∧ 0 ≤ rectV serviceR ∧
    (207/20:ℝ) ≤ rectG serviceR ∧ (401/100:ℝ) ≤ rectT serviceR := by
  norm_num [rectG,rectY,rectV,rectT,rectWidth,serviceR,center,basis,Fin.sum_univ_succ]
  all_goals simp
  all_goals norm_num

theorem recovery_outputs (a : State) (ha : InRect recoveryR a) :
    (207/20:ℝ) ≤ HG (reconstruct a) ∧ (391/100:ℝ) ≤ HT (reconstruct a) := by
  have h := recovery_output_checks
  have hb := rect_service_bounds recoveryR a ha h.1 h.2.1
  exact ⟨h.2.2.1.trans hb.1,h.2.2.2.trans hb.2⟩

theorem service_outputs (a : State) (ha : InRect serviceR a) :
    (207/20:ℝ) ≤ HG (reconstruct a) ∧ (401/100:ℝ) ≤ HT (reconstruct a) := by
  have h := service_output_checks
  have hb := rect_service_bounds serviceR a ha h.1 h.2.1
  exact ⟨h.2.2.1.trans hb.1,h.2.2.2.trans hb.2⟩

end
end DynamicSharedResource.Certificate

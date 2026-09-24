import proofs.RAF1519.Refinement.RelaxedMission

namespace RAF1519.Refinement.Relaxed
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability FiniteCopyReactor
open scoped ENNReal BigOperators

def exampleVolume : ℕ := 224000000000000
def exampleCounts : MolecularState 2 := fun q =>
  if q.1=0 then ![19*exampleVolume/20,19*exampleVolume/20,exampleVolume/20,0,0,0,0] q.2
  else ![13*exampleVolume/14,13*exampleVolume/14,0,0,exampleVolume/28,0,0] q.2

theorem exampleCounts_ready : ∀ i, Ready (1/100)
    (concentration exampleVolume (fun s => exampleCounts (i,s))) := by
  intro i
  constructor
  · intro s
    unfold concentration
    positivity
  fin_cases i <;>
    dsimp [concentration, exampleCounts, exampleVolume, materialA, materialB,
      stock, free, ProductiveRecovery.A, ProductiveRecovery.B, ProductiveRecovery.Y] <;> norm_num

theorem connected_mission_bound : (99/100:ℝ) < 1-100*cycleError 2 exampleVolume 1 := by
  have h := mul_le_mul_of_nonneg_right exp_fourteen_certificate (Real.exp_pos (-14)).le
  rw [← Real.exp_add] at h
  norm_num at h
  norm_num [cycleError, exampleVolume]
  linarith

theorem connected_hundred_cycle_mission
    (r d : Fin 2 → ℝ) (hr : ∀ i, 19 ≤ r i ∧ r i ≤ 21)
    (hd : ∀ i, 1/50 ≤ d i ∧ d i ≤ 1/25)
    (policy : ReturnedHistory 2 → Fin 2 → Intervention) :
    let R := returnedPhysicalHistory (by norm_num : 0 < 2) r d exampleExchange exampleVolume
      (fun i => le_trans (by norm_num) (hr i).1) (fun i => le_trans (by norm_num) (hd i).1)
      exampleExchange_nonneg (by norm_num [exampleVolume]) exampleCounts policy
    ENNReal.ofReal (99/100) < fullHistoryKernel R.step 100 [] (historyMission R) := by
  dsimp only
  have hl := returned_mission (by norm_num : 0 < 2) r d exampleExchange exampleVolume
    (by norm_num [exampleVolume]) 1 (by norm_num) hr hd exampleExchange_nonneg
    exampleExchange_symmetric exampleExchange_degree exampleCounts exampleCounts_ready policy 100
  have hb := ENNReal.ofReal_lt_ofReal_iff_of_nonneg
    (q := 1-100*cycleError 2 exampleVolume 1) (by norm_num : (0:ℝ) ≤ 99/100)
  exact (hb.mpr connected_mission_bound).trans_le hl

#print axioms connected_hundred_cycle_mission
end
end RAF1519.Refinement.Relaxed

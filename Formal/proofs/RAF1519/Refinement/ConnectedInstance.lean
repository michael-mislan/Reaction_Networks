import proofs.RAF1519.Refinement.ReturnedHistory

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability FiniteCopyReactor
open scoped ENNReal BigOperators

def exampleVolume : ℕ := 22400000000000000
def exampleExchange (i j : Fin 2) : ℝ := if i=j then 0 else 1
def exampleCounts : MolecularState 2 := fun q =>
  if q.1=0 then ![19*exampleVolume/20,19*exampleVolume/20,exampleVolume/20,0,0,0,0] q.2
  else ![13*exampleVolume/14,13*exampleVolume/14,0,0,exampleVolume/28,0,0] q.2

theorem exampleExchange_nonneg : ∀ i j, 0 ≤ exampleExchange i j := by
  intro i j
  unfold exampleExchange
  split_ifs <;> norm_num

theorem exampleExchange_symmetric : ∀ i j, exampleExchange i j=exampleExchange j i := by
  intro i j
  simp only [exampleExchange, eq_comm]

theorem exampleExchange_degree : ∀ i, (∑ j, exampleExchange i j) ≤ 1 := by
  intro i
  fin_cases i <;> norm_num [Fin.sum_univ_two, exampleExchange]

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

theorem exp_fourteen_certificate : (600000:ℝ) ≤ Real.exp 14 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 14) 16
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

theorem connected_mission_bound : (99/100:ℝ) < 1-100*cycleError 2 exampleVolume 1 := by
  have h := mul_le_mul_of_nonneg_right exp_fourteen_certificate (Real.exp_pos (-14)).le
  rw [← Real.exp_add] at h
  norm_num at h
  norm_num [cycleError, exampleVolume]
  linarith

end
end RAF1519.Refinement

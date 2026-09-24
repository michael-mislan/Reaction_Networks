import proofs.SerialTransferSelection.ManyCycleShare
import proofs.SerialTransferSelection.GeometricEligibility

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

def refinedM : ℕ := 1000000000000000

theorem shareCycleError_split (N M JB JR : ℕ) (qb qr t q ε : ℝ) :
    shareCycleError N M JB JR qb qr t q ε =
      chemicalCycleError N M t + 16/(ε^2*(M : ℝ)*q)+t*qb/JB+(M : ℝ)*(5376*qr/JR) := by
  unfold shareCycleError chemicalCycleError
  ring

theorem share_transfer_identity (M j : ℕ) (hM : 0 < M) :
    16/((1/50 : ℝ)^2*(M : ℝ)*shareFloor j) =
      80000/(M : ℝ)*(204/49 : ℝ)^j := by
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hM
  have hp : (49/204 : ℝ)^j ≠ 0 := pow_ne_zero _ (by norm_num)
  have hi : (204/49 : ℝ)^j = ((49/204 : ℝ)^j)⁻¹ := by
    rw [← inv_pow]
    norm_num
  rw [hi]
  unfold shareFloor
  field_simp [hm,hp]
  ring

theorem share_geometric_budget (N M JB JR K : ℕ) (hM : 0 < M) (qb qr t : ℝ) :
    historyBudget (fun j => shareCycleError N M JB JR qb qr t (shareFloor j) (1/50)) K 0 =
      (K : ℝ)*(chemicalCycleError N M t+t*qb/JB+(M : ℝ)*(5376*qr/JR))+
      80000/(M : ℝ)*historyBudget (fun j => (204/49 : ℝ)^j) K 0 := by
  simp_rw [shareCycleError_split,share_transfer_identity M _ hM]
  rw [historyBudget_add,historyBudget_add,historyBudget_add,
    historyBudget_mul_left,historyBudget_const,historyBudget_const,historyBudget_const]
  ring

theorem refined_chemical_bound : chemicalCycleError tenCycleN refinedM candidateTime ≤ 1/10^6 := by
  apply le_trans _ tenCycle_chemical_bound
  have hm : (refinedM : ℝ) ≤ tenCycleM := by norm_num [refinedM,tenCycleM]
  unfold chemicalCycleError phaseChemicalRawError recoveryError partitionError
    localAlpha innerEnergy outerEnergy candidateTime
  dsimp only
  gcongr

theorem refined_transfer_bound :
    80000/(refinedM : ℝ)*historyBudget (fun j => (204/49 : ℝ)^j) 10 0 < 1/5000 := by
  norm_num [historyBudget,refinedM]

theorem refined_tenCycle_error (JB JR : ℕ) (qb qr : ℝ)
    (hb : candidateTime*qb/JB < 1/10000)
    (hr : (refinedM : ℝ)*(5376*qr/JR) < 1/10000) :
    historyBudget (fun j => shareCycleError tenCycleN refinedM JB JR qb qr
      candidateTime (shareFloor j) (1/50)) 10 0 < 1/100 := by
  rw [share_geometric_budget _ _ _ _ _ (by norm_num [refinedM])]
  have ht := refined_transfer_bound
  have hc := refined_chemical_bound
  norm_num only [Nat.cast_ofNat]
  linarith

theorem tenCycle_population_improvement : 100000*refinedM=tenCycleM := by
  norm_num [refinedM,tenCycleM]

end SerialTransferSelection

import proofs.SerialTransferSelection.ManyCycleBaseline
import proofs.SerialTransferSelection.NonvacuousInstance

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

def tenCycleN : ℕ := 262144000000000000000000
def tenCycleM : ℕ := 100000000000000000000

theorem exp_negative_integer_bound (k : ℕ) (x : ℝ) (hx : (k : ℝ) ≤ x) :
    Real.exp (-x) ≤ 1/(2 : ℝ)^k := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h1 k
  have he : (Real.exp 1)^k = Real.exp (k : ℝ) := by
    rw [← Real.exp_nat_mul]
    simp
  rw [he] at hp
  calc
    Real.exp (-x) ≤ Real.exp (-(k : ℝ)) := Real.exp_le_exp.mpr (neg_le_neg hx)
    _ = 1 / Real.exp (k : ℝ) := by rw [Real.exp_neg, inv_eq_one_div]
    _ ≤ 1 / (2 : ℝ)^k := one_div_le_one_div_of_le (by positivity) hp

noncomputable def chemicalCycleError (N M : ℕ) (t : ℝ) : ℝ :=
  phaseChemicalRawError N M t + Real.exp (-(N : ℝ)/2500) +
    Real.exp (-(19*(N : ℝ)/500000)) +
    (M : ℝ)*recoveryError ((N : ℝ)*localAlpha*innerEnergy)

theorem tenCycle_chemical_bound : chemicalCycleError tenCycleN tenCycleM candidateTime ≤ 1/10^6 := by
  have h (x : ℝ) (hx : 256 ≤ x) : Real.exp (-x) ≤ 1/10^70 :=
    (exp_negative_integer_bound 256 x hx).trans (by norm_num)
  have h1 := h 3584 (by norm_num)
  have h2 := h 2048 (by norm_num)
  have h3 := h 3840 (by norm_num)
  have h4 := h 512 (by norm_num)
  have h5 := h 768 (by norm_num)
  have h6 := h ((tenCycleN : ℝ)/(35*10^12)) (by norm_num [tenCycleN])
  have h7 := h ((tenCycleN : ℝ)/2500) (by norm_num [tenCycleN])
  have h8 := h (19*(tenCycleN : ℝ)/500000) (by norm_num [tenCycleN])
  have h9 := h 256 (by norm_num)
  have h10 := h 4096 (by norm_num)
  have h11 := h 7936 (by norm_num)
  unfold chemicalCycleError
  rw [phaseChemicalRawError_expanded]
  norm_num [tenCycleN,tenCycleM,candidateTime,localAlpha,innerEnergy,outerEnergy,
    partitionError,recoveryError] at h6 h7 h8 ⊢
  linarith only [h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11]

theorem sourceCycleError_chemical_split (N M JB JR : ℕ) (qb qr t p ε : ℝ) :
    sourceCycleError N M JB JR qb qr t p ε =
      chemicalCycleError N M t + 32/(ε^2*p*(M : ℝ)) + t*qb/JB + (M : ℝ)*(5376*qr/JR) := by
  unfold sourceCycleError chemicalCycleError
  ring

theorem historyBudget_add (a b : ℕ → ℝ) (k j : ℕ) :
    historyBudget (fun i => a i+b i) k j = historyBudget a k j+historyBudget b k j := by
  induction k generalizing j with
  | zero => simp [historyBudget]
  | succ k ih => simp only [historyBudget,ih]; ring

theorem historyBudget_const (a : ℝ) (k j : ℕ) : historyBudget (fun _ => a) k j = k*a := by
  induction k generalizing j with
  | zero => simp [historyBudget]
  | succ k ih => simp only [historyBudget,ih,Nat.cast_add,Nat.cast_one]; ring

theorem tenCycle_transfer_bound :
    historyBudget (fun j => 32/((1/50 : ℝ)^2*baselineFloor j*(tenCycleM : ℝ))) 10 0 < 1/5000 := by
  norm_num [historyBudget,baselineFloor,tenCycleM]

theorem tenCycle_error_bound (JB JR : ℕ) (qb qr : ℝ)
    (hb : candidateTime*qb/JB < 1/10000)
    (hr : (tenCycleM : ℝ)*(5376*qr/JR) < 1/10000) :
    historyBudget (fun j => sourceCycleError tenCycleN tenCycleM JB JR qb qr
      candidateTime (baselineFloor j) (1/50)) 10 0 < 1/100 := by
  simp_rw [sourceCycleError_chemical_split]
  rw [historyBudget_add,historyBudget_add,historyBudget_add]
  simp only [historyBudget_const]
  have ht := tenCycle_transfer_bound
  have hc := tenCycle_chemical_bound
  norm_num only [Nat.cast_ofNat] at *
  linarith

end SerialTransferSelection

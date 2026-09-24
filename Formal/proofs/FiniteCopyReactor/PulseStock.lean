import proofs.FiniteCopyReactor.Pulse
import proofs.FiniteCopyReactor.Restart

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding
open scoped BigOperators

def speciesWeight : Fin 6 → ℝ := ![0,0,1,9/8,7/5,9/5]
def moleculeWeight (N : Counts) (m : Molecules N) : ℝ := speciesWeight m.1

theorem moleculeWeight_bounds (N : Counts) (m : Molecules N) :
    0 ≤ moleculeWeight N m ∧ moleculeWeight N m ≤ 9/5 := by
  obtain ⟨i,k⟩ := m
  fin_cases i <;> norm_num [moleculeWeight, speciesWeight]

theorem moleculeWeight_total (N : Counts) :
    ∑ m, moleculeWeight N m = weightedCount N := by
  rw [Fintype.sum_sigma]
  simp only [moleculeWeight, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  norm_num [speciesWeight, Fin.sum_univ_succ, weightedCount, weighted, Fin.succ]
  change (N 2:ℝ)+((N 3:ℝ)*(9/8)+((N 4:ℝ)*(7/5)+(N 5:ℝ)*(9/5))) = _
  ring

/-- The concrete catalytic pulse tail, with no assumed phase abundance. -/
theorem restart_pulse_stock_tail (N : Counts) (V : ℕ) (p : Intervention)
    (hN : Restart V N) :
    pulseTail N p (moleculeWeight N) ((3/250)*(V:ℝ)) ≤
      Real.exp (-(1177/1000000000)*(V:ℝ)) := by
  apply pulse_stock_tail N p (moleculeWeight N) V
    (fun m => (moleculeWeight_bounds N m).1) (fun m => (moleculeWeight_bounds N m).2)
  rw [moleculeWeight_total]
  have h : (2:ℝ)*V ≤ (stockInteger N:ℝ) := by exact_mod_cast hN.2.2.2.2
  rw [stock_integer_real] at h
  linarith

end
end FiniteCopyReactor

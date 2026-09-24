import proofs.CompositionalMemory.ControlledTerminalTransport
import proofs.CompositionalMemory.ControlledCheckedRows

namespace CompositionalMemory.ControlledRows
open FiniteIntegerRows

theorem all_array_bounds (N : Nat) (data : Nat → Array Int)
    (hrows : ∀ m, N ≤ m → m < 2*N → ControlledRows.checkLayer m (data m) (data (m+1))=true)
    (ht : ControlledRows.terminalCheck N (data (2*N))=true)
    (j : Fin (N+1)) (i : Nat) (hi : i < stateCount (N+j.val)) :
    (∀ col : Fin 2, value (data (N+j.val)) i col.val ≤ precisionScale) ∧
      precisionScale ≤ value (data (N+j.val)) i 2 := by
  by_cases hj : j.val=N
  · have hm : N+j.val=2*N := by omega
    rw [hm] at hi ⊢
    have hr := checked_terminal_rewards N (data (2*N)) ht i hi
    have hS : (0 : ℝ) < (precisionScale : ℝ) := by norm_num [precisionScale]
    constructor
    · intro col
      have hh : (value (data (2*N)) i col.val : ℝ)/(precisionScale : ℝ) ≤ 1 := by
        fin_cases col
        · exact hr.2.1.trans (terminalReward_bounds N _ _ 0).2
        · exact hr.2.2.2.1.trans (terminalReward_bounds N _ _ 1).2
      have hh' := (div_le_one hS).mp hh
      exact_mod_cast hh'
    · have hw := (of_decide_eq_true (terminal_checked_row N (data (2*N)) ht i hi)).2.2.2.2
      rw [hw]
  · have hr := of_decide_eq_true (checked_row (N+j.val) _ _
      (hrows (N+j.val) (by omega) (by omega)) i hi)
    refine ⟨?_,hr.2.2.2.2.2⟩
    intro col
    fin_cases col
    · exact hr.2.2.2.1
    · exact hr.2.2.2.2.1

end CompositionalMemory.ControlledRows

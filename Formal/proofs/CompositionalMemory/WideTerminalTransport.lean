import proofs.CompositionalMemory.WideTerminalPayoff

namespace CompositionalMemory.FiniteIntegerRows
set_option maxHeartbeats 40000
attribute [local irreducible] splitNumerator

theorem range_map_value (n i : Nat) (hi : i < n) (f : Nat → Nat) :
    ((Array.range n).map f)[i]! = f i := by
  simp [getElem!_pos,hi]

theorem terminal_checked_row (v : Array Int) (h : terminalCheck v=true)
    (i : Nat) (hi : i < stateCount 50) :
    terminalRow v i (splitNumerator (i/201) 3 50) (splitNumerator (i%201) 0 4)
      (splitNumerator (i/201) 175 350) (splitNumerator (i%201) 3 62)=true := by
  have hall := (Bool.and_eq_true_iff.mp h).2
  have hh := (List.all_eq_true.mp hall) i (List.mem_range.mpr hi)
  have hx : i/201 < 801 := by norm_num [stateCount] at hi; omega
  have hy : i%201 < 201 := Nat.mod_lt _ (by norm_num)
  simpa only [range_map_value 801 (i/201) hx,range_map_value 201 (i%201) hy] using hh

theorem integer_terminal_fraction (z : Int) (a b n : Nat)
    (h : z*(2 : Int)^n ≤ scale*(a : Int)*b) :
    (z : ℝ)/(scale : ℝ) ≤ (a : ℝ)*(b : ℝ)/(2 : ℝ)^n := by
  have hh : (z : ℝ)*(2 : ℝ)^n ≤ (scale : ℝ)*(a : ℝ)*(b : ℝ) := by
    exact_mod_cast h
  apply (div_le_div_iff₀ (by norm_num [scale]) (by positivity)).mpr
  simpa only [mul_assoc,mul_comm,mul_left_comm] using hh

theorem checked_terminal_rewards (v : Array Int) (h : terminalCheck v=true)
    (i : Nat) (hi : i < stateCount 50) :
    0 ≤ (value v i 0 : ℝ)/(scale : ℝ) ∧
    (value v i 0 : ℝ)/(scale : ℝ) ≤ exactTerminalReward (i/201) (i%201) 0 ∧
    0 ≤ (value v i 1 : ℝ)/(scale : ℝ) ∧
    (value v i 1 : ℝ)/(scale : ℝ) ≤ exactTerminalReward (i/201) (i%201) 1 ∧
    (value v i 2 : ℝ)/(scale : ℝ)=1 := by
  have hh := of_decide_eq_true (terminal_checked_row v h i hi)
  have h0 : (0 : ℝ) ≤ (value v i 0 : ℝ) := by exact_mod_cast hh.1
  have h1 : (0 : ℝ) ≤ (value v i 1 : ℝ) := by exact_mod_cast hh.2.1
  have hS : (0 : ℝ) < (scale : ℝ) := by norm_num [scale]
  refine ⟨div_nonneg h0 hS.le,?_,div_nonneg h1 hS.le,?_,?_⟩
  · simpa only [exactTerminalReward,if_pos rfl] using
      integer_terminal_fraction _ _ _ _ hh.2.2.1
  · simpa only [exactTerminalReward,show ¬(1 : Nat)=0 by decide,if_false] using
      integer_terminal_fraction _ _ _ _ hh.2.2.2.1
  · rw [hh.2.2.2.2]
    exact div_self (ne_of_gt hS)

end CompositionalMemory.FiniteIntegerRows

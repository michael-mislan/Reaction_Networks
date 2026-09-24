import proofs.CompositionalMemory.ControlledIntegerRows
import proofs.CompositionalMemory.WidePayoffBounds

namespace CompositionalMemory.ControlledRows
open FiniteIntegerRows
attribute [local irreducible] splitNumerator

noncomputable def terminalReward (N x y col : Nat) : ℝ :=
  if col=0 then
    (splitNumerator x ((N+9)/10) (2*N) : ℝ)*splitNumerator y 0 (4*N/25)/(2 : ℝ)^(x+y)
  else
    (splitNumerator x (7*N) (14*N) : ℝ)*splitNumerator y ((N+9)/10) (25*N/10)/(2 : ℝ)^(x+y)

theorem terminalReward_bounds (N x y col : Nat) :
    0 ≤ terminalReward N x y col ∧ terminalReward N x y col ≤ 1 := by
  unfold terminalReward
  split_ifs <;> exact splitReward_bounds _ _ _ _ _ _

theorem terminal_checked_row (N : Nat) (v : Array Int) (h : terminalCheck N v=true)
    (i : Nat) (hi : i < stateCount (2*N)) :
    terminalRow N v i
      (splitNumerator (i/(8*N+1)) ((N+9)/10) (2*N))
      (splitNumerator (i%(8*N+1)) 0 (4*N/25))
      (splitNumerator (i/(8*N+1)) (7*N) (14*N))
      (splitNumerator (i%(8*N+1)) ((N+9)/10) (25*N/10))=true := by
  have hall := (Bool.and_eq_true_iff.mp h).2
  have hh := (List.all_eq_true.mp hall) i (List.mem_range.mpr hi)
  have hs : stateCount (2*N)=(32*N+1)*(8*N+1) := by dsimp [stateCount]; ring
  have hx : i/(8*N+1) < 32*N+1 := by
    apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
    rw [hs] at hi
    simpa only [Nat.mul_comm] using hi
  have hy : i%(8*N+1) < 8*N+1 := Nat.mod_lt _ (by omega)
  simpa only [range_map_value (32*N+1) (i/(8*N+1)) hx,
    range_map_value (8*N+1) (i%(8*N+1)) hy] using hh

theorem integer_terminal_fraction (z : Int) (a b n : Nat)
    (h : z*(2 : Int)^n ≤ precisionScale*(a : Int)*b) :
    (z : ℝ)/(precisionScale : ℝ) ≤ (a : ℝ)*(b : ℝ)/(2 : ℝ)^n := by
  have hh : (z : ℝ)*(2 : ℝ)^n ≤ (precisionScale : ℝ)*(a : ℝ)*(b : ℝ) := by
    exact_mod_cast h
  apply (div_le_div_iff₀ (by norm_num [precisionScale]) (by positivity)).mpr
  simpa only [mul_assoc,mul_comm,mul_left_comm] using hh

theorem checked_terminal_rewards (N : Nat) (v : Array Int) (h : terminalCheck N v=true)
    (i : Nat) (hi : i < stateCount (2*N)) :
    0 ≤ (value v i 0 : ℝ)/(precisionScale : ℝ) ∧
    (value v i 0 : ℝ)/(precisionScale : ℝ) ≤ terminalReward N (i/(8*N+1)) (i%(8*N+1)) 0 ∧
    0 ≤ (value v i 1 : ℝ)/(precisionScale : ℝ) ∧
    (value v i 1 : ℝ)/(precisionScale : ℝ) ≤ terminalReward N (i/(8*N+1)) (i%(8*N+1)) 1 ∧
    (value v i 2 : ℝ)/(precisionScale : ℝ)=1 := by
  have hh := of_decide_eq_true (terminal_checked_row N v h i hi)
  have h0 : (0 : ℝ) ≤ (value v i 0 : ℝ) := by exact_mod_cast hh.1
  have h1 : (0 : ℝ) ≤ (value v i 1 : ℝ) := by exact_mod_cast hh.2.1
  have hS : (0 : ℝ) < (precisionScale : ℝ) := by norm_num [precisionScale]
  refine ⟨div_nonneg h0 hS.le,?_,div_nonneg h1 hS.le,?_,?_⟩
  · simpa only [terminalReward,if_pos rfl] using integer_terminal_fraction _ _ _ _ hh.2.2.1
  · simpa only [terminalReward,show ¬(1 : Nat)=0 by decide,if_false] using
      integer_terminal_fraction _ _ _ _ hh.2.2.2.1
  · rw [hh.2.2.2.2]
    exact div_self (ne_of_gt hS)

end CompositionalMemory.ControlledRows

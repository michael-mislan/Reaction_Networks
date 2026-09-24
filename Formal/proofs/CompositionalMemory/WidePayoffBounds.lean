import proofs.CompositionalMemory.WideBirthTransport
import proofs.CompositionalMemory.FiniteGeneratorTransport

namespace CompositionalMemory
open FiniteCopy FiniteIntegerRows
set_option maxHeartbeats 50000

theorem splitNumerator_le (n lo hi : Nat) : splitNumerator n lo hi ≤ 2^n := by
  rw [← Nat.sum_range_choose]
  apply Finset.sum_le_sum
  intro k _
  split_ifs <;> omega

theorem splitReward_bounds (x y a b c d : Nat) :
    0 ≤ (splitNumerator x a b : ℝ)*(splitNumerator y c d : ℝ)/(2 : ℝ)^(x+y) ∧
    (splitNumerator x a b : ℝ)*(splitNumerator y c d : ℝ)/(2 : ℝ)^(x+y) ≤ 1 := by
  constructor
  · positivity
  · apply (div_le_one (by positivity)).mpr
    have hx : (splitNumerator x a b : ℝ) ≤ (2 : ℝ)^x := by exact_mod_cast splitNumerator_le x a b
    have hy : (splitNumerator y c d : ℝ) ≤ (2 : ℝ)^y := by exact_mod_cast splitNumerator_le y c d
    rw [pow_add]
    exact mul_le_mul hx hy (by positivity) (by positivity)

theorem exactTerminalReward_bounds (x y col : Nat) :
    0 ≤ exactTerminalReward x y col ∧ exactTerminalReward x y col ≤ 1 := by
  unfold exactTerminalReward
  split_ifs <;> exact splitReward_bounds _ _ _ _ _ _

noncomputable def wideExactPayoff (col : Nat) : WideFiniteState → ℝ
  | none => 0
  | some ⟨j,x,y⟩ => if j.val=25 then exactTerminalReward x.val y.val col else 0

theorem wideExactPayoff_bounds (col : Nat) (s : WideFiniteState) :
    0 ≤ wideExactPayoff col s ∧ wideExactPayoff col s ≤ 1 := by
  cases s with
  | none => norm_num [wideExactPayoff]
  | some s =>
    rcases s with ⟨j,x,y⟩
    dsimp only [wideExactPayoff]
    split_ifs
    · exact exactTerminalReward_bounds _ _ _
    · norm_num

theorem wideTerminalPayoff_bounds (data : Nat → Array Int)
    (ht : terminalCheck (data 50)=true) (col : Nat) (hc : col=0 ∨ col=1)
    (s : WideFiniteState) :
    0 ≤ wideTerminalPayoff data col s ∧ wideTerminalPayoff data col s ≤ wideExactPayoff col s := by
  cases s with
  | none => simp [wideTerminalPayoff,wideExactPayoff]
  | some s =>
    rcases s with ⟨j,x,y⟩
    by_cases hj : j.val=25
    · have hx : x.val < 801 := by simpa [hj] using x.isLt
      have hy : y.val < 201 := by simpa [hj] using y.isLt
      have hh := checked_terminal_rewards (data 50) ht (x.val*201+y.val)
        (by norm_num [stateCount]; omega)
      have hix : (x.val*201+y.val)/201=x.val := by omega
      have hiy : (x.val*201+y.val)%201=y.val := by omega
      rw [hix,hiy] at hh
      simp only [wideTerminalPayoff,wideExactPayoff,hj,if_true,wideValue]
      norm_num
      rcases hc with rfl | rfl
      · exact ⟨hh.1,hh.2.1⟩
      · exact ⟨hh.2.2.1,hh.2.2.2.1⟩
    · simp [wideTerminalPayoff,wideExactPayoff,hj]

theorem wide_newborn_exact_deadline (γ : ℝ) (hγ : 0 ≤ γ)
    (hg : |γ-1/10| ≤ 1/10000000) (data : Nat → Array Int) (lim : Nat → Limits)
    (hcheck : ∀ m, 25 ≤ m → m < 50 → checkLayer m (data m) (data (m+1)) (lim m)=true)
    (hlim : ∀ m, 25 ≤ m → m < 50 → limitsOK m (lim m)=true)
    (hterminal : terminalCheck (data 50)=true) (hbirth : birthOK (data 25)=true)
    (col : Nat) (x : Fin 401) (y : Fin 101) (hb : wideNewborn col x.val y.val) :
    (991/1000 : ℝ) ≤ finiteTimeExpectation (wideFiniteModel γ hγ) 20
      (wideExactPayoff col) (some ⟨0,x,y⟩) := by
  apply (wide_newborn_deadline γ hγ hg data lim hcheck hlim hterminal hbirth col x y hb).trans
  apply finite_time_mono
  intro s
  exact (wideTerminalPayoff_bounds data hterminal col (wide_newborn_count_bound col x.val y.val hb).2.2.2 s).2

end CompositionalMemory

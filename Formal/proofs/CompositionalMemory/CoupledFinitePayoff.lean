import proofs.CompositionalMemory.CoupledGlobalGenerator

namespace CompositionalMemory
open FiniteIntegerRows ControlledRows

noncomputable def coupledExactPayoff (N : Nat) (word : Fin 2 → Fin 2) :
    CoupledFiniteState N → ℝ
  | none => 0
  | some ⟨j,a⟩ => if j.val=N then
    terminalReward N (a 0).1.val (a 0).2.val (word 0).val*
    terminalReward N (a 1).1.val (a 1).2.val (word 1).val else 0

theorem coupledExactPayoff_bounds (N : Nat) (word : Fin 2 → Fin 2)
    (s : CoupledFiniteState N) : 0 ≤ coupledExactPayoff N word s ∧ coupledExactPayoff N word s ≤ 1 := by
  cases s with
  | none => norm_num [coupledExactPayoff]
  | some s =>
    rcases s with ⟨j,a⟩
    dsimp only [coupledExactPayoff]
    split_ifs
    · have h0 := terminalReward_bounds N (a 0).1.val (a 0).2.val (word 0).val
      have h1 := terminalReward_bounds N (a 1).1.val (a 1).2.val (word 1).val
      constructor
      · exact mul_nonneg h0.1 h1.1
      · nlinarith [mul_le_mul h0.2 h1.2 h1.1 (by norm_num : (0 : ℝ) ≤ 1)]
    · norm_num

theorem checked_terminal_coordinate (N : Nat) (v : Array Int)
    (ht : ControlledRows.terminalCheck N v=true) (x y : Nat)
    (hx : x ≤ 32*N) (hy : y ≤ 8*N) (col : Fin 2) :
    (value v (x*(8*N+1)+y) col.val : ℝ)/(precisionScale : ℝ) ≤ terminalReward N x y col.val := by
  have hm : 4*(2*N)+1=8*N+1 := by omega
  have hcoords := coupled_index_coordinates (2*N) x y (by omega)
  rw [hm] at hcoords
  have hi : x*(8*N+1)+y < stateCount (2*N) := by
    have hh := Nat.mul_le_mul_right (8*N+1) hx
    dsimp [stateCount]
    nlinarith only [hh,hy]
  have hr := checked_terminal_rewards N v ht (x*(8*N+1)+y) hi
  rw [hcoords.1,hcoords.2] at hr
  fin_cases col
  · exact hr.2.1
  · exact hr.2.2.2.1

theorem coupled_current_bounds (N : Nat) (data : Nat → Array Int)
    (hrows : ∀ m, N ≤ m → m < 2*N → ControlledRows.checkLayer m (data m) (data (m+1))=true)
    (ht : ControlledRows.terminalCheck N (data (2*N))=true)
    (s : CoupledLiveState N) (k : Fin 2) :
    (∀ col : Fin 2, coupledCurrent N data s k col.val ≤ 1) ∧ 1 ≤ coupledCurrent N data s k 2 := by
  let m := N+s.1.val
  let i := (s.2 k).1.val*(4*m+1)+(s.2 k).2.val
  have hi : i < stateCount m := by
    have hx := Nat.le_of_lt_succ (s.2 k).1.isLt
    have hy := Nat.le_of_lt_succ (s.2 k).2.isLt
    have hh := Nat.mul_le_mul_right (4*m+1) hx
    dsimp [m,i,stateCount] at hh ⊢
    nlinarith only [hh,hy]
  have hb := all_array_bounds N data hrows ht s.1 i hi
  have hS : (0 : ℝ) < (precisionScale : ℝ) := by norm_num [precisionScale]
  constructor
  · intro col
    apply (div_le_one hS).mpr
    exact_mod_cast hb.1 col
  · apply (le_div_iff₀ hS).mpr
    simpa using (show (precisionScale : ℝ) ≤ (value (data m) i 2 : ℝ) by exact_mod_cast hb.2)

theorem coupled_value_cover (N : Nat) (data : Nat → Array Int)
    (hrows : ∀ m, N ≤ m → m < 2*N → ControlledRows.checkLayer m (data m) (data (m+1))=true)
    (ht : ControlledRows.terminalCheck N (data (2*N))=true) (word : Fin 2 → Fin 2)
    (s : CoupledFiniteState N) :
    coupledJointValue N data word s ≤ coupledExactPayoff N word s+coupledJointTime N data s := by
  cases s with
  | none => norm_num [coupledJointValue,coupledExactPayoff,coupledJointTime]
  | some s =>
    rcases s with ⟨j,a⟩
    by_cases hj : j.val=N
    · have hb (k : Fin 2) : coupledCurrent N data ⟨j,a⟩ k (word k).val ≤
          terminalReward N (a k).1.val (a k).2.val (word k).val := by
        have hx : (a k).1.val ≤ 32*N := by have h := (a k).1.isLt; omega
        have hy : (a k).2.val ≤ 8*N := by have h := (a k).2.isLt; omega
        have hh := checked_terminal_coordinate N (data (2*N)) ht _ _ hx hy (word k)
        have hm : N+j.val=2*N := by omega
        simpa only [coupledCurrent,hm,show 4*(2*N)+1=8*N+1 by omega] using hh
      have hl := coupled_terminal_lower
        (terminalReward N (a 0).1.val (a 0).2.val (word 0).val)
        (terminalReward N (a 1).1.val (a 1).2.val (word 1).val)
        (terminalReward_bounds N _ _ _).2 (terminalReward_bounds N _ _ _).2
      simp only [coupledExactPayoff,coupledJointTime,hj,ite_true,add_zero]
      change coupledCurrent N data ⟨j,a⟩ 0 (word 0).val+
        coupledCurrent N data ⟨j,a⟩ 1 (word 1).val-1 ≤ _
      linarith only [hb 0,hb 1,hl]
    · have h0 := coupled_current_bounds N data hrows ht ⟨j,a⟩ 0
      have h1 := coupled_current_bounds N data hrows ht ⟨j,a⟩ 1
      have hw : coupledJointTime N data (some ⟨j,a⟩)=
          (coupledCurrent N data ⟨j,a⟩ 0 2+coupledCurrent N data ⟨j,a⟩ 1 2)/2 := by
        simp [coupledJointTime,coupledCurrent,hj]
        ring
      rw [hw]
      simp only [coupledExactPayoff,hj,ite_false,zero_add]
      change coupledCurrent N data ⟨j,a⟩ 0 (word 0).val+
        coupledCurrent N data ⟨j,a⟩ 1 (word 1).val-1 ≤ _
      linarith only [h0.1 (word 0),h1.1 (word 1),h0.2,h1.2]

end CompositionalMemory

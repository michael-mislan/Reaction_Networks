import proofs.CompositionalMemory.ReversibleGlobalGenerator
import proofs.CompositionalMemory.CoupledFinitePayoff

namespace CompositionalMemory
open FiniteIntegerRows ControlledRows

theorem reversible_current_bounds (N : Nat) (data : Nat → Array Int)
    (hrows : ∀ m, N ≤ m → m < 2*N → ReversibleRows.checkLayer m (data m) (data (m+1))=true)
    (ht : ReversibleRows.terminalCheck N (data (2*N))=true)
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
  have hb := ReversibleRows.all_array_bounds N data hrows ht s.1 i hi
  have hS : (0 : ℝ) < (precisionScale : ℝ) := by norm_num [precisionScale]
  constructor
  · intro col
    apply (div_le_one hS).mpr
    exact_mod_cast hb.1 col
  · apply (le_div_iff₀ hS).mpr
    simpa using (show (precisionScale : ℝ) ≤ (value (data m) i 2 : ℝ) by exact_mod_cast hb.2)

theorem reversible_value_cover (N : Nat) (data : Nat → Array Int)
    (hrows : ∀ m, N ≤ m → m < 2*N → ReversibleRows.checkLayer m (data m) (data (m+1))=true)
    (ht : ReversibleRows.terminalCheck N (data (2*N))=true) (word : Fin 2 → Fin 2)
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
    · have h0 := reversible_current_bounds N data hrows ht ⟨j,a⟩ 0
      have h1 := reversible_current_bounds N data hrows ht ⟨j,a⟩ 1
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

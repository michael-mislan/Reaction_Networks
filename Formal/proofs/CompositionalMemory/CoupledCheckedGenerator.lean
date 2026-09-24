import proofs.CompositionalMemory.CoupledLocalGenerator

namespace CompositionalMemory
open FiniteIntegerRows ControlledRows

theorem coupled_checked_local_bounds (N : Nat) (hN : 0 < N) (ε : ℝ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1/10) (data : Nat → Array Int)
    (hrows : ∀ m, N ≤ m → m < 2*N → ControlledRows.checkLayer m (data m) (data (m+1))=true)
    (s : CoupledLiveState N) (hs : s.1.val < N) (k : Fin 2) :
    -(1/1000000 : ℝ) ≤ coupledControlledLocal N ε data s k 0 ∧
    -(1/1000000 : ℝ) ≤ coupledControlledLocal N ε data s k 1 ∧
    coupledControlledLocal N ε data s k 2 ≤ -(5/8 : ℝ)*coupledCurrent N data s k 2+1/50000 := by
  let m := N+s.1.val
  let i := (s.2 k).1.val*(4*m+1)+(s.2 k).2.val
  let other : Fin 2 := ⟨1-k.val,by omega⟩
  have hm : 0 < m := by dsimp [m]; omega
  have hi : i < stateCount m := by
    have hx := Nat.le_of_lt_succ (s.2 k).1.isLt
    have hy := Nat.le_of_lt_succ (s.2 k).2.isLt
    have hh := Nat.mul_le_mul_right (4*m+1) hx
    dsimp [i,stateCount,m] at hh ⊢
    nlinarith only [hh,hy]
  have hrow := checked_row m (data m) (data (m+1))
    (hrows m (by dsimp [m]; omega) (by dsimp [m]; omega)) i hi
  have hc := coupled_control_ranges m hm (s.2 other).1.val (s.2 other).2.val
    (Nat.le_of_lt_succ (s.2 other).1.isLt) (Nat.le_of_lt_succ (s.2 other).2.isLt)
    ε hε hε1
  have hl := checked_literal_bounds m hm (data m) (data (m+1)) i hrow
    ((s.2 other).1.val/(16*(m : ℝ))) (5*ε*(s.2 other).2.val/(2*(m : ℝ)))
    hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  simp only [coupled_local_controlled_literal N hN ε data s hs]
  refine ⟨hl.1,hl.2.1,?_⟩
  convert hl.2.2 using 1
  dsimp [coupledCurrent,m,i]
  ring

end CompositionalMemory

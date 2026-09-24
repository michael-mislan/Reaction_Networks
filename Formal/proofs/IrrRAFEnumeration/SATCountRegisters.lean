import proofs.IrrRAFEnumeration.SATCountOps

namespace IrrRAFEnumeration.SATSource

open Complexity Complexity.TM

/-- Fixed stages: registers 0,1 hold n,m; 2,3,4,5 become W,q,M,R. -/
def countProgram : List CountOp :=
  [.add 0 2, .add 0 2, .add 0 2, .add 1 2, .inc 2,
   .add 0 3, .add 0 3, .add 0 3, .mul 0 1 3, .mul 0 1 3, .inc 3,
   .add 2 4, .add 3 4, .inc 4, .inc 4,
   .add 0 5, .add 0 5, .add 3 5, .inc 5]

def countInitial (n m : Nat) : Fin 6 → Nat := ![n,m,0,0,0,0]

theorem countProgram_valid : ∀ op ∈ countProgram, op.Valid := by
  intro op ho
  simp only [countProgram, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp [CountOp.Valid] <;> decide

theorem countProgram_value (n m : Nat) :
    countRun countProgram (countInitial n m) =
      ![n,m,3*n+m+1,3*n+2*n*m+1,6*n+2*n*m+m+4,5*n+2*n*m+2] := by
  funext i
  fin_cases i <;> simp [countRun, countProgram, countEval, countInitial] <;> ring

theorem countProgram_diagonal_cost (t : Nat) :
    countCost countProgram (countInitial t t) = 22*t^4+88*t^3+220*t^2+253*t+109 := by
  dsimp [countCost, countProgram, countOpCost, countEval, countInitial, mulAddBound, Function.update]
  ring

theorem countProgram_cost_bound (n m : Nat) :
    countCost countProgram (countInitial n m) ≤ 692*(n+m+1)^4 := by
  let L := n+m+1
  have hmono : countCost countProgram (countInitial n m) ≤
      countCost countProgram (countInitial L L) :=
    countCost_mono countProgram (by intro i; fin_cases i <;> simp [countInitial, L] <;> omega)
  rw [countProgram_diagonal_cost] at hmono
  have hL : 1 ≤ L := by dsimp [L]; omega
  have h₂ : L ≤ L^2 := by simpa using Nat.pow_le_pow_right hL (show 1 ≤ 2 by decide)
  have h₃ : L^2 ≤ L^3 := Nat.pow_le_pow_right hL (by decide)
  have h₄ : L^3 ≤ L^4 := Nat.pow_le_pow_right hL (by decide)
  change countCost countProgram (countInitial n m) ≤ 692*L^4
  nlinarith

theorem countRegistersTM_correct (n m : Nat) (inp : Tape) (ys : List Bool) (hp : Parked inp) :
    (countSeqTM countProgram).HoareTime (EmitPred inp (countTapes (countInitial n m)) ys)
      (EmitPred inp
        (countTapes ![n,m,3*n+m+1,3*n+2*n*m+1,6*n+2*n*m+m+4,5*n+2*n*m+2]) ys)
      (692*(n+m+1)^4) := by
  have h := countSeq_correct countProgram countProgram_valid (countInitial n m) inp ys hp
  rw [countProgram_value] at h
  exact h.mono_bound (countProgram_cost_bound n m)

end IrrRAFEnumeration.SATSource

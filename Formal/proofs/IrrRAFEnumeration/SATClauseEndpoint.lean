import proofs.IrrRAFEnumeration.SATClauseInner

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource Complexity Complexity.TM

def terminalWork (n m W Q M : Nat) (stream : Tape) : Fin 13 → Tape :=
  ![regTape 1,regTape (M-2),regTape W,regTape (Q-1),regTape 1,regTape (M-1),
    regTape n,regTape m,regTape W,regTape Q,regTape M,regTape (2*n),stream]

theorem clauseWork_endpoint {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    clauseWork Φ m 0 (regTape m) = terminalWork n m (Fintype.card (Wire n m))
      (Fintype.card (Step n m)) (moleculeCount n m) (cnfStreamCursor Φ (2*n*m)) := by
  funext i
  fin_cases i <;> simp [clauseWork,terminalWork,moleculeCount,wire_card,step_card,Nat.sub_sub]
  all_goals (congr 1; omega)

end IrrRAFEnumeration.SATSource

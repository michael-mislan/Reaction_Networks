import proofs.IrrRAFEnumeration.CompletionCatalystClause
import proofs.IrrRAFEnumeration.CompletionImplicationScan

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

def reactantStart (d r j : Nat) := d+r+3+d+3*d*j

theorem original_reactant_cell {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C] (j : Fin r) (x : Fin d) :
    (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _))).cells
      (reactantStart d r j.val+x.val) = Γ.ofBool (decide (x ∈ Q.inputs j)) := by
  have h := original_incidence_cell Q C (.inr (j,0,x))
  simpa [reactantStart,slotCode,incidence,finSumFinEquiv,finProdFinEquiv,
    Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_comm,Nat.mul_left_comm] using h

def reactantClauses {d r : Nat} (Q : CRS (Fin d) (Fin r)) (j : Fin r) : SAT.CNF :=
  PositiveCompletionCNF.each d (fun x => if x ∈ Q.inputs j then
    [PositiveCompletionCNF.implies (PositiveCompletionCNF.selectVar j)
      [PositiveCompletionCNF.rowVar r ⟨d,by omega⟩ x]] else [])

theorem reactant_implicationClauses {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C] (j : Fin r) :
    implicationClauses j.val (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
      (reactantStart d r j.val) (r+d*d) d = reactantClauses Q j := by
  have h := implicationClauses_eq_each j.val
    (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
    (reactantStart d r j.val) (r+d*d) d (fun x => decide (x ∈ Q.inputs j))
    (original_reactant_cell Q C j)
  simpa [reactantClauses,PositiveCompletionCNF.implies,PositiveCompletionCNF.positive,
    PositiveCompletionCNF.selectVar,PositiveCompletionCNF.rowVar] using h

def reactantRowTM : TM 5 := implicationScanTM

theorem reactantRowTM_correct {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C] (j : Fin r) (ys : List Bool) :
    reactantRowTM.HoareTime
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (implicationWork j.val (regTape d) (reactantStart d r j.val) (r+d*d) 0) ys)
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (implicationWork j.val (regTape d) (reactantStart d r j.val+d) (r+d*d+d) 0)
        (ys++SAT.CNF.encode (reactantClauses Q j)))
      (d*(5*reactantStart d r j.val+5*(r+d*d)+3*j.val+10*d+63)+d+2) := by
  have h := implicationScanTM_correct j.val
    (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
    (reactantStart d r j.val) (r+d*d) d ys (parkedInput_parked _) rfl rfl
  simpa [reactantRowTM,reactant_implicationClauses] using h

end IrrRAFEnumeration.CompletionQuery

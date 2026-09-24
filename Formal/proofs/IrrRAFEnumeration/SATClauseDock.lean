import proofs.IrrRAFEnumeration.SATClauseBody
import proofs.IrrRAFEnumeration.SATRunConstruction
import proofs.IrrRAFEnumeration.SATStreamInit

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource Complexity Complexity.TM

theorem clausePattern_eq_reactionRows {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (j : Fin m) (x : Choice n) :
    clausePattern ((choiceOffset n x).val+1) (moleculeCount n m-((choiceOffset n x).val+1)-1)
      (3*n+j.val+1) (3*n+m+(finProdFinEquiv (j,choiceOffset n x)).val-j.val)
      (Fintype.card (Step n m)-3*n-(finProdFinEquiv (j,choiceOffset n x)).val)
      (Fintype.card (Wire n m)+3*n+(finProdFinEquiv (j,choiceOffset n x)).val+2)
      (decide (x ∈ Φ j)) = reactionRows Φ (auxiliaryReaction (.clause j x)) := by
  let pos := (finProdFinEquiv (j,choiceOffset n x)).val
  have hcode : (stepCode n m (.clause j x)).val = 3*n+pos := by
    simp [stepCode,stepOffset,stepEquiv,finSumFinEquiv,pos]
    omega
  have hnext : 3*n+pos+1 < Fintype.card (Step n m)+1 := by
    have hi := (stepCode n m (.clause j x)).isLt
    rw [hcode] at hi
    omega
  have hcat : (catalystIndex (auxiliaryReaction (.clause j x))).val = 3*n+pos+1 := by
    simp only [auxiliaryReaction,catalystIndex,nextAux,Fin.val_castSucc,hcode,Nat.mod_eq_of_lt hnext]
  have hi := auxiliaryInputRow_correct Φ (.clause j x)
  change spanRow ((choiceOffset n x).val+1) 1 (moleculeCount n m-((choiceOffset n x).val+1)-1) = _ at hi
  have ho := auxiliaryOutputRow_correct Φ (.clause j x)
  simp only [auxiliaryOutputRow,signalOutput,wirePosition,hcode] at ho
  have hgap : 1+Fintype.card (Wire n m)+(3*n+pos)-(3*n+j.val+1)-1 =
      3*n+m+pos-j.val := by
    have hj := j.isLt
    rw [wire_card]
    omega
  have htail : moleculeCount n m-(1+Fintype.card (Wire n m)+(3*n+pos))-1 =
      Fintype.card (Step n m)-3*n-pos := by dsimp [moleculeCount]; omega
  rw [hgap,htail] at ho
  have hc := catalyst_row (m := m) (auxiliaryReaction (.clause j x))
  rw [hcat] at hc
  have hbefore : 1+Fintype.card (Wire n m)+(3*n+pos+1) =
      Fintype.card (Wire n m)+3*n+pos+2 := by omega
  have hafter : moleculeCount n m-(1+Fintype.card (Wire n m)+(3*n+pos+1))-1 =
      Fintype.card (Step n m)-3*n-pos-1 := by dsimp [moleculeCount]; omega
  rw [hafter,hbefore] at hc
  unfold clausePattern reactionRows
  rw [hi,ho,hc]

end IrrRAFEnumeration.SATSource

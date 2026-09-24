import proofs.IrrRAFEnumeration.SATTerminalBodies
import proofs.IrrRAFEnumeration.SATClausePrefix

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource

theorem finishPattern_eq_reactionRows {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    finishPattern n m (Fintype.card (Wire n m)) (Fintype.card (Step n m)) (moleculeCount n m) =
      reactionRows Φ (auxiliaryReaction (.finish)) := by
  have hq : 1 ≤ Fintype.card (Step n m) := by rw [step_card]; omega
  have hcode : (stepCode n m (.finish)).val = Fintype.card (Step n m)-1 := by
    simp [stepCode,stepOffset,stepEquiv,finSumFinEquiv,unitCode,step_card]
    ring
  have hcat : (catalystIndex (auxiliaryReaction (n := n) (m := m) (.finish))).val =
      Fintype.card (Step n m) := by
    simp only [auxiliaryReaction,catalystIndex,nextAux,Fin.val_castSucc,hcode,
      Nat.sub_add_cancel hq,Nat.mod_eq_of_lt (Nat.lt_succ_self _)]
  have hi := finish_input_row Φ
  rw [← wire_card n m] at hi
  have his : moleculeCount n m-Fintype.card (Wire n m) = Fintype.card (Step n m)+2 := by
    dsimp [moleculeCount]
    omega
  rw [his] at hi
  have ho := auxiliaryOutputRow_correct Φ (.finish)
  simp only [auxiliaryOutputRow,signalOutput,wirePosition,hcode] at ho
  rw [← wire_card n m] at ho
  have hg : 1+Fintype.card (Wire n m)+(Fintype.card (Step n m)-1)-Fintype.card (Wire n m)-1 =
      Fintype.card (Step n m)-1 := by omega
  have ht : moleculeCount n m-(1+Fintype.card (Wire n m)+(Fintype.card (Step n m)-1))-1 = 1 := by
    dsimp [moleculeCount]
    omega
  rw [hg,ht] at ho
  have hc := catalyst_row (m := m) (auxiliaryReaction (n := n) (m := m) (.finish))
  rw [hcat] at hc
  have hbefore : 1+Fintype.card (Wire n m)+Fintype.card (Step n m) = moleculeCount n m-1 := by
    dsimp [moleculeCount]
    omega
  have hafter : moleculeCount n m-(1+Fintype.card (Wire n m)+Fintype.card (Step n m))-1 = 0 := by
    dsimp [moleculeCount]
    omega
  rw [hafter,hbefore] at hc
  unfold finishPattern reactionRows
  rw [hi,ho,hc]

theorem resetPattern_eq_reactionRows {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    resetPattern (Fintype.card (Wire n m)) (Fintype.card (Step n m)) =
      reactionRows Φ (reset (n := Fintype.card (Choice n)) (q := Fintype.card (Step n m))) := by
  have hi := reset_input_row Φ
  rw [← wire_card n m] at hi
  have ht : moleculeCount n m-Fintype.card (Wire n m)-1 = Fintype.card (Step n m)+1 := by
    dsimp [moleculeCount]
    omega
  rw [ht] at hi
  have ho := reset_output_row Φ
  have hc := catalyst_row (m := m)
    (reset (n := Fintype.card (Choice n)) (q := Fintype.card (Step n m)))
  have hcat : (catalystIndex (reset (n := Fintype.card (Choice n))
      (q := Fintype.card (Step n m)))).val = 0 := by
    simp [reset,catalystIndex,nextAux]
  rw [hcat] at hc
  have hbefore : 1+Fintype.card (Wire n m)+0 = Fintype.card (Wire n m)+1 := by omega
  have hafter : moleculeCount n m-(1+Fintype.card (Wire n m)+0)-1 = Fintype.card (Step n m) := by
    dsimp [moleculeCount]
    omega
  rw [hafter,hbefore] at hc
  unfold resetPattern reactionRows
  rw [hi,ho,hc]

theorem afterClauseRows_eq_terminalPatterns {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    afterClauseRows Φ =
      finishPattern n m (Fintype.card (Wire n m)) (Fintype.card (Step n m)) (moleculeCount n m) ++
        resetPattern (Fintype.card (Wire n m)) (Fintype.card (Step n m)) := by
  rw [finishPattern_eq_reactionRows Φ,resetPattern_eq_reactionRows Φ]
  simp only [afterClauseRows,List.ofFn_succ,List.ofFn_zero,List.flatten_cons,List.flatten_nil,List.append_nil]
  apply congrArg₂ List.append
  · apply congrArg (reactionRows Φ)
    apply congrArg Sum.inr
    apply Fin.ext
    simp [stepCode,stepOffset,stepEquiv,finSumFinEquiv,unitCode]
    ring
  · apply congrArg (reactionRows Φ)
    apply congrArg Sum.inr
    apply Fin.ext
    simp [step_card]
    ring

end IrrRAFEnumeration.SATSource

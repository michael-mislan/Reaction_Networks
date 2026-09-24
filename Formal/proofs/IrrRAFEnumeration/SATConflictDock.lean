import proofs.IrrRAFEnumeration.SATConflictPhase
import proofs.IrrRAFEnumeration.SATRunConstruction
import proofs.IrrRAFEnumeration.SATStreamInit

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource Complexity Complexity.TM

theorem conflictPrefix_eq_ofFn (W Q M fuel : Nat) :
    conflictPrefix W Q M fuel = (List.ofFn (fun i : Fin fuel =>
      conflictPattern W (2*i.val+1) (M-(2*i.val+1)-2) i.val (Q-i.val)
        (W+i.val+2) (Q-i.val-1))).flatten := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [conflictPrefix,List.ofFn_succ_last,List.flatten_append]
      simpa only [Fin.val_castSucc,Fin.val_last,List.flatten_cons,List.flatten_nil,
        List.append_nil] using congrArg (fun xs => xs ++ conflictPattern W (2*fuel+1)
          (M-(2*fuel+1)-2) fuel (Q-fuel) (W+fuel+2) (Q-fuel-1)) ih

theorem conflictPattern_eq_reactionRows {n m : Nat} (Φ : Fin m → Finset (Choice n)) (i : Fin n) :
    conflictPattern (Fintype.card (Wire n m)) (2*i.val+1)
      (moleculeCount n m-(2*i.val+1)-2) i.val (Fintype.card (Step n m)-i.val)
      (Fintype.card (Wire n m)+i.val+2) (Fintype.card (Step n m)-i.val-1) =
      reactionRows Φ (auxiliaryReaction (.conflict i)) := by
  have hcode : (stepCode n m (.conflict i)).val = i.val := by
    simp [stepCode,stepOffset,stepEquiv,finSumFinEquiv]
  have hnext : i.val+1 < Fintype.card (Step n m)+1 := by
    have hi := i.isLt
    rw [step_card]
    omega
  have hcat : (catalystIndex (auxiliaryReaction (m := m) (.conflict i))).val = i.val+1 := by
    simp only [auxiliaryReaction,catalystIndex,nextAux,Fin.val_castSucc,hcode,
      Nat.mod_eq_of_lt hnext]
  have hi := auxiliaryInputRow_correct Φ (.conflict i)
  change spanRow (2*i.val+1) 2 (moleculeCount n m-(2*i.val+1)-2) = _ at hi
  have ho := auxiliaryOutputRow_correct Φ (.conflict i)
  simp only [auxiliaryOutputRow,signalOutput,wirePosition,hcode] at ho
  rw [← wire_card n m] at ho
  have hgap : 1+Fintype.card (Wire n m)+i.val-Fintype.card (Wire n m)-1 = i.val := by omega
  have htail : moleculeCount n m-(1+Fintype.card (Wire n m)+i.val)-1 =
      Fintype.card (Step n m)-i.val := by dsimp [moleculeCount]; omega
  rw [hgap,htail] at ho
  have hc := catalyst_row (m := m) (auxiliaryReaction (m := m) (.conflict i))
  rw [hcat] at hc
  have hbefore : 1+Fintype.card (Wire n m)+(i.val+1) = Fintype.card (Wire n m)+i.val+2 := by omega
  have hafter : moleculeCount n m-(1+Fintype.card (Wire n m)+(i.val+1))-1 =
      Fintype.card (Step n m)-i.val-1 := by dsimp [moleculeCount]; omega
  rw [hafter,hbefore] at hc
  unfold conflictPattern reactionRows
  rw [hi,ho,hc]

/-- The complete conflict phase emits exactly the original auxiliary CRS rows.
Its entry register setup is a separate charged phase. -/
theorem conflictPhaseTM_source_correct {n m : Nat} (Φ : Fin m → Finset (Choice n)) (ys : List Bool) :
    conflictPhaseTM.HoareTime
      (EmitPred (parkedInput (cnfBits Φ))
        (conflictWork n m (Fintype.card (Wire n m)) (Fintype.card (Step n m))
          (moleculeCount n m) (reactionCount n m) 0 (cnfStreamCursor Φ 0)) ys)
      (EmitPred (parkedInput (cnfBits Φ))
        (conflictWork n m (Fintype.card (Wire n m)) (Fintype.card (Step n m))
          (moleculeCount n m) (reactionCount n m) n (cnfStreamCursor Φ 0))
        (ys ++ (List.ofFn (fun i : Fin n => reactionRows Φ (auxiliaryReaction (.conflict i)))).flatten))
      (n*(100*(moleculeCount n m+1)+3)+2) := by
  have h := conflictPhaseTM_correct n m (Fintype.card (Wire n m)) (Fintype.card (Step n m))
    (moleculeCount n m) (reactionCount n m) (cnfStreamCursor Φ 0) (parkedInput (cnfBits Φ)) ys
    (cnfStreamCursor_parked Φ 0) (parkedInput_parked _)
    (by rw [step_card]; omega) (by dsimp [moleculeCount]; omega)
    (by simp [moleculeCount,wire_card,step_card]; omega)
  have he : conflictPrefix (Fintype.card (Wire n m)) (Fintype.card (Step n m))
      (moleculeCount n m) n =
      (List.ofFn (fun i : Fin n => reactionRows Φ (auxiliaryReaction (.conflict i)))).flatten := by
    rw [conflictPrefix_eq_ofFn]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext i
    exact conflictPattern_eq_reactionRows Φ i
  rw [he] at h
  exact h

end IrrRAFEnumeration.SATSource

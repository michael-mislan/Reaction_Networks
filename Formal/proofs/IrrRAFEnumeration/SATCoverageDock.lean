import proofs.IrrRAFEnumeration.SATCoveragePhase
import proofs.IrrRAFEnumeration.SATRunConstruction
import proofs.IrrRAFEnumeration.SATStreamInit

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource Complexity Complexity.TM

theorem coveragePattern_eq_reactionRows {n m : Nat} (Φ : Fin m → Finset (Choice n)) (x : Choice n) :
    coveragePattern ((choiceOffset n x).val+1) (moleculeCount n m-((choiceOffset n x).val+1)-1)
      (2*n+x.1.val+1) (2*n+m+x.1.val+(if x.2 then 1 else 0))
      (Fintype.card (Step n m)-n-(choiceOffset n x).val)
      (Fintype.card (Wire n m)+n+(choiceOffset n x).val+2) =
      reactionRows Φ (auxiliaryReaction (.coverage x)) := by
  have hx : (choiceOffset n x).val = 2*x.1.val+(if x.2 then 1 else 0) := inputCode_value x
  have hcode : (stepCode n m (.coverage x)).val = n+(choiceOffset n x).val := by
    simp [stepCode,stepOffset,stepEquiv,finSumFinEquiv]
  have hnext : n+(choiceOffset n x).val+1 < Fintype.card (Step n m)+1 := by
    have hi := (choiceOffset n x).isLt
    rw [step_card]
    omega
  have hcat : (catalystIndex (auxiliaryReaction (m := m) (.coverage x))).val = n+(choiceOffset n x).val+1 := by
    simp only [auxiliaryReaction,catalystIndex,nextAux,Fin.val_castSucc,hcode,Nat.mod_eq_of_lt hnext]
  have hi := auxiliaryInputRow_correct Φ (.coverage x)
  change spanRow ((choiceOffset n x).val+1) 1 (moleculeCount n m-((choiceOffset n x).val+1)-1) = _ at hi
  have ho := auxiliaryOutputRow_correct Φ (.coverage x)
  simp only [auxiliaryOutputRow,signalOutput,wirePosition,hcode] at ho
  have hgap : 1+Fintype.card (Wire n m)+(n+(choiceOffset n x).val)-(2*n+x.1.val+1)-1 =
      2*n+m+x.1.val+(if x.2 then 1 else 0) := by rw [wire_card]; omega
  have htail : moleculeCount n m-(1+Fintype.card (Wire n m)+(n+(choiceOffset n x).val))-1 =
      Fintype.card (Step n m)-n-(choiceOffset n x).val := by dsimp [moleculeCount]; omega
  rw [hgap,htail] at ho
  have hc := catalyst_row (m := m) (auxiliaryReaction (m := m) (.coverage x))
  rw [hcat] at hc
  have hbefore : 1+Fintype.card (Wire n m)+(n+(choiceOffset n x).val+1) =
      Fintype.card (Wire n m)+n+(choiceOffset n x).val+2 := by omega
  have hafter : moleculeCount n m-(1+Fintype.card (Wire n m)+(n+(choiceOffset n x).val+1))-1 =
      Fintype.card (Step n m)-n-(choiceOffset n x).val-1 := by dsimp [moleculeCount]; omega
  rw [hafter,hbefore] at hc
  unfold coveragePattern reactionRows
  rw [hi,ho,hc]

theorem coveragePairPattern_eq_rows {n m : Nat} (Φ : Fin m → Finset (Choice n)) (i : Fin n) :
    coveragePairPattern (2*i.val+1) (moleculeCount n m-(2*i.val+1)-1) (2*n+i.val+1)
      (2*n+m+i.val) (Fintype.card (Step n m)-n-2*i.val) (Fintype.card (Wire n m)+n+2*i.val+2) =
      reactionRows Φ (auxiliaryReaction (.coverage (i,false))) ++
        reactionRows Φ (auxiliaryReaction (.coverage (i,true))) := by
  have hf := coveragePattern_eq_reactionRows Φ (i,false)
  have ht := coveragePattern_eq_reactionRows Φ (i,true)
  have hx0 : (choiceOffset n (i,false)).val = 2*i.val := by
    simp [choiceOffset,bitCode,finProdFinEquiv,Nat.mul_comm]
  have hx1 : (choiceOffset n (i,true)).val = 2*i.val+1 := by
    simp [choiceOffset,bitCode,finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  rw [hx0] at hf
  rw [hx1] at ht
  simp only [Bool.false_eq_true,↓reduceIte,Nat.add_zero] at hf ht
  have hs : moleculeCount n m-(2*i.val+1)-1-1 = moleculeCount n m-(2*i.val+1+1)-1 := by omega
  have hl : Fintype.card (Step n m)-n-2*i.val-1 = Fintype.card (Step n m)-n-(2*i.val+1) := by omega
  have hc : Fintype.card (Wire n m)+n+2*i.val+2+1 = Fintype.card (Wire n m)+n+(2*i.val+1)+2 := by omega
  unfold coveragePairPattern
  rw [hf,hs,hl,hc,ht]

def coverageSourceRows {n m : Nat} (Φ : Fin m → Finset (Choice n)) : List Bool :=
  (List.ofFn (fun i : Fin n => reactionRows Φ (auxiliaryReaction (.coverage (i,false))) ++
    reactionRows Φ (auxiliaryReaction (.coverage (i,true))))).flatten

theorem coveragePrefix_eq_ofFn (n m W Q M fuel : Nat) :
    coveragePrefix n m W Q M fuel = (List.ofFn (fun i : Fin fuel =>
      coveragePairPattern (2*i.val+1) (M-(2*i.val+1)-1) (2*n+i.val+1)
        (2*n+m+i.val) (Q-n-2*i.val) (W+n+2*i.val+2))).flatten := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [coveragePrefix,List.ofFn_succ_last,List.flatten_append]
      simpa only [Fin.val_castSucc,Fin.val_last,List.flatten_cons,List.flatten_nil,List.append_nil]
        using congrArg (fun xs => xs ++ coveragePairPattern (2*fuel+1) (M-(2*fuel+1)-1)
          (2*n+fuel+1) (2*n+m+fuel) (Q-n-2*fuel) (W+n+2*fuel+2)) ih

theorem coveragePhaseTM_source_correct {n m : Nat} (Φ : Fin m → Finset (Choice n)) (ys : List Bool) :
    coveragePhaseTM.HoareTime
      (EmitPred (parkedInput (cnfBits Φ)) (coverageWork n m (Fintype.card (Wire n m))
        (Fintype.card (Step n m)) (moleculeCount n m) (reactionCount n m) 0 (cnfStreamCursor Φ 0)) ys)
      (EmitPred (parkedInput (cnfBits Φ)) (coverageWork n m (Fintype.card (Wire n m))
        (Fintype.card (Step n m)) (moleculeCount n m) (reactionCount n m) n (cnfStreamCursor Φ 0))
        (ys ++ coverageSourceRows Φ)) (n*(400*(moleculeCount n m+1)+3)+2) := by
  have h := coveragePhaseTM_correct n m (Fintype.card (Wire n m)) (Fintype.card (Step n m))
    (moleculeCount n m) (reactionCount n m) (cnfStreamCursor Φ 0) (parkedInput (cnfBits Φ)) ys
    (cnfStreamCursor_parked Φ 0) (parkedInput_parked _) (wire_card n m)
    (by rw [step_card]; omega) (by dsimp [moleculeCount]; omega)
  have he : coveragePrefix n m (Fintype.card (Wire n m)) (Fintype.card (Step n m)) (moleculeCount n m) n =
      coverageSourceRows Φ := by
    rw [coveragePrefix_eq_ofFn]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext i
    exact coveragePairPattern_eq_rows Φ i
  rw [he] at h
  exact h

end IrrRAFEnumeration.SATSource

import proofs.IrrRAFEnumeration.SATConflictSetup
import proofs.IrrRAFEnumeration.SATConflictDock

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource Complexity Complexity.TM

def preparedConflictTM : TM 13 := seqTM conflictSetupTM conflictPhaseTM

theorem preparedConflictTM_correct {n m : Nat} (Φ : Fin m → Finset (Choice n)) (ys : List Bool) :
    preparedConflictTM.HoareTime (EmitPred (parkedInput (cnfBits Φ)) (savedPrefixWork Φ) ys)
      (EmitPred (parkedInput (cnfBits Φ))
        (conflictWork n m (Fintype.card (Wire n m)) (Fintype.card (Step n m))
          (moleculeCount n m) (reactionCount n m) n (cnfStreamCursor Φ 0))
        (ys ++ (List.ofFn (fun i : Fin n => reactionRows Φ (auxiliaryReaction (.conflict i)))).flatten))
      (4096*(n+m+Fintype.card (Wire n m)+Fintype.card (Step n m)+
        moleculeCount n m+reactionCount n m+1)^2+1+
        (n*(100*(moleculeCount n m+1)+3)+2)) := by
  have hw : ∀ i, Parked (conflictWork n m (Fintype.card (Wire n m)) (Fintype.card (Step n m))
      (moleculeCount n m) (reactionCount n m) 0 (cnfStreamCursor Φ 0) i) := by
    intro i
    fin_cases i <;> first | exact parked_regTape _ | exact cnfStreamCursor_parked Φ 0
  exact seqTM_hoareTime _ _ (conflictSetupTM_correct Φ ys)
    (emitPred_transition (parkedInput_parked _) hw ys) (conflictPhaseTM_source_correct Φ ys)

def initializedConflictTM : TM 13 := seqTM initializedSavedPrefixTM preparedConflictTM

/-- Actual initialized source compilation through the complete conflict block.
Coverage, clause, finish and reset blocks remain to be appended. -/
theorem initializedConflictTM_correct {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    initializedConflictTM.HoareTime
      (fun inp work out => inp = Tape.init ((cnfBits Φ).map Γ.ofBool) ∧
        (∀ i, work i = Tape.init []) ∧ out = Tape.init [])
      (EmitPred (parkedInput (cnfBits Φ))
        (conflictWork n m (Fintype.card (Wire n m)) (Fintype.card (Step n m))
          (moleculeCount n m) (reactionCount n m) n (cnfStreamCursor Φ 0))
        (sourcePrefixBits Φ ++
          (List.ofFn (fun i : Fin n => reactionRows Φ (auxiliaryReaction (.conflict i)))).flatten))
      (10000000*((cnfBits Φ).length+1)^4) := by
  have hw : ∀ i, Parked (savedPrefixWork Φ i) := by
    intro i
    fin_cases i <;> first | exact parked_regTape _ | exact cnfStreamCursor_parked Φ 0
  have h := seqTM_hoareTime _ _ (initializedSavedPrefixTM_correct Φ)
    (emitPred_transition (parkedInput_parked _) hw (sourcePrefixBits Φ))
    (preparedConflictTM_correct Φ (sourcePrefixBits Φ))
  apply h.mono_bound
  let L := (cnfBits Φ).length+1
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hn : n ≤ L := by dsimp [L]; rw [cnfBits_length]; omega
  have hm : m ≤ L := by dsimp [L]; rw [cnfBits_length]; omega
  have hnm : n*m ≤ L^2 := by simpa [pow_two] using Nat.mul_le_mul hn hm
  have hL2 : L ≤ L^2 := by nlinarith
  have hsum : n+m+Fintype.card (Wire n m)+Fintype.card (Step n m)+
      moleculeCount n m+reactionCount n m+1 ≤ 40*L^2 := by
    simp [wire_card,step_card,moleculeCount,reactionCount,Choice]
    nlinarith
  have hsquare := Nat.pow_le_pow_left hsum 2
  have hM : moleculeCount n m ≤ 20*L^2 := by
    simp [moleculeCount,wire_card,step_card]
    nlinarith
  have hrow : 100*(moleculeCount n m+1)+3 ≤ 2103*L^2 := by nlinarith
  have hloop := Nat.mul_le_mul hn hrow
  have h34 : L^3 ≤ L^4 := Nat.pow_le_pow_right hL (by decide)
  change 1000000*L^4+1+(4096*(n+m+Fintype.card (Wire n m)+Fintype.card (Step n m)+
    moleculeCount n m+reactionCount n m+1)^2+1+(n*(100*(moleculeCount n m+1)+3)+2)) ≤
      10000000*L^4
  nlinarith

end IrrRAFEnumeration.SATSource

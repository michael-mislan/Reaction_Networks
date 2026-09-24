import proofs.IrrRAFEnumeration.CompletionBlockerAppend

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

def resetBlockerCountersTM : TM 7 := seqTM (setConstTM 1 1) (clearRegTM 2)

theorem resetBlockerCountersTM_correct {r : Nat} (U : Finset (Fin r)) (base blocks : List Bool)
    (inp : Tape) (hp : Parked inp) :
    resetBlockerCountersTM.HoareTime (EmitPred inp (dynamicWork U (1+r) r base blocks) [])
      (EmitPred inp (dynamicWork U 1 0 base blocks) []) (4*r+20) := by
  have hs := setConstTM_hoareTime (1 : Fin 7) 1 (1+r) inp (dynamicWork U (1+r) r base blocks) [] hp
    (dynamicWork_parked _ _ _ _ _) rfl
  have he : Function.update (dynamicWork U (1+r) r base blocks) (1 : Fin 7) (regTape 1) =
      dynamicWork U 1 r base blocks := by
    funext i
    fin_cases i <;> simp [dynamicWork,frameWork,maskWork]
  rw [he] at hs
  have hc := clearRegTM_hoareTime (2 : Fin 7) r inp (dynamicWork U 1 r base blocks) [] hp
    (fun i _ => dynamicWork_parked _ _ _ _ _ i) rfl
  have he' : Function.update (dynamicWork U 1 r base blocks) (2 : Fin 7) (regTape 0) =
      dynamicWork U 1 0 base blocks := by
    funext i
    fin_cases i <;> simp [dynamicWork,frameWork,maskWork]
  rw [he'] at hc
  have h := seqTM_hoareTime _ _ hs (emitPred_transition hp (dynamicWork_parked _ _ _ _ _) []) hc
  convert h using 1
  omega

def commitBlockerTM : TM 7 := seqTM appendBlockerTM resetBlockerCountersTM

def blockerCommitTime (r oldLength clauseLength : Nat) :=
  oldLength+1+1+(r*(10*r+58)+r+6)+1+(oldLength+clauseLength)+3+1+(4*r+20)

/-- Appending one upward-cone blocker returns to the exact reusable query prefix. -/
theorem commitBlockerTM_correct {r : Nat} (U : Finset (Fin r)) (base blocks : List Bool)
    (inp : Tape) (hp : Parked inp) :
    commitBlockerTM.HoareTime (EmitPred inp (dynamicWork U 1 0 base blocks) [])
      (EmitPred inp (dynamicWork U 1 0 base (blocks++SAT.CNF.encode [blockerClause U])) [])
      (blockerCommitTime r blocks.length (SAT.CNF.encode [blockerClause U]).length) := by
  have h := seqTM_hoareTime _ _ (appendBlockerTM_correct U base blocks inp hp)
    (emitPred_transition hp (dynamicWork_parked _ _ _ _ _) [])
    (resetBlockerCountersTM_correct U base _ inp hp)
  simpa only [commitBlockerTM,blockerCommitTime,List.length_append] using h

theorem commitKnownBlocker_correct {r : Nat} (G : List (Finset (Fin r))) (U : Finset (Fin r))
    (base : List Bool) (inp : Tape) (hp : Parked inp) :
    commitBlockerTM.HoareTime
      (EmitPred inp (dynamicWork U 1 0 base (SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G))) [])
      (EmitPred inp (dynamicWork U 1 0 base (SAT.CNF.encode (PositiveCompletionCNF.outputBlockers (G++[U])))) [])
      (blockerCommitTime r (SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)).length
        (SAT.CNF.encode [blockerClause U]).length) := by
  have h := commitBlockerTM_correct U base (SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)) inp hp
  simpa only [PositiveCompletionCNF.outputBlockers_append,SAT.CNF.encode_append,blockerClause] using h

end IrrRAFEnumeration.CompletionQuery

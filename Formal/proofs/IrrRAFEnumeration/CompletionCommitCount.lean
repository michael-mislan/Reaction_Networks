import proofs.IrrRAFEnumeration.CompletionStoredCommit

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

def enumWork {r : Nat} (k : Nat) (U : Finset (Fin r))
    (base blocks records : List Bool) (j count : Nat) :=
  frameWork (m := 1)
    (frameWork (m := 1) (minimizeWork k U base blocks j) (fun _ => accumulatorTape records))
    (fun _ => regTape count)

def enumCount (k : Nat) : Fin ((((bufferedCount k+1)+1)+1)+1) :=
  Fin.last (((bufferedCount k+1)+1)+1)

def commitOutputTM (k : Nat) : TM ((((bufferedCount k+1)+1)+1)+1) :=
  seqTM ((recordAndBlockTM k).liftTM 1) (incRegTM (enumCount k))

theorem enumWork_parked {r : Nat} (k : Nat) (U : Finset (Fin r))
    (base blocks records : List Bool) (j count : Nat) :
    ∀ i, Parked (enumWork k U base blocks records j count i) := by
  intro i
  unfold enumWork frameWork
  split
  · split
    · exact minimizeWork_parked _ _ _ _ _ _
    · exact (accumulatorTape_outAcc _).parked
  · exact parked_regTape _

/-- The concrete commit updates mask records, blockers, and count together. -/
theorem commitOutputTM_correct {r : Nat} (k : Nat) (U : Finset (Fin r))
    (base blocks records : List Bool) (j count : Nat) (inp : Tape) (hp : Parked inp) :
    (commitOutputTM k).HoareTime (EmitPred inp (enumWork k U base blocks records j count) [])
      (EmitPred inp (enumWork k U base (blocks++SAT.CNF.encode [blockerClause U])
        (records++containerMask U) j (count+1)) [])
      (2*r+6+blockerCommitTime r blocks.length (SAT.CNF.encode [blockerClause U]).length+1+2*count+4) := by
  have h1 := liftTM_frame_correct (recordAndBlockTM k) 1 (fun _ => regTape count)
    (fun _ _ => parked_regTape _) inp inp _ _ [] [] _
    (recordAndBlockTM_correct k U base blocks records j inp hp)
  let W := enumWork k U base (blocks++SAT.CNF.encode [blockerClause U]) (records++containerMask U) j count
  have hi := incRegTM_hoareTime (enumCount k) count inp W [] hp
    (fun i _ => enumWork_parked _ _ _ _ _ _ _ i) (by simp [W,enumWork,enumCount,frameWork])
  simp only [W,enumWork,enumCount,frameWork_update_last] at hi
  have h := seqTM_hoareTime _ _ h1 (emitPred_transition hp (enumWork_parked _ _ _ _ _ _ _) []) hi
  convert h using 1

def storedMasks {r : Nat} (G : List (Finset (Fin r))) : List Bool := G.flatMap containerMask

/-- Both buffers and the unary count now represent the very same extended list. -/
theorem commitKnownOutput_correct {r : Nat} (k : Nat) (G : List (Finset (Fin r)))
    (U : Finset (Fin r)) (base : List Bool) (j : Nat) (inp : Tape) (hp : Parked inp) :
    (commitOutputTM k).HoareTime
      (EmitPred inp (enumWork k U base (SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G))
        (storedMasks G) j G.length) [])
      (EmitPred inp (enumWork k U base (SAT.CNF.encode (PositiveCompletionCNF.outputBlockers (G++[U])))
        (storedMasks (G++[U])) j (G++[U]).length) [])
      (2*r+6+blockerCommitTime r (SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)).length
        (SAT.CNF.encode [blockerClause U]).length+1+2*G.length+4) := by
  have h := commitOutputTM_correct k U base (SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G))
    (storedMasks G) j G.length inp hp
  simpa only [PositiveCompletionCNF.outputBlockers_append,SAT.CNF.encode_append,
    blockerClause,storedMasks,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,List.length_append,List.length_cons,List.length_nil,Nat.add_zero] using h

end IrrRAFEnumeration.CompletionQuery

import proofs.IrrRAFEnumeration.CompletionBlockerCommit

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

def commitMinBlockerTM (k : Nat) : TM ((bufferedCount k+1)+1) :=
  ((((commitBlockerTM.liftTM (3+k)).liftTM 1).liftTM 1).liftTM 1).liftTM 1

theorem commitMinBlockerTM_correct {r : Nat} (k : Nat) (U : Finset (Fin r))
    (base blocks : List Bool) (j : Nat) (inp : Tape) (hp : Parked inp) :
    (commitMinBlockerTM k).HoareTime (EmitPred inp (minimizeWork k U base blocks j) [])
      (EmitPred inp (minimizeWork k U base (blocks++SAT.CNF.encode [blockerClause U]) j) [])
      (blockerCommitTime r blocks.length (SAT.CNF.encode [blockerClause U]).length) := by
  have h := commitBlockerTM_correct U base blocks inp hp
  have h1 := liftTM_frame_correct _ (3+k) (fun _ => regTape 0)
    (fun _ _ => parked_regTape _) inp inp _ _ [] [] _ h
  have h2 := liftTM_frame_correct _ 1 (fun _ => parkedInput [])
    (fun _ _ => parkedInput_parked _) inp inp _ _ [] [] _ h1
  have h3 := liftTM_frame_correct _ 1 (fun _ => accumulatorTape [])
    (fun _ _ => (accumulatorTape_outAcc []).parked) inp inp _ _ [] [] _ h2
  have h4 := liftTM_frame_correct _ 1 (fun _ => regTape j)
    (fun _ _ => parked_regTape _) inp inp _ _ [] [] _ h3
  have h5 := liftTM_frame_correct _ 1 (fun _ => regTape r)
    (fun _ _ => parked_regTape _) inp inp _ _ [] [] _ h4
  simpa only [commitMinBlockerTM,minimizeWork,trialWork_zero,completionWork,
    bufferedWork,queryDecisionWork,queryPrefix] using h5

def recordMaskTM {n : Nat} (src : Fin n) : TM (n+1) := (appendRestoreTM src).retargetOutput

theorem recordMaskTM_correct {n r : Nat} (src : Fin n) (U : Finset (Fin r))
    (inp : Tape) (work : Fin n → Tape) (records : List Bool)
    (hp : Parked inp) (hw : ∀ i, Parked (work i))
    (hm : work src = parkedInput (containerMask U)) :
    (recordMaskTM src).HoareTime
      (EmitPred inp (frameWork (m := 1) work (fun _ => accumulatorTape records)) [])
      (EmitPred inp (frameWork (m := 1) work (fun _ => accumulatorTape (records++containerMask U))) [])
      (2*r+5) := by
  have h := appendRestoreTM_correct src (containerMask U) inp work records hp hw
    (by rw [hm]; rfl) (by rw [hm]; rfl) (by rw [hm]; exact parkedInput_chunk _)
  have hr := redirectEmitter_correct _ inp inp work work _ _ _ h
  simpa only [recordMaskTM,containerMask,List.length_ofFn] using hr

def minMask (k : Nat) : Fin ((bufferedCount k+1)+1) := Fin.castAdd 1 (trialMask k)

theorem minimizeWork_mask {r : Nat} (k : Nat) (U : Finset (Fin r)) (base blocks : List Bool)
    (j : Nat) : minimizeWork k U base blocks j (minMask k) = parkedInput (containerMask U) := by
  simp only [minimizeWork,minMask,frameWork,Fin.val_castAdd,dif_pos (trialMask k).isLt]
  exact trialWork_mask _ _ _ _ _ _

theorem minimizeWork_parked {r : Nat} (k : Nat) (U : Finset (Fin r)) (base blocks : List Bool)
    (j : Nat) : ∀ i, Parked (minimizeWork k U base blocks j i) := by
  intro i
  unfold minimizeWork frameWork
  split
  · exact trialWork_parked _ _ _ _ _ _ _
  · exact parked_regTape _

/-- Record the mask, then commit that same mask's blocker. Both stored views
change together at the postcondition; all minimizer registers are retained. -/
def recordAndBlockTM (k : Nat) : TM (((bufferedCount k+1)+1)+1) :=
  seqTM (recordMaskTM (minMask k)) ((commitMinBlockerTM k).liftTM 1)

theorem recordAndBlockTM_correct {r : Nat} (k : Nat) (U : Finset (Fin r))
    (base blocks records : List Bool) (j : Nat) (inp : Tape) (hp : Parked inp) :
    (recordAndBlockTM k).HoareTime
      (EmitPred inp (frameWork (m := 1) (minimizeWork k U base blocks j)
        (fun _ => accumulatorTape records)) [])
      (EmitPred inp (frameWork (m := 1)
        (minimizeWork k U base (blocks++SAT.CNF.encode [blockerClause U]) j)
        (fun _ => accumulatorTape (records++containerMask U))) [])
      (2*r+6+blockerCommitTime r blocks.length (SAT.CNF.encode [blockerClause U]).length) := by
  have h1 := recordMaskTM_correct (minMask k) U inp (minimizeWork k U base blocks j) records hp
    (minimizeWork_parked _ _ _ _ _) (minimizeWork_mask _ _ _ _ _)
  have h2 := liftTM_frame_correct (commitMinBlockerTM k) 1
    (fun _ => accumulatorTape (records++containerMask U))
    (fun _ _ => (accumulatorTape_outAcc _).parked) inp inp _ _ [] [] _
    (commitMinBlockerTM_correct k U base blocks j inp hp)
  have hw : ∀ i, Parked (frameWork (m := 1) (minimizeWork k U base blocks j)
      (fun _ => accumulatorTape (records++containerMask U)) i) := by
    intro i
    unfold frameWork
    split
    · exact minimizeWork_parked _ _ _ _ _ _
    · exact (accumulatorTape_outAcc _).parked
  exact seqTM_hoareTime _ _ h1 (emitPred_transition hp hw []) h2

end IrrRAFEnumeration.CompletionQuery

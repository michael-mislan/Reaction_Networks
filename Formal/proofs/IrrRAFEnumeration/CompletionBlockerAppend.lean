import proofs.IrrRAFEnumeration.CompletionBufferEnd

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

def blockerClause {r : Nat} (U : Finset (Fin r)) : SAT.Clause :=
  PositiveCompletionCNF.negative
    (PositiveCompletionCNF.members (fun j => j ∈ U) PositiveCompletionCNF.selectVar)

theorem containerMask_blocker {r : Nat} (U : Finset (Fin r)) :
    selectedLiterals false (parkedInput (containerMask U)) 1 0 r = blockerClause U := by
  have h := selectedLiterals_eq_filter false (parkedInput (containerMask U)) 1 0 r
    (fun j => decide (j ∈ U)) (containerMask_cell U)
  simpa [blockerClause,PositiveCompletionCNF.negative,PositiveCompletionCNF.members,
    PositiveCompletionCNF.selectVar,List.map_map] using h

def blockerPrefix {r : Nat} (U : Finset (Fin r)) (pos index : Nat) (base : List Bool) : Fin 6 → Tape :=
  frameWork (m := 1)
    (frameWork (m := 1) (maskWork (regTape r) pos index 0) (fun _ => parkedInput (containerMask U)))
    (fun _ => parkedInput base)

def blockerAccumWork {r : Nat} (U : Finset (Fin r)) (pos index : Nat) (base blocks : List Bool) : Fin 7 → Tape :=
  frameWork (m := 1) (blockerPrefix U pos index base) (fun _ => accumulatorTape blocks)

theorem blockerPrefix_parked {r : Nat} (U : Finset (Fin r)) (pos index : Nat) (base : List Bool) :
    ∀ i, Parked (blockerPrefix U pos index base i) := by
  intro i
  fin_cases i <;> first | exact parked_regTape _ | exact parkedInput_parked _

theorem blockerPrefix_dynamic {r : Nat} (U : Finset (Fin r)) (pos index : Nat) (base blocks : List Bool) :
    frameWork (m := 1) (blockerPrefix U pos index base) (fun _ => parkedInput blocks) =
      dynamicWork U pos index base blocks := by
  funext i
  fin_cases i <;> rfl

def blockerEmitTM : TM 7 := ((retargetInput (selectedClauseTM false)).liftTM 1).retargetOutput

/-- Emit the selected mask's negative disjunction into the persistent blocker
accumulator, retaining the mask and fixed chemistry. -/
theorem blockerEmitTM_correct {r : Nat} (U : Finset (Fin r)) (base blocks : List Bool)
    (inp : Tape) (hp : Parked inp) :
    blockerEmitTM.HoareTime (EmitPred inp (blockerAccumWork U 1 0 base blocks) [])
      (EmitPred inp (blockerAccumWork U (1+r) r base
        (blocks++SAT.CNF.encode [blockerClause U])) []) (r*(10*r+58)+r+6) := by
  let vin := parkedInput (containerMask U)
  have h := selectedClauseTM_correct false vin 1 0 r blocks (parkedInput_parked _) rfl rfl
  rw [containerMask_blocker U] at h
  have hv := virtualEmitter_correct (selectedClauseTM false) inp vin vin
    (maskWork (regTape r) 1 0 0) (maskWork (regTape r) (1+r) (0+r) 0)
    _ _ _ hp ⟨rfl,(parkedInput_parked _).2⟩
    (fun i => ⟨by fin_cases i <;> rfl,(maskWork_parked _ _ _ _ (parked_regTape _) i).2⟩) h
  have hf := liftTM_frame_correct (retargetInput (selectedClauseTM false)) 1
    (fun _ => parkedInput base) (fun _ _ => parkedInput_parked _) inp inp _ _ _ _ _ hv
  have ho := redirectEmitter_correct _ inp inp _ _ _ _ _ hf
  have ht : r*(5*1+5*0+10*r+53)+r+6 = r*(10*r+58)+r+6 := by ring
  rw [ht] at ho
  simpa only [blockerEmitTM,blockerAccumWork,blockerPrefix,Nat.zero_add] using ho

def appendBlockerTM : TM 7 :=
  seqTM (seekBufferEndTM 6) (seqTM blockerEmitTM (rewindWorkTM 6))

theorem appendBlockerTM_correct {r : Nat} (U : Finset (Fin r)) (base blocks : List Bool)
    (inp : Tape) (hp : Parked inp) :
    appendBlockerTM.HoareTime (EmitPred inp (dynamicWork U 1 0 base blocks) [])
      (EmitPred inp (dynamicWork U (1+r) r base (blocks++SAT.CNF.encode [blockerClause U])) [])
      (blocks.length+1+1+(r*(10*r+58)+r+6)+1+
        (blocks++SAT.CNF.encode [blockerClause U]).length+3) := by
  have hs := seekBufferEndTM_correct (6 : Fin 7) blocks inp (dynamicWork U 1 0 base blocks) [] hp
    (dynamicWork_parked _ _ _ _ _) (parkedInput_chunk blocks)
  have he : Function.update (dynamicWork U 1 0 base blocks) (6 : Fin 7)
      (advanceInput ((dynamicWork U 1 0 base blocks) 6) blocks.length) =
        blockerAccumWork U 1 0 base blocks := by
    funext i
    fin_cases i <;> simp [dynamicWork,blockerAccumWork,blockerPrefix,frameWork,accumulatorTape]
  rw [he] at hs
  have hm := blockerEmitTM_correct U base blocks inp hp
  have hr := rewindQuery_correct (blockerPrefix U (1+r) r base) inp
    (blocks++SAT.CNF.encode [blockerClause U]) hp (blockerPrefix_parked _ _ _ _)
  rw [blockerPrefix_dynamic] at hr
  have hpark : ∀ pos index bs i, Parked (blockerAccumWork U pos index base bs i) := by
    intro pos index bs i
    unfold blockerAccumWork frameWork
    split
    · exact blockerPrefix_parked _ _ _ _ _
    · exact (accumulatorTape_outAcc _).parked
  have hmr := seqTM_hoareTime _ _ hm (emitPred_transition hp (hpark _ _ _) []) hr
  have h := seqTM_hoareTime _ _ hs (emitPred_transition hp (hpark _ _ _) []) hmr
  convert h using 1
  omega

end IrrRAFEnumeration.CompletionQuery

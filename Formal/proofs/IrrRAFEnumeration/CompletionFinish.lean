import proofs.IrrRAFEnumeration.CompletionMinimizeCommit

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

def enumRecords (k : Nat) : Fin ((((bufferedCount k+1)+1)+1)+1) :=
  Fin.castAdd 1 (Fin.last ((bufferedCount k+1)+1))

def finishWork {r : Nat} (k : Nat) (U : Finset (Fin r))
    (base blocks records : List Bool) (j count : Nat) :=
  frameWork (m := 1)
    (frameWork (m := 1) (minimizeWork k U base blocks j) (fun _ => parkedInput records))
    (fun _ => regTape count)

theorem finishWork_parked {r : Nat} (k : Nat) (U : Finset (Fin r))
    (base blocks records : List Bool) (j count : Nat) :
    ∀ i, Parked (finishWork k U base blocks records j count i) := by
  intro i
  unfold finishWork frameWork
  split
  · split
    · exact minimizeWork_parked _ _ _ _ _ _
    · exact parkedInput_parked _
  · exact parked_regTape _

def finishTM (k : Nat) : TM ((((bufferedCount k+1)+1)+1)+1) :=
  seqTM ((rewindWorkTM (Fin.last ((bufferedCount k+1)+1))).liftTM 1)
    (seqTM (emitRunTM true (enumCount k))
      (seqTM (emitBitsTM [false]) (appendRestoreTM (enumRecords k))))

/-- Write the actual unary-count/fixed-width-mask output, including an empty
family's single false delimiter. No final output size is supplied to the machine. -/
theorem finishTM_correct {r : Nat} (k : Nat) (U : Finset (Fin r))
    (base blocks : List Bool) (G : List (Finset (Fin r))) (j : Nat)
    (inp : Tape) (hp : Parked inp) :
    (finishTM k).HoareTime
      (EmitPred inp (enumWork k U base blocks (storedMasks G) j G.length) [])
      (EmitPred inp (finishWork k U base blocks (storedMasks G) j G.length)
        (outputBits (Equiv.refl (Fin r)) G))
      (3*(storedMasks G).length+4*G.length+14) := by
  let W := finishWork k U base blocks (storedMasks G) j G.length
  have hw := finishWork_parked k U base blocks (storedMasks G) j G.length
  have hr := rewindQuery_correct (minimizeWork k U base blocks j) inp (storedMasks G) hp
    (minimizeWork_parked _ _ _ _ _)
  have hr' := liftTM_frame_correct _ 1 (fun _ => regTape G.length)
    (fun _ _ => parked_regTape _) inp inp _ _ [] [] _ hr
  have hh := emitRunTM_correct true (enumCount k) G.length inp W [] hp hw
    (by simp [W,finishWork,enumCount,frameWork])
  simp only [List.nil_append] at hh
  have hd := emitBitsTM_hoareTime [false] inp W (List.replicate G.length true) hp hw
  have hm : W (enumRecords k) = parkedInput (storedMasks G) := by
    simp [W,finishWork,enumRecords,frameWork]
  have ha := appendRestoreTM_correct (enumRecords k) (storedMasks G) inp W
    (List.replicate G.length true++[false]) hp hw
    (by rw [hm]; rfl) (by rw [hm]; rfl) (by rw [hm]; exact parkedInput_chunk _)
  have hda := seqTM_hoareTime _ _ hd (emitPred_transition hp hw _) ha
  have hhda := seqTM_hoareTime _ _ hh (emitPred_transition hp hw _) hda
  have h := seqTM_hoareTime _ _ hr' (emitPred_transition hp hw []) hhda
  have he : (List.replicate G.length true++[false])++storedMasks G =
      outputBits (Equiv.refl (Fin r)) G := by
    simp [outputBits,outputBody,storedMasks,List.append_assoc]
    rfl
  rw [he] at h
  convert h using 1
  simp only [List.length_singleton]
  omega

end IrrRAFEnumeration.CompletionQuery

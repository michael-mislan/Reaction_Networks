import proofs.IrrRAFEnumeration.SATStreamPosition
import proofs.IrrRAFEnumeration.SATStreamRows

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource Complexity Complexity.TM

theorem cnfStreamCursor_parked {n m : Nat} (Φ : Fin m → Finset (Choice n)) (pos : Nat) :
    Parked (cnfStreamCursor Φ pos) :=
  advanceInput_parked _ _ (parkedInput_parked _)

theorem cnfStreamCursor_next {n m : Nat} (Φ : Fin m → Finset (Choice n)) (pos : Nat) :
    (cnfStreamCursor Φ pos).move .right = cnfStreamCursor Φ (pos+1) := by
  simpa only [cnfStreamCursor,Nat.add_assoc] using
    advanceInput_move (parkedInput (cnfBits Φ)) (n+m+2+pos)

theorem cnfStreamCursor_read {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (j : Fin m) (x : Choice n) :
    (cnfStreamCursor Φ (finProdFinEquiv (j,choiceOffset n x)).val).read =
      Γ.ofBool (decide (x ∈ Φ j)) := by
  have h := clausePosition_cell Φ j x
  simpa only [cnfStreamCursor,advanceInput,parkedInput,Tape.read,clausePosition,
    cnfHeader_length,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

def streamInitTM (pre post : Nat) : TM (pre+1+post) :=
  seqTM (copyRestoreTM pre post)
    (skipCNFHeadersTM (placeWorkIdx pre post (0 : Fin 1)))

/-- A charged stream initialization from the actual encoded CNF, preserving
all occupied surrounding tapes and the original input position. -/
theorem streamInit_correct {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (pre post : Nat) (work : Fin (pre+1+post) → Tape) (ys : List Bool)
    (hw : ∀ i, Parked (work i))
    (hd : work (placeWorkIdx pre post (0 : Fin 1)) = (Tape.init []).move .right) :
    (streamInitTM pre post).HoareTime (EmitPred (parkedInput (cnfBits Φ)) work ys)
      (EmitPred (parkedInput (cnfBits Φ))
        (Function.update work (placeWorkIdx pre post (0 : Fin 1)) (cnfStreamCursor Φ 0)) ys)
      (4*(cnfBits Φ).length+13) := by
  let q := placeWorkIdx pre post (0 : Fin 1)
  let W := Function.update work q (parkedInput (cnfBits Φ))
  have hwp : ∀ i, Parked (W i) := updateTape_parked work q _ hw (parkedInput_parked _)
  have hc := copyRestore_correct pre post (cnfBits Φ) ys work hw hd
  have hs := skipCNFHeaders_correct Φ q (parkedInput (cnfBits Φ)) W ys
    (parkedInput_parked _) hwp (by simp [W])
  have h := seqTM_hoareTime _ _ hc (emitPred_transition (parkedInput_parked _) hwp ys) hs
  have he : Function.update W q (cnfStreamCursor Φ 0) = Function.update work q (cnfStreamCursor Φ 0) := by
    simp [W]
  rw [he] at h
  apply h.mono_bound
  have hlen := cnfBits_length Φ
  omega

/-- The already verified row emitter consumes the initialized whole-CNF
cursor directly; no second copy of just the body is required. -/
theorem streamClauseOutputFromCNF_correct {n m k : Nat} (Φ : Fin m → Finset (Choice n))
    (j : Fin m) (x : Choice n) (ra cursor rb rc : Fin k)
    (hbne : rb ≠ cursor) (hcne : rc ≠ cursor)
    (inp : Tape) (work : Fin k → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ i, Parked (work i))
    (ha : work ra = regTape (wirePosition (Wire.clause (n := n) j)))
    (hb : work rb = regTape
      (1+Fintype.card (Wire n m)+(stepCode n m (.clause j x)).val-wirePosition (Wire.clause (n := n) j)-1))
    (hc : work rc = regTape
      (moleculeCount n m-(1+Fintype.card (Wire n m)+(stepCode n m (.clause j x)).val)-1))
    (hcursor : work cursor = cnfStreamCursor Φ (finProdFinEquiv (j,choiceOffset n x)).val) :
    (streamMarkedRowTM ra cursor rb rc).HoareTime (EmitPred inp work ys)
      (EmitPred inp (Function.update work cursor
        (cnfStreamCursor Φ ((finProdFinEquiv (j,choiceOffset n x)).val+1)))
        (ys ++ auxiliaryOutputRow Φ (.clause j x)))
      (4*(wirePosition (Wire.clause (n := n) j)+
        (1+Fintype.card (Wire n m)+(stepCode n m (.clause j x)).val-wirePosition (Wire.clause (n := n) j)-1)+
        (moleculeCount n m-(1+Fintype.card (Wire n m)+(stepCode n m (.clause j x)).val)-1))+12) := by
  have hread : (work cursor).read = Γ.ofBool (decide (x ∈ Φ j)) := by
    rw [hcursor]
    exact cnfStreamCursor_read Φ j x
  have h := streamMarkedRowTM_correct ra cursor rb rc hbne hcne _ _ _ (decide (x ∈ Φ j))
    inp work ys hp hw ha hb hc hread
  rw [hcursor,cnfStreamCursor_next] at h
  simpa only [auxiliaryOutputRow,signalOutput] using h

end IrrRAFEnumeration.SATSource

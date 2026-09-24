import proofs.IrrRAFEnumeration.SATStreamCursor
import proofs.IrrRAFEnumeration.SATRowMachines

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource Complexity Complexity.TM

def streamMarkedRowTM {k : Nat} (before cursor between after : Fin k) : TM k :=
  seqTM (emitRunTM false before)
    (seqTM (emitCursorBitTM cursor)
      (seqTM (emitRunTM false between)
        (seqTM (emitBitsTM [true]) (emitRunTM false after))))

theorem streamMarkedRowTM_correct {k : Nat} (ra cursor rb rc : Fin k)
    (hbne : rb ≠ cursor) (hcne : rc ≠ cursor) (a b c : Nat) (bit : Bool)
    (inp : Tape) (work : Fin k → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ i, Parked (work i))
    (ha : work ra = regTape a) (hb : work rb = regTape b) (hc : work rc = regTape c)
    (hbit : (work cursor).read = Γ.ofBool bit) :
    (streamMarkedRowTM ra cursor rb rc).HoareTime (EmitPred inp work ys)
      (EmitPred inp (Function.update work cursor ((work cursor).move .right))
        (ys ++ markedRow a b c bit)) (4*(a+b+c)+12) := by
  let w := Function.update work cursor ((work cursor).move .right)
  have hwp : ∀ i, Parked (w i) := by
    intro i
    by_cases hi : i = cursor
    · subst i
      simpa [w] using parked_move_right (work cursor) (hw cursor)
    · simpa [w,hi] using hw i
  have h₁ := emitRunTM_correct false ra a inp work ys hp hw ha
  have h₂ := emitCursorBitTM_correct cursor bit inp work
    (ys ++ List.replicate a false) hp hw hbit
  have h₃ := emitRunTM_correct false rb b inp w
    ((ys ++ List.replicate a false) ++ [bit]) hp hwp (by simpa [w,hbne] using hb)
  have h₄ := emitBitsTM_hoareTime [true] inp w
    (((ys ++ List.replicate a false) ++ [bit]) ++ List.replicate b false) hp hwp
  have h₅ := emitRunTM_correct false rc c inp w
    ((((ys ++ List.replicate a false) ++ [bit]) ++ List.replicate b false) ++ [true])
    hp hwp (by simpa [w,hcne] using hc)
  have h₄₅ := seqTM_hoareTime _ _ h₄ (emitPred_transition hp hwp _) h₅
  have h₃₄₅ := seqTM_hoareTime _ _ h₃ (emitPred_transition hp hwp _) h₄₅
  have h₂₃₄₅ := seqTM_hoareTime _ _ h₂ (emitPred_transition hp hwp _) h₃₄₅
  have h := seqTM_hoareTime _ _ h₁ (emitPred_transition hp hw _) h₂₃₄₅
  have ht : (4*a+2)+1+(1+1+((4*b+2)+1+(1+1+(4*c+2)))) = 4*(a+b+c)+12 := by omega
  simpa only [streamMarkedRowTM,markedRow,List.length_singleton,List.append_assoc,ht] using h

def bodyCursor (bits : List Bool) (pos : Nat) : Tape :=
  {head := pos+1,cells := (Tape.init (bits.map Γ.ofBool)).cells}

theorem bodyCursor_parked (bits : List Bool) (pos : Nat) : Parked (bodyCursor bits pos) :=
  ⟨by change 1 ≤ pos+1; omega,Tape.init_ofBool_cells_ne_start bits⟩

theorem bodyCursor_next (bits : List Bool) (pos : Nat) :
    (bodyCursor bits pos).move .right = bodyCursor bits (pos+1) := rfl

theorem cnfBodyCursor_read {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (j : Fin m) (x : Choice n) :
    (bodyCursor (cnfBody Φ) (finProdFinEquiv (j,choiceOffset n x)).val).read =
      Γ.ofBool (decide (x ∈ Φ j)) := by
  change (Tape.init ((cnfBody Φ).map Γ.ofBool)).cells
    ((finProdFinEquiv (j,choiceOffset n x)).val+1) = _
  rw [Tape.init_cells_succ]
  simp only [List.getElem?_map,cnfBody,List.getElem?_ofFn]
  rw [dif_pos (finProdFinEquiv (j,choiceOffset n x)).isLt]
  change Γ.ofBool (decide ((choiceOffset n).symm
    (finProdFinEquiv.symm (finProdFinEquiv (j,choiceOffset n x))).2 ∈
      Φ (finProdFinEquiv.symm (finProdFinEquiv (j,choiceOffset n x))).1)) = _
  simp only [Equiv.symm_apply_apply]

/-- Actual clause product row, consuming the next CNF incidence from a work
tape. Copying and positioning that stream are explicit outer obligations. -/
theorem streamClauseOutput_correct {n m k : Nat} (Φ : Fin m → Finset (Choice n))
    (j : Fin m) (x : Choice n) (ra cursor rb rc : Fin k)
    (hbne : rb ≠ cursor) (hcne : rc ≠ cursor)
    (inp : Tape) (work : Fin k → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ i, Parked (work i))
    (ha : work ra = regTape (wirePosition (Wire.clause (n := n) j)))
    (hb : work rb = regTape
      (1+Fintype.card (Wire n m)+(stepCode n m (.clause j x)).val-wirePosition (Wire.clause (n := n) j)-1))
    (hc : work rc = regTape
      (moleculeCount n m-(1+Fintype.card (Wire n m)+(stepCode n m (.clause j x)).val)-1))
    (hcursor : work cursor = bodyCursor (cnfBody Φ) (finProdFinEquiv (j,choiceOffset n x)).val) :
    (streamMarkedRowTM ra cursor rb rc).HoareTime (EmitPred inp work ys)
      (EmitPred inp (Function.update work cursor
        (bodyCursor (cnfBody Φ) ((finProdFinEquiv (j,choiceOffset n x)).val+1)))
        (ys ++ auxiliaryOutputRow Φ (.clause j x)))
      (4*(wirePosition (Wire.clause (n := n) j)+
        (1+Fintype.card (Wire n m)+(stepCode n m (.clause j x)).val-wirePosition (Wire.clause (n := n) j)-1)+
        (moleculeCount n m-(1+Fintype.card (Wire n m)+(stepCode n m (.clause j x)).val)-1))+12) := by
  have hread : (work cursor).read = Γ.ofBool (decide (x ∈ Φ j)) := by
    rw [hcursor]
    exact cnfBodyCursor_read Φ j x
  have h := streamMarkedRowTM_correct ra cursor rb rc hbne hcne _ _ _ (decide (x ∈ Φ j))
    inp work ys hp hw ha hb hc hread
  rw [hcursor,bodyCursor_next] at h
  simpa only [auxiliaryOutputRow,signalOutput] using h

end IrrRAFEnumeration.SATSource

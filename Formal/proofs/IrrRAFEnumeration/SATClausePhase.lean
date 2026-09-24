import proofs.IrrRAFEnumeration.SATClauseBoundary

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource Complexity Complexity.TM

def clauseBlockTM : TM 13 := seqTM clauseInnerTM clauseBoundaryTM

def clauseBlockBound (n m : Nat) : Nat :=
  (2*n*(100*(moleculeCount n m+1)+3)+2)+1+
    4096*(n+m+Fintype.card (Wire n m)+Fintype.card (Step n m)+
      moleculeCount n m+reactionCount n m+1)^2

theorem clauseBlockTM_correct {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (j : Fin m) (outer : Tape) (ho : Parked outer) (ys : List Bool) :
    clauseBlockTM.HoareTime
      (EmitPred (parkedInput (cnfBits Φ)) (clauseWork Φ j.val 0 outer) ys)
      (EmitPred (parkedInput (cnfBits Φ)) (clauseWork Φ (j.val+1) 0 outer)
        (ys ++ clauseRowsPrefix Φ j (2*n))) (clauseBlockBound n m) := by
  have hw : ∀ k, Parked (clauseWork Φ j.val (2*n) outer k) := by
    intro k
    fin_cases k <;> first | exact parked_regTape _ | exact ho | exact cnfStreamCursor_parked Φ _
  exact seqTM_hoareTime _ _ (clauseInnerTM_correct Φ j outer ho ys)
    (emitPred_transition (parkedInput_parked _) hw _)
    (clauseBoundaryTM_correct Φ j.val j.isLt outer ho (ys ++ clauseRowsPrefix Φ j (2*n)))

def clausePhasePrefix {n m : Nat} (Φ : Fin m → Finset (Choice n)) : Nat → List Bool
  | 0 => []
  | j+1 => clausePhasePrefix Φ j ++
      if hj : j < m then clauseRowsPrefix Φ ⟨j,hj⟩ (2*n) else []

def clausePhaseTM : TM 13 := forRegTM clauseBlockTM 7

theorem clausePhaseTM_correct {n m : Nat} (Φ : Fin m → Finset (Choice n)) (ys : List Bool) :
    clausePhaseTM.HoareTime
      (EmitPred (parkedInput (cnfBits Φ)) (clauseWork Φ 0 0 (regTape m)) ys)
      (EmitPred (parkedInput (cnfBits Φ)) (clauseWork Φ m 0 (regTape m))
        (ys ++ clausePhasePrefix Φ m))
      (m*(clauseBlockBound n m+3)+2) := by
  have hp := parkedInput_parked (cnfBits Φ)
  have hw : ∀ j k, Parked (clauseWork Φ j 0 (regTape m) k) := by
    intro j k
    fin_cases k <;> first | exact parked_regTape _ | exact cnfStreamCursor_parked Φ _
  have he : ∀ j (t : Tape), Function.update (clauseWork Φ j 0 (regTape m)) 7 t =
      clauseWork Φ j 0 t := by
    intro j t
    funext k
    fin_cases k <;> simp [clauseWork]
  have hbody : ∀ j, j < m → clauseBlockTM.HoareTime
      (EmitPred (parkedInput (cnfBits Φ))
        (Function.update (clauseWork Φ j 0 (regTape m)) 7 ⟨j+2,regCells m⟩)
        (ys ++ clausePhasePrefix Φ j))
      (EmitPred (parkedInput (cnfBits Φ))
        (Function.update (clauseWork Φ (j+1) 0 (regTape m)) 7 ⟨j+2,regCells m⟩)
        (ys ++ clausePhasePrefix Φ (j+1))) (clauseBlockBound n m) := by
    intro j hj
    rw [he,he]
    have h := clauseBlockTM_correct Φ ⟨j,hj⟩ ⟨j+2,regCells m⟩
      (parked_regCells (by omega)) (ys ++ clausePhasePrefix Φ j)
    simpa only [clausePhasePrefix,dif_pos hj,List.append_assoc] using h
  have h := forRegTM_hoareTime clauseBlockTM (7 : Fin 13) m (parkedInput (cnfBits Φ))
    (fun j => clauseWork Φ j 0 (regTape m)) (fun j => ys ++ clausePhasePrefix Φ j)
    (clauseBlockBound n m) hp (fun _ => rfl) (fun j k _ => hw j k) hbody
  have ht : m*(clauseBlockBound n m+2)+(m+2) = m*(clauseBlockBound n m+3)+2 := by ring
  simpa only [clausePhaseTM,clausePhasePrefix,List.append_nil,ht] using h

end IrrRAFEnumeration.SATSource

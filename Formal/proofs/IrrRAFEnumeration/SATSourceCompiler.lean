import proofs.IrrRAFEnumeration.SATTerminalPhase
import proofs.IrrRAFEnumeration.SATTerminalDock

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource Complexity Complexity.TM

/-- One fixed machine; formula dimensions and incidences are read from input. -/
def sourceCompilerTM : TM 13 := seqTM initializedClauseTM terminalTM

/-- Complete original dense CRS encoding, from actual CNF input and blank
tapes, with a uniform polynomial tape-step bound. This statement concerns
well-formed CNF encodings; a total string-domain adapter remains separate. -/
theorem sourceCompilerTM_correct {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    sourceCompilerTM.HoareTime
      (fun inp work out => inp = Tape.init ((cnfBits Φ).map Γ.ofBool) ∧
        (∀ i, work i = Tape.init []) ∧ out = Tape.init [])
      (EmitPred (parkedInput (cnfBits Φ))
        (resetWork n m (Fintype.card (Wire n m)) (Fintype.card (Step n m))
          (moleculeCount n m) (cnfStreamCursor Φ (2*n*m)))
        (sourceBits Φ))
      (10000000000*((cnfBits Φ).length+1)^5) := by
  have hi := initializedClauseTM_correct Φ
  rw [clauseWork_endpoint] at hi
  have hw : ∀ i, Parked (terminalWork n m (Fintype.card (Wire n m)) (Fintype.card (Step n m))
      (moleculeCount n m) (cnfStreamCursor Φ (2*n*m)) i) := by
    intro i
    fin_cases i <;> first | exact parked_regTape _ | exact cnfStreamCursor_parked Φ _
  have ht := terminalTM_correct n m (Fintype.card (Wire n m)) (Fintype.card (Step n m))
    (moleculeCount n m) (cnfStreamCursor Φ (2*n*m)) (parkedInput (cnfBits Φ))
    (clauseSourcePrefix Φ) (cnfStreamCursor_parked Φ _) (parkedInput_parked _)
    (by rw [step_card]; omega)
  have h := seqTM_hoareTime _ _ hi
    (emitPred_transition (parkedInput_parked _) hw (clauseSourcePrefix Φ)) ht
  have hout : clauseSourcePrefix Φ ++
      (finishPattern n m (Fintype.card (Wire n m)) (Fintype.card (Step n m)) (moleculeCount n m) ++
        resetPattern (Fintype.card (Wire n m)) (Fintype.card (Step n m))) = sourceBits Φ := by
    rw [← afterClauseRows_eq_terminalPatterns Φ]
    exact (sourceBits_eq_clause_prefix_append Φ).symm
  rw [hout] at h
  apply h.mono_bound
  let L := (cnfBits Φ).length+1
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hn : n ≤ L := by dsimp [L]; rw [cnfBits_length]; omega
  have hm : m ≤ L := by dsimp [L]; rw [cnfBits_length]; omega
  have hnm : n*m ≤ L^2 := by simpa [pow_two] using Nat.mul_le_mul hn hm
  have hL2 : L ≤ L^2 := by nlinarith
  have hsum : n+m+Fintype.card (Wire n m)+Fintype.card (Step n m)+moleculeCount n m+1 ≤ 40*L^2 := by
    simp [wire_card,step_card,moleculeCount]
    nlinarith
  have hsquare := Nat.pow_le_pow_left hsum 2
  have h45 : L^4 ≤ L^5 := Nat.pow_le_pow_right hL (by decide)
  change 1000000000*L^5+1+10000*(n+m+Fintype.card (Wire n m)+
      Fintype.card (Step n m)+moleculeCount n m+1)^2 ≤ 10000000000*L^5
  nlinarith

end IrrRAFEnumeration.SATSource

import proofs.IrrRAFEnumeration.SATCoverageSetup
import proofs.IrrRAFEnumeration.SATCoverageDock
import proofs.IrrRAFEnumeration.SATConflictPrefix

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource Complexity Complexity.TM

def preparedCoverageTM : TM 13 := seqTM coverageSetupTM coveragePhaseTM

theorem preparedCoverageTM_correct {n m : Nat} (Φ : Fin m → Finset (Choice n)) (ys : List Bool) :
    preparedCoverageTM.HoareTime
      (EmitPred (parkedInput (cnfBits Φ))
        (conflictWork n m (Fintype.card (Wire n m)) (Fintype.card (Step n m))
          (moleculeCount n m) (reactionCount n m) n (cnfStreamCursor Φ 0)) ys)
      (EmitPred (parkedInput (cnfBits Φ))
        (coverageWork n m (Fintype.card (Wire n m)) (Fintype.card (Step n m))
          (moleculeCount n m) (reactionCount n m) n (cnfStreamCursor Φ 0))
        (ys ++ coverageSourceRows Φ))
      (4096*(n+m+Fintype.card (Wire n m)+Fintype.card (Step n m)+
        moleculeCount n m+reactionCount n m+1)^2+1+
        (n*(400*(moleculeCount n m+1)+3)+2)) := by
  have hw : ∀ i, Parked (coverageWork n m (Fintype.card (Wire n m)) (Fintype.card (Step n m))
      (moleculeCount n m) (reactionCount n m) 0 (cnfStreamCursor Φ 0) i) := by
    intro i
    fin_cases i <;> first | exact parked_regTape _ | exact cnfStreamCursor_parked Φ 0
  exact seqTM_hoareTime _ _ (coverageSetupTM_correct Φ ys)
    (emitPred_transition (parkedInput_parked _) hw ys) (coveragePhaseTM_source_correct Φ ys)

def initializedCoverageTM : TM 13 := seqTM initializedConflictTM preparedCoverageTM

/-- Actual initialized compiler through literals, conflicts and coverage.
Clause, finish and reset reactions remain to be emitted. -/
theorem initializedCoverageTM_correct {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    initializedCoverageTM.HoareTime
      (fun inp work out => inp = Tape.init ((cnfBits Φ).map Γ.ofBool) ∧
        (∀ i, work i = Tape.init []) ∧ out = Tape.init [])
      (EmitPred (parkedInput (cnfBits Φ))
        (coverageWork n m (Fintype.card (Wire n m)) (Fintype.card (Step n m))
          (moleculeCount n m) (reactionCount n m) n (cnfStreamCursor Φ 0))
        (conflictSourcePrefix Φ ++ coverageSourceRows Φ))
      (100000000*((cnfBits Φ).length+1)^4) := by
  have hw : ∀ i, Parked (conflictWork n m (Fintype.card (Wire n m)) (Fintype.card (Step n m))
      (moleculeCount n m) (reactionCount n m) n (cnfStreamCursor Φ 0) i) := by
    intro i
    fin_cases i <;> first | exact parked_regTape _ | exact cnfStreamCursor_parked Φ 0
  have h := seqTM_hoareTime _ _ (initializedConflictTM_correct Φ)
    (emitPred_transition (parkedInput_parked _) hw (conflictSourcePrefix Φ))
    (preparedCoverageTM_correct Φ (conflictSourcePrefix Φ))
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
  have hrow : 400*(moleculeCount n m+1)+3 ≤ 8403*L^2 := by nlinarith
  have hloop := Nat.mul_le_mul hn hrow
  have h34 : L^3 ≤ L^4 := Nat.pow_le_pow_right hL (by decide)
  change 10000000*L^4+1+(4096*(n+m+Fintype.card (Wire n m)+Fintype.card (Step n m)+
    moleculeCount n m+reactionCount n m+1)^2+1+(n*(400*(moleculeCount n m+1)+3)+2)) ≤
      100000000*L^4
  nlinarith

end IrrRAFEnumeration.SATSource

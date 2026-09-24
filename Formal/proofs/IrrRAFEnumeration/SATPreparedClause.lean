import proofs.IrrRAFEnumeration.SATClauseSetup
import proofs.IrrRAFEnumeration.SATClausePhase

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource Complexity Complexity.TM

def preparedClauseTM : TM 13 := seqTM clauseSetupTM clausePhaseTM

theorem preparedClauseTM_correct {n m : Nat} (Φ : Fin m → Finset (Choice n)) (ys : List Bool) :
    preparedClauseTM.HoareTime
      (EmitPred (parkedInput (cnfBits Φ))
        (coverageWork n m (Fintype.card (Wire n m)) (Fintype.card (Step n m))
          (moleculeCount n m) (reactionCount n m) n (cnfStreamCursor Φ 0)) ys)
      (EmitPred (parkedInput (cnfBits Φ)) (clauseWork Φ m 0 (regTape m))
        (ys ++ clausePhasePrefix Φ m))
      (4096*(n+m+Fintype.card (Wire n m)+Fintype.card (Step n m)+
        moleculeCount n m+reactionCount n m+1)^2+1+
        (m*(clauseBlockBound n m+3)+2)) := by
  have hw : ∀ k, Parked (clauseWork Φ 0 0 (regTape m) k) := by
    intro k
    fin_cases k <;> first | exact parked_regTape _ | exact cnfStreamCursor_parked Φ _
  exact seqTM_hoareTime _ _ (clauseSetupTM_correct Φ ys)
    (emitPred_transition (parkedInput_parked _) hw ys) (clausePhaseTM_correct Φ ys)

def initializedClauseTM : TM 13 := seqTM initializedCoverageTM preparedClauseTM

theorem initializedClauseTM_correct {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    initializedClauseTM.HoareTime
      (fun inp work out => inp = Tape.init ((cnfBits Φ).map Γ.ofBool) ∧
        (∀ i, work i = Tape.init []) ∧ out = Tape.init [])
      (EmitPred (parkedInput (cnfBits Φ)) (clauseWork Φ m 0 (regTape m))
        (coverageSourcePrefix Φ ++ clausePhasePrefix Φ m))
      (1000000000*((cnfBits Φ).length+1)^5) := by
  have hw : ∀ k, Parked (coverageWork n m (Fintype.card (Wire n m)) (Fintype.card (Step n m))
      (moleculeCount n m) (reactionCount n m) n (cnfStreamCursor Φ 0) k) := by
    intro k
    fin_cases k <;> first | exact parked_regTape _ | exact cnfStreamCursor_parked Φ _
  have h := seqTM_hoareTime _ _ (initializedCoverageTM_correct Φ)
    (emitPred_transition (parkedInput_parked _) hw (coverageSourcePrefix Φ))
    (preparedClauseTM_correct Φ (coverageSourcePrefix Φ))
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
  have hrow : 100*(moleculeCount n m+1)+3 ≤ 2103*L^2 := by nlinarith
  have hinner := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hn) hrow
  have h34 : L^3 ≤ L^4 := Nat.pow_le_pow_right hL (by decide)
  have h45 : L^4 ≤ L^5 := Nat.pow_le_pow_right hL (by decide)
  have hblock : clauseBlockBound n m+3 ≤ 10000000*L^4 := by
    unfold clauseBlockBound
    nlinarith
  have houter := Nat.mul_le_mul hm hblock
  change 100000000*L^4+1+(4096*(n+m+Fintype.card (Wire n m)+Fintype.card (Step n m)+
    moleculeCount n m+reactionCount n m+1)^2+1+(m*(clauseBlockBound n m+3)+2)) ≤
      1000000000*L^5
  nlinarith

end IrrRAFEnumeration.SATSource

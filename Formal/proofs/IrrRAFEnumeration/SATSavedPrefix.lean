import proofs.IrrRAFEnumeration.SATSavedCounts
import proofs.IrrRAFEnumeration.SATSourcePrefix

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource Complexity Complexity.TM

def sourceSavedWork {n m : Nat} (Φ : Fin m → Finset (Choice n)) : Fin 13 → Tape :=
  savedCounts n m (Fintype.card (Wire n m)) (Fintype.card (Step n m))
    (moleculeCount n m) (reactionCount n m) (cnfStreamCursor Φ 0)

theorem sourceSavedWork_parked {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    ∀ i, Parked (sourceSavedWork Φ i) := by
  intro i
  fin_cases i <;> first | exact parked_regTape _ | exact cnfStreamCursor_parked Φ 0

theorem sourceStreamWork_eq_unsaved {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    sourceStreamWork Φ = unsavedCounts n m (Fintype.card (Wire n m))
      (Fintype.card (Step n m)) (moleculeCount n m) (reactionCount n m) (cnfStreamCursor Φ 0) := by
  have hz : (Tape.init []).move .right = regTape 0 := reg_zero_init_bumped.eq_regT
  funext i
  fin_cases i <;> simp [sourceStreamWork,sourceCountWork,unsavedCounts,countTapes,hz]

theorem sourceSavedWork_frame {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    frameWork (m := 7) (countTapes ![n,m,Fintype.card (Wire n m),Fintype.card (Step n m),
      moleculeCount n m,reactionCount n m]) (sourceSavedWork Φ) = sourceSavedWork Φ := by
  funext i
  fin_cases i <;> simp [frameWork,sourceSavedWork,savedCounts,countTapes]

def savedPrefixWork {n m : Nat} (Φ : Fin m → Finset (Choice n)) : Fin 13 → Tape :=
  frameWork (m := 7) (literalRegs (moleculeCount n m-1) (2*n) (2*n)) (sourceSavedWork Φ)

def saveAndPrefixTM : TM 13 := seqTM saveCountsTM (sourcePrefixTM.liftTM 7)

theorem saveAndPrefixTM_correct {n m : Nat} (Φ : Fin m → Finset (Choice n)) (ys : List Bool) :
    saveAndPrefixTM.HoareTime (EmitPred (parkedInput (cnfBits Φ)) (sourceStreamWork Φ) ys)
      (EmitPred (parkedInput (cnfBits Φ)) (savedPrefixWork Φ) (ys ++ sourcePrefixBits Φ))
      (128*(n+m+Fintype.card (Wire n m)+Fintype.card (Step n m)+
        moleculeCount n m+reactionCount n m+1)^2+1+
        (12*moleculeCount n m+4*reactionCount n m+31+literalSourceBudget n m)) := by
  have hs := saveCountsTM_correct n m (Fintype.card (Wire n m)) (Fintype.card (Step n m))
    (moleculeCount n m) (reactionCount n m) (cnfStreamCursor Φ 0) (parkedInput (cnfBits Φ)) ys
    (cnfStreamCursor_parked Φ 0) (parkedInput_parked _)
  rw [← sourceStreamWork_eq_unsaved Φ] at hs
  have hp := liftTM_frame_correct sourcePrefixTM 7 (sourceSavedWork Φ)
    (fun i _ => sourceSavedWork_parked Φ i) _ _ _ _ _ _ _ (sourcePrefixTM_correct Φ ys)
  rw [sourceSavedWork_frame Φ] at hp
  exact seqTM_hoareTime _ _ hs
    (emitPred_transition (parkedInput_parked _) (sourceSavedWork_parked Φ) ys) hp

def initializedSavedPrefixTM : TM 13 := seqTM sourceStreamInitTM saveAndPrefixTM

/-- Emit the complete verified source prefix from ordinary initial tapes,
with every source count saved and the incidence stream ready for the suffix. -/
theorem initializedSavedPrefixTM_correct {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    initializedSavedPrefixTM.HoareTime
      (fun inp work out => inp = Tape.init ((cnfBits Φ).map Γ.ofBool) ∧
        (∀ i, work i = Tape.init []) ∧ out = Tape.init [])
      (EmitPred (parkedInput (cnfBits Φ)) (savedPrefixWork Φ) (sourcePrefixBits Φ))
      (1000000*((cnfBits Φ).length+1)^4) := by
  have h := seqTM_hoareTime _ _ (sourceStreamInitTM_correct Φ)
    (emitPred_transition (parkedInput_parked _) (sourceStreamWork_parked Φ) [])
    (saveAndPrefixTM_correct Φ [])
  simp only [List.nil_append] at h
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
  have hR : reactionCount n m ≤ 20*L^2 := by
    simp [reactionCount,Choice,step_card]
    nlinarith
  have h24 : L^2 ≤ L^4 := Nat.pow_le_pow_right hL (by decide)
  have hb := literalSourceBudget_polynomial Φ
  change literalSourceBudget n m ≤ 300000*L^4 at hb
  change 730*L^4+1+(128*(n+m+Fintype.card (Wire n m)+Fintype.card (Step n m)+
    moleculeCount n m+reactionCount n m+1)^2+1+
    (12*moleculeCount n m+4*reactionCount n m+31+literalSourceBudget n m)) ≤ 1000000*L^4
  nlinarith

end IrrRAFEnumeration.SATSource

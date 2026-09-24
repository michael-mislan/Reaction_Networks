import proofs.IrrRAFEnumeration.SATCountRegisters

namespace IrrRAFEnumeration.SATSource

open SATCompletion Complexity Complexity.TM

theorem countInitial_tapes (n m : Nat) :
    countTapes (countInitial n m) =
      Function.update (Function.update (fun _ : Fin 6 => regTape 0) 0 (regTape n)) 1 (regTape m) := by
  funext i
  fin_cases i <;> simp [countTapes, countInitial]

def sourceInitTM : TM 6 := seqTM (dimensionInitTM 0 1) (countSeqTM countProgram)

/-- Initialize actual encoded-CRS dimensions from the CNF tape. Registers
hold n,m,wire count,signal-rule count,molecule count,reaction count. -/
theorem sourceInitTM_correct {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    sourceInitTM.HoareTime
      (fun inp work out => inp = Tape.init ((cnfBits Φ).map Γ.ofBool) ∧
        (∀ i, work i = Tape.init []) ∧ out = Tape.init [])
      (EmitPred (parkedInput (cnfBits Φ))
        (countTapes ![n,m,Fintype.card (Wire n m),Fintype.card (Step n m),
          moleculeCount n m,reactionCount n m]) [])
      (710*((cnfBits Φ).length+1)^4) := by
  have h₁ := dimensionInitTM_correct Φ (0 : Fin 6) 1 (by decide)
  rw [← countInitial_tapes] at h₁
  have h₂ := countRegistersTM_correct n m (parkedInput (cnfBits Φ)) [] (parkedInput_parked _)
  have hall := seqTM_hoareTime _ _ h₁
    (emitPred_transition (parkedInput_parked _) (fun _ => parked_regTape _) []) h₂
  have he : ![n,m,3*n+m+1,3*n+2*n*m+1,6*n+2*n*m+m+4,5*n+2*n*m+2] =
      ![n,m,Fintype.card (Wire n m),Fintype.card (Step n m),moleculeCount n m,reactionCount n m] := by
    funext i
    fin_cases i <;> simp [wire_card, step_card, moleculeCount, reactionCount, Choice] <;> ring
  rw [he] at hall
  apply hall.mono_bound
  let L := (cnfBits Φ).length+1
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hnm : n+m+1 ≤ L := by dsimp [L]; rw [cnfBits_length]; omega
  have hp : (n+m+1)^4 ≤ L^4 := Nat.pow_le_pow_left hnm 4
  have hlin : L ≤ L^4 := by
    simpa using Nat.pow_le_pow_right hL (show 1 ≤ 4 by decide)
  change 3*n+3*m+13+1+692*(n+m+1)^4 ≤ 710*L^4
  nlinarith

end IrrRAFEnumeration.SATSource

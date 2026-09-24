import proofs.IrrRAFEnumeration.SATLiteralSetup
import proofs.IrrRAFEnumeration.SATSourceInit

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource Complexity Complexity.TM

def preparedLiteralTM : TM 6 := seqTM literalSetupTM literalPhaseTM

def literalSourceBudget (n m : Nat) : Nat :=
  128*(n+m+Fintype.card (Wire n m)+Fintype.card (Step n m)+
    moleculeCount n m+reactionCount n m+1)^2+1+
    (2*n*(14*(moleculeCount n m-1)+51)+2)

/-- The literal phase now starts from source counts, not prepared loop
registers. It preserves the existing output prefix and charges the setup. -/
theorem preparedLiteralTM_correct {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (ys : List Bool) :
    preparedLiteralTM.HoareTime
      (EmitPred (parkedInput (cnfBits Φ))
        (countTapes ![n,m,Fintype.card (Wire n m),Fintype.card (Step n m),
          moleculeCount n m,reactionCount n m]) ys)
      (EmitPred (parkedInput (cnfBits Φ))
        (literalRegs (moleculeCount n m-1) (2*n) (2*n))
        (ys ++ (List.ofFn (fun i : Fin (Fintype.card (Choice n)) => reactionRows Φ (.inl i))).flatten))
      (literalSourceBudget n m) := by
  have h₁ := literalSetupTM_correct n m (Fintype.card (Wire n m))
    (Fintype.card (Step n m)) (moleculeCount n m) (reactionCount n m)
    (parkedInput (cnfBits Φ)) ys (parkedInput_parked _)
  have hcard : Fintype.card (Choice n) = 2*n := by simp [Choice,Nat.mul_comm]
  have h₂ := literalPhaseTM_source_correct Φ ys
  have hstart : literalRegs (moleculeCount n m-1) (Fintype.card (Choice n)) 0 =
      literalRegs (moleculeCount n m-1) (2*n) 0 := by rw [hcard]
  have hfinal : literalRegs (moleculeCount n m-1) (Fintype.card (Choice n)) (Fintype.card (Choice n)) =
      literalRegs (moleculeCount n m-1) (2*n) (2*n) := by rw [hcard]
  have htime : Fintype.card (Choice n)*(14*(moleculeCount n m-1)+51)+2 =
      2*n*(14*(moleculeCount n m-1)+51)+2 := by rw [hcard]
  rw [hstart,hfinal,htime] at h₂
  have hw : ∀ i, Parked (literalRegs (moleculeCount n m-1) (2*n) 0 i) := by
    intro i
    fin_cases i <;> exact parked_regTape _
  have h := seqTM_hoareTime _ _ h₁
    (emitPred_transition (parkedInput_parked _) hw ys) h₂
  have he : literalSetupInput n m (Fintype.card (Wire n m)) (Fintype.card (Step n m))
      (moleculeCount n m) (reactionCount n m) =
      countTapes ![n,m,Fintype.card (Wire n m),Fintype.card (Step n m),
        moleculeCount n m,reactionCount n m] := by
    funext i
    fin_cases i <;> rfl
  rw [he] at h
  exact h

theorem literalSourceBudget_polynomial {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    literalSourceBudget n m ≤ 300000*((cnfBits Φ).length+1)^4 := by
  let L := (cnfBits Φ).length+1
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hn : n ≤ L := by dsimp [L]; rw [cnfBits_length]; omega
  have hm : m ≤ L := by dsimp [L]; rw [cnfBits_length]; omega
  have hnm : n*m ≤ L^2 := by simpa [pow_two] using Nat.mul_le_mul hn hm
  have hL₂ : L ≤ L^2 := by nlinarith
  have hsum : n+m+Fintype.card (Wire n m)+Fintype.card (Step n m)+
      moleculeCount n m+reactionCount n m+1 ≤ 40*L^2 := by
    simp [wire_card,step_card,moleculeCount,reactionCount,Choice]
    nlinarith
  have hsquare := Nat.pow_le_pow_left hsum 2
  have hM : moleculeCount n m ≤ 20*L^2 := by
    simp [moleculeCount,wire_card,step_card]
    nlinarith
  have hrow : 14*(moleculeCount n m-1)+51 ≤ 331*L^2 := by
    nlinarith [Nat.sub_le (moleculeCount n m) 1]
  have hloop := Nat.mul_le_mul (show 2*n ≤ 2*L by omega) hrow
  have hL₃₄ : L^3 ≤ L^4 := Nat.pow_le_pow_right hL (by decide)
  have hL₄ : 1 ≤ L^4 := by
    have : 0 < L^4 := by positivity
    omega
  change _ ≤ 300000*L^4
  unfold literalSourceBudget
  nlinarith

def initializedLiteralTM : TM 6 := seqTM sourceInitTM preparedLiteralTM

/-- A fixed machine emits the literal-reaction rows from the actual CNF
input with blank work/output tapes. This is one phase, not the whole source. -/
theorem initializedLiteralTM_correct {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    initializedLiteralTM.HoareTime
      (fun inp work out => inp = Tape.init ((cnfBits Φ).map Γ.ofBool) ∧
        (∀ i, work i = Tape.init []) ∧ out = Tape.init [])
      (EmitPred (parkedInput (cnfBits Φ))
        (literalRegs (moleculeCount n m-1) (2*n) (2*n))
        ((List.ofFn (fun i : Fin (Fintype.card (Choice n)) => reactionRows Φ (.inl i))).flatten))
      (301000*((cnfBits Φ).length+1)^4) := by
  have h := seqTM_hoareTime _ _ (sourceInitTM_correct Φ)
    (emitPred_transition (parkedInput_parked _) (fun _ => parked_regTape _) [])
    (preparedLiteralTM_correct Φ [])
  simp only [List.nil_append] at h
  apply h.mono_bound
  have hb := literalSourceBudget_polynomial Φ
  have hpos : 1 ≤ ((cnfBits Φ).length+1)^4 := by
    have : 0 < ((cnfBits Φ).length+1)^4 := by positivity
    omega
  omega

end IrrRAFEnumeration.SATSource

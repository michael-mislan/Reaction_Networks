import proofs.IrrRAFEnumeration.SATPreparedLiteral
import proofs.IrrRAFEnumeration.SATSourcePreamble

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource Complexity Complexity.TM

def sourcePrefixBits {n m : Nat} (Φ : Fin m → Finset (Choice n)) : List Bool :=
  sourceHeader (moleculeCount n m) (reactionCount n m) ++
    ([true] ++ List.replicate (moleculeCount n m-1) false) ++
    (List.ofFn (fun i : Fin (Fintype.card (Choice n)) => reactionRows Φ (.inl i))).flatten

/-- The emitted prefix is literally the beginning of the existing full source
encoding; the outstanding suffix consists of the auxiliary reactions. -/
theorem sourceBits_eq_prefix_append {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    sourceBits Φ = sourcePrefixBits Φ ++
      (List.ofFn (fun j : Fin (Fintype.card (Step n m)+1) => reactionRows Φ (.inr j))).flatten := by
  have hsplit := ofFn_sum_equiv
    (a := Fintype.card (Choice n)) (b := Fintype.card (Step n m)+1)
    (fun r => reactionRows Φ ((reactionCode _ _).symm r))
  simp only [reactionCode,Equiv.symm_apply_apply] at hsplit
  rw [← runSourceBits_correct Φ]
  unfold runSourceBits runSourceBody
  simp only [runReactionRows_correct,reactionCode]
  dsimp only [reactionCount]
  rw [hsplit]
  simp only [List.flatten_append,sourcePrefixBits,sourceHeader,spanRow,
    List.replicate_zero,List.replicate_one,List.nil_append,List.append_assoc]
  rfl

def sourcePrefixTM : TM 6 :=
  seqTM (sourceHeaderTM 4 5) (seqTM (foodRowTM 4) preparedLiteralTM)

theorem sourcePrefixTM_correct {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (ys : List Bool) :
    sourcePrefixTM.HoareTime
      (EmitPred (parkedInput (cnfBits Φ))
        (countTapes ![n,m,Fintype.card (Wire n m),Fintype.card (Step n m),
          moleculeCount n m,reactionCount n m]) ys)
      (EmitPred (parkedInput (cnfBits Φ))
        (literalRegs (moleculeCount n m-1) (2*n) (2*n))
        (ys ++ sourcePrefixBits Φ))
      (12*moleculeCount n m+4*reactionCount n m+31+literalSourceBudget n m) := by
  let work := countTapes ![n,m,Fintype.card (Wire n m),Fintype.card (Step n m),
    moleculeCount n m,reactionCount n m]
  have hw : ∀ i, Parked (work i) := fun _ => parked_regTape _
  have hp := parkedInput_parked (cnfBits Φ)
  have hM : 1 ≤ moleculeCount n m := by unfold moleculeCount; omega
  have h₁ := sourceHeaderTM_correct (4 : Fin 6) 5 (moleculeCount n m) (reactionCount n m)
    (parkedInput (cnfBits Φ)) work ys hp hw rfl rfl
  have h₂ := foodRowTM_correct (4 : Fin 6) (moleculeCount n m) hM
    (parkedInput (cnfBits Φ)) work
    (ys ++ sourceHeader (moleculeCount n m) (reactionCount n m)) hp hw rfl
  have h₃ := preparedLiteralTM_correct Φ
    ((ys ++ sourceHeader (moleculeCount n m) (reactionCount n m)) ++
      ([true] ++ List.replicate (moleculeCount n m-1) false))
  have h₂₃ := seqTM_hoareTime _ _ h₂ (emitPred_transition hp hw _) h₃
  have h := seqTM_hoareTime _ _ h₁ (emitPred_transition hp hw _) h₂₃
  have ht : (4*moleculeCount n m+4*reactionCount n m+9)+1+
      ((8*moleculeCount n m+20)+1+literalSourceBudget n m) =
      12*moleculeCount n m+4*reactionCount n m+31+literalSourceBudget n m := by omega
  simpa only [sourcePrefixTM,sourcePrefixBits,List.append_assoc,ht] using h

def initializedSourcePrefixTM : TM 6 := seqTM sourceInitTM sourcePrefixTM

/-- A complete source prefix from blank tapes, including every preparation
and emission step. Auxiliary reaction phases remain to be appended. -/
theorem initializedSourcePrefixTM_correct {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    initializedSourcePrefixTM.HoareTime
      (fun inp work out => inp = Tape.init ((cnfBits Φ).map Γ.ofBool) ∧
        (∀ i, work i = Tape.init []) ∧ out = Tape.init [])
      (EmitPred (parkedInput (cnfBits Φ))
        (literalRegs (moleculeCount n m-1) (2*n) (2*n)) (sourcePrefixBits Φ))
      (400000*((cnfBits Φ).length+1)^4) := by
  have h := seqTM_hoareTime _ _ (sourceInitTM_correct Φ)
    (emitPred_transition (parkedInput_parked _) (fun _ => parked_regTape _) [])
    (sourcePrefixTM_correct Φ [])
  simp only [List.nil_append] at h
  apply h.mono_bound
  let L := (cnfBits Φ).length+1
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hn : n ≤ L := by dsimp [L]; rw [cnfBits_length]; omega
  have hm : m ≤ L := by dsimp [L]; rw [cnfBits_length]; omega
  have hnm : n*m ≤ L^2 := by simpa [pow_two] using Nat.mul_le_mul hn hm
  have hL₂ : L ≤ L^2 := by nlinarith
  have hM : moleculeCount n m ≤ 20*L^2 := by
    simp [moleculeCount,wire_card,step_card]
    nlinarith
  have hR : reactionCount n m ≤ 20*L^2 := by
    simp [reactionCount,Choice,step_card]
    nlinarith
  have hpow : L^2 ≤ L^4 := Nat.pow_le_pow_right hL (by decide)
  have hb := literalSourceBudget_polynomial Φ
  change literalSourceBudget n m ≤ 300000*L^4 at hb
  change 710*L^4+1+(12*moleculeCount n m+4*reactionCount n m+31+literalSourceBudget n m) ≤ 400000*L^4
  nlinarith

end IrrRAFEnumeration.SATSource

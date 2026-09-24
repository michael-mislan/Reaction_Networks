import proofs.IrrRAFEnumeration.SATLiteralDock

namespace IrrRAFEnumeration.SATSource

open Complexity Complexity.TM

def literalSetupInput (n m w q M r : Nat) : Fin 6 → Tape :=
  ![regTape n,regTape m,regTape w,regTape q,regTape M,regTape r]

def literalSetupTM : TM 6 := seqTM (copyIntoTM 0 5) (seqTM (addIntoTM 0 5) (seqTM (copyIntoTM 4 2) (seqTM (decRegTM 2) (seqTM (decRegTM 4) (seqTM (decRegTM 4) (seqTM (clearRegTM 0) (seqTM (clearRegTM 1) (seqTM (incRegTM 1) (seqTM (clearRegTM 3) (incRegTM 3))))))))))

/-- Prepare all six literal-loop registers by actual copy/add/clear/inc/dec
machines. Persistent source counts must be saved on the framed extra tapes. -/
theorem literalSetupTM_correct (n m w q M r : Nat)
    (inp : Tape) (ys : List Bool) (hp : Parked inp) :
    literalSetupTM.HoareTime (EmitPred inp (literalSetupInput n m w q M r) ys)
      (EmitPred inp (literalRegs (M-1) (2*n) 0) ys)
      (128*(n+m+w+q+M+r+1)^2) := by
  let v₀ := literalSetupInput n m w q M r
  have hp₀ : ∀ i, Parked (v₀ i) := by
    intro i
    fin_cases i <;> exact parked_regTape _
  let v₁ := Function.update v₀ (5 : Fin 6) (regTape (n))
  have hp₁ : ∀ j, Parked (v₁ j) := updateReg_parked v₀ hp₀ _ _
  have h₁ := copyIntoTM_hoareTime (0 : Fin 6) 5 (by decide) n r inp v₀ ys hp (fun j _ => hp₀ j) rfl rfl
  let v₂ := Function.update v₁ (5 : Fin 6) (regTape (n+n))
  have hp₂ : ∀ j, Parked (v₂ j) := updateReg_parked v₁ hp₁ _ _
  have h₂ := addIntoTM_hoareTime (0 : Fin 6) 5 (by decide) n n inp v₁ ys hp (fun j _ => hp₁ j) rfl rfl
  let v₃ := Function.update v₂ (2 : Fin 6) (regTape (M))
  have hp₃ : ∀ j, Parked (v₃ j) := updateReg_parked v₂ hp₂ _ _
  have h₃ := copyIntoTM_hoareTime (4 : Fin 6) 2 (by decide) M w inp v₂ ys hp (fun j _ => hp₂ j) rfl rfl
  let v₄ := Function.update v₃ (2 : Fin 6) (regTape (M-1))
  have hp₄ : ∀ j, Parked (v₄ j) := updateReg_parked v₃ hp₃ _ _
  have h₄ := decRegTM_hoareTime (2 : Fin 6) M inp v₃ ys hp (fun j _ => hp₃ j) rfl
  let v₅ := Function.update v₄ (4 : Fin 6) (regTape (M-1))
  have hp₅ : ∀ j, Parked (v₅ j) := updateReg_parked v₄ hp₄ _ _
  have h₅ := decRegTM_hoareTime (4 : Fin 6) M inp v₄ ys hp (fun j _ => hp₄ j) rfl
  let v₆ := Function.update v₅ (4 : Fin 6) (regTape (M-1-1))
  have hp₆ : ∀ j, Parked (v₆ j) := updateReg_parked v₅ hp₅ _ _
  have h₆ := decRegTM_hoareTime (4 : Fin 6) (M-1) inp v₅ ys hp (fun j _ => hp₅ j) rfl
  let v₇ := Function.update v₆ (0 : Fin 6) (regTape (0))
  have hp₇ : ∀ j, Parked (v₇ j) := updateReg_parked v₆ hp₆ _ _
  have h₇ := clearRegTM_hoareTime (0 : Fin 6) n inp v₆ ys hp (fun j _ => hp₆ j) rfl
  let v₈ := Function.update v₇ (1 : Fin 6) (regTape (0))
  have hp₈ : ∀ j, Parked (v₈ j) := updateReg_parked v₇ hp₇ _ _
  have h₈ := clearRegTM_hoareTime (1 : Fin 6) m inp v₇ ys hp (fun j _ => hp₇ j) rfl
  let v₉ := Function.update v₈ (1 : Fin 6) (regTape (0+1))
  have hp₉ : ∀ j, Parked (v₉ j) := updateReg_parked v₈ hp₈ _ _
  have h₉ := incRegTM_hoareTime (1 : Fin 6) 0 inp v₈ ys hp (fun j _ => hp₈ j) rfl
  let v₁₀ := Function.update v₉ (3 : Fin 6) (regTape (0))
  have hp₁₀ : ∀ j, Parked (v₁₀ j) := updateReg_parked v₉ hp₉ _ _
  have h₁₀ := clearRegTM_hoareTime (3 : Fin 6) q inp v₉ ys hp (fun j _ => hp₉ j) rfl
  let v₁₁ := Function.update v₁₀ (3 : Fin 6) (regTape (0+1))
  have hp₁₁ : ∀ j, Parked (v₁₁ j) := updateReg_parked v₁₀ hp₁₀ _ _
  have h₁₁ := incRegTM_hoareTime (3 : Fin 6) 0 inp v₁₀ ys hp (fun j _ => hp₁₀ j) rfl
  have hchain10 := seqTM_hoareTime _ _ h₁₀ (emitPred_transition hp hp₁₀ ys) h₁₁
  have hchain9 := seqTM_hoareTime _ _ h₉ (emitPred_transition hp hp₉ ys) hchain10
  have hchain8 := seqTM_hoareTime _ _ h₈ (emitPred_transition hp hp₈ ys) hchain9
  have hchain7 := seqTM_hoareTime _ _ h₇ (emitPred_transition hp hp₇ ys) hchain8
  have hchain6 := seqTM_hoareTime _ _ h₆ (emitPred_transition hp hp₆ ys) hchain7
  have hchain5 := seqTM_hoareTime _ _ h₅ (emitPred_transition hp hp₅ ys) hchain6
  have hchain4 := seqTM_hoareTime _ _ h₄ (emitPred_transition hp hp₄ ys) hchain5
  have hchain3 := seqTM_hoareTime _ _ h₃ (emitPred_transition hp hp₃ ys) hchain4
  have hchain2 := seqTM_hoareTime _ _ h₂ (emitPred_transition hp hp₂ ys) hchain3
  have hchain1 := seqTM_hoareTime _ _ h₁ (emitPred_transition hp hp₁ ys) hchain2
  have he : v₁₁ = literalRegs (M-1) (2*n) 0 := by
    funext i
    fin_cases i <;> simp [v₁₁,v₁₀,v₉,v₈,v₇,v₆,v₅,v₄,v₃,v₂,v₁,v₀,literalSetupInput,literalRegs,two_mul]
  change literalSetupTM.HoareTime _ (EmitPred inp v₁₁ ys) _ at hchain1
  rw [he] at hchain1
  apply hchain1.mono_bound
  let B := n+m+w+q+M+r+1
  have hn : n ≤ B := by dsimp [B]; omega
  have hm : m ≤ B := by dsimp [B]; omega
  have hw : w ≤ B := by dsimp [B]; omega
  have hq : q ≤ B := by dsimp [B]; omega
  have hM : M ≤ B := by dsimp [B]; omega
  have hr : r ≤ B := by dsimp [B]; omega
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hn₂ : n^2 ≤ B^2 := Nat.pow_le_pow_left hn 2
  have hM₂ : M^2 ≤ B^2 := Nat.pow_le_pow_left hM 2
  have hB₂ : B ≤ B^2 := by nlinarith
  change _ ≤ 128*B^2
  nlinarith [Nat.sub_le M 1]

end IrrRAFEnumeration.SATSource

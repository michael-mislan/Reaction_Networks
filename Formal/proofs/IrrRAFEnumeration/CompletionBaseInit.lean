import proofs.IrrRAFEnumeration.CompletionBaseAssembly
import proofs.IrrRAFEnumeration.SATDimensionInit

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

/-- The original CRS has two unary headers. No completion-query parser is needed. -/
theorem originalDimensionRegs_correct {d r k : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (rd rr : Fin k) (hne : rr ≠ rd) (work : Fin k → Tape) (ys : List Bool)
    (hw : ∀ i, Parked (work i)) (hd : work rd = regTape 0) (hr : work rr = regTape 0) :
    (dimensionRegsTM rd rr).HoareTime
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _))) work ys)
      (EmitPred (advanceInput (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _))) (d+r+2))
        (Function.update (Function.update work rd (regTape d)) rr (regTape r)) ys)
      (2*d+2*r+5) := by
  let body := List.ofFn (fun i => incidence Q C (Equiv.refl _) (Equiv.refl _)
    ((slotCode d r).symm i))
  let W := Function.update work rd (regTape d)
  have hw' : ∀ i, Parked (W i) := updateReg_parked work hw rd d
  have h₁ := headerRegTM_bits rd [] (List.replicate r true ++ false :: body)
    d work ys hw hd
  have h₂ := headerRegTM_bits rr (List.replicate d true ++ [false]) body
    r W ys hw' (by simpa [W,Function.update_of_ne hne] using hr)
  have e₁ : [] ++ (List.replicate d true ++ false :: (List.replicate r true ++ false :: body)) =
      inputBits Q C (Equiv.refl _) (Equiv.refl _) := by
    simp [inputBits,body,List.append_assoc]
  have e₂ : (List.replicate d true ++ [false]) ++ (List.replicate r true ++ false :: body) =
      inputBits Q C (Equiv.refl _) (Equiv.refl _) := by
    simp [inputBits,body,List.append_assoc]
  rw [e₁] at h₁
  rw [e₂] at h₂
  simp only [List.length_nil,Nat.zero_add,List.length_append,List.length_replicate,
    List.length_singleton] at h₁ h₂
  have h := seqTM_hoareTime _ _ h₁
    (emitPred_transition (advanceInput_parked _ _ (parkedInput_parked _)) hw' ys) h₂
  have ep : d+1+r+1 = d+r+2 := by omega
  have et : (2*d+2)+1+(2*r+2) = 2*d+2*r+5 := by omega
  rw [ep,et] at h
  exact h

/-- Starts from the actual blank work tapes and restores the original input head. -/
theorem originalDimensionInit_correct {d r k : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (rd rr : Fin k) (hne : rr ≠ rd) :
    (dimensionInitTM rd rr).HoareTime
      (fun inp work out =>
        inp = Tape.init ((inputBits Q C (Equiv.refl _) (Equiv.refl _)).map Γ.ofBool) ∧
        (∀ i, work i = Tape.init []) ∧ out = Tape.init [])
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (Function.update (Function.update (fun _ : Fin k => regTape 0) rd (regTape d))
          rr (regTape r)) [])
      (3*d+3*r+13) := by
  let z := inputBits Q C (Equiv.refl _) (Equiv.refl _)
  let W₀ : Fin k → Tape := fun _ => regTape 0
  let W := Function.update (Function.update W₀ rd (regTape d)) rr (regTape r)
  have hw : ∀ i, Parked (W i) :=
    updateReg_parked _ (updateReg_parked _ (fun _ => parked_regTape _) _ _) _ _
  have h₁ : (bumpTM (n := k)).HoareTime _ (EmitPred (parkedInput z) W₀ []) 1 :=
    (bumpTM_hoareTime z).strengthen_post (by
      rintro inp work out ⟨hi,hw,ho⟩
      exact ⟨hi,funext (fun i => (hw i).eq_regT),ho⟩)
  have h₂ := originalDimensionRegs_correct Q C rd rr hne W₀ []
    (fun _ => parked_regTape _) rfl rfl
  have h₃ := rewindParsedInput_correct z (d+r+2) W [] hw
  have h₂₃ := seqTM_hoareTime _ _ h₂
    (emitPred_transition (advanceInput_parked _ _ (parkedInput_parked _)) hw []) h₃
  have h := seqTM_hoareTime _ _ h₁
    (emitPred_transition (parkedInput_parked _) (fun _ => parked_regTape _) []) h₂₃
  apply h.mono_bound
  omega

end IrrRAFEnumeration.CompletionQuery

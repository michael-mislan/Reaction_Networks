import proofs.IrrRAFEnumeration.CompletionQueryClock

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

/-- Reuse the existing emitter after one shared whole-machine entry bump. -/
def parkedBaseCompilerTM : TM 23 :=
  seqTM (seqTM (dimensionRegsTM 12 13) rewindInputTM)
    (seqTM baseBankTM baseEmitTM)

theorem existingBaseEmit_correct {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C] :
    baseEmitTM.HoareTime
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (baseRegWork (baseBankValues d r)) [])
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (baseRegWork (baseRunState d r 6)) (SAT.CNF.encode (assembledBase Q C)))
      (6*(baseRunPhaseTime (inputBits Q C (Equiv.refl _) (Equiv.refl _)).length+1)+1) := by
  let z := inputBits Q C (Equiv.refl _) (Equiv.refl _)
  have h := bigSeqTM_hoareTime ((List.finRange 6).map baseRunPhaseTM)
    (parkedInput z) (fun k => baseRegWork (baseRunState d r k)) (baseRunOutput Q C)
    (baseRunPhaseTime z.length) (parkedInput_parked z) (fun _ _ => parked_regTape _) (by
      intro k hk
      have hk6 : k < 6 := by simpa using hk
      simp only [List.getElem_map,List.getElem_finRange,Fin.cast_mk]
      have hh := baseRunPhaseTM_correct Q C ⟨k,hk6⟩ (baseRunOutput Q C k)
      rw [baseRunOutput_succ Q C ⟨k,hk6⟩] at hh
      exact hh)
  have hfull : baseRunOutput Q C 6 = SAT.CNF.encode (assembledBase Q C) := by
    simp [baseRunOutput,List.finRange_succ,basePhaseClauses,assembledBase,List.append_assoc]
  have hz : baseRunOutput Q C 0 = [] := by simp [baseRunOutput]
  simpa only [List.length_map,List.length_finRange,hfull,hz,baseRunState] using h

theorem parkedBaseCompiler_correct {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C] :
    parkedBaseCompilerTM.HoareTime
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (fun _ => regTape 0) [])
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (baseRegWork (baseRunState d r 6)) (SAT.CNF.encode (assembledBase Q C)))
      (baseCompilerTime (inputBits Q C (Equiv.refl _) (Equiv.refl _)).length) := by
  let z := inputBits Q C (Equiv.refl _) (Equiv.refl _)
  let W := Function.update (Function.update (fun _ : Fin 23 => regTape 0) 12 (regTape d))
    13 (regTape r)
  have hw : ∀ i, Parked (W i) :=
    updateReg_parked _ (updateReg_parked _ (fun _ => parked_regTape _) _ _) _ _
  have hdim := seqTM_hoareTime _ _
    (originalDimensionRegs_correct Q C (12 : Fin 23) 13 (by decide)
      (fun _ => regTape 0) [] (fun _ => parked_regTape _) rfl rfl)
    (emitPred_transition (advanceInput_parked _ _ (parkedInput_parked z)) hw [])
    (rewindParsedInput_correct z (d+r+2) W [] hw)
  have he : W = baseRegWork (baseBankInitial d r) := by
    simp only [baseBankInitial,baseRegWork_update]
    rfl
  rw [he] at hdim
  have hbank := baseBankTM_correct d r (parkedInput z) [] (parkedInput_parked z)
  rw [baseBankStage_final] at hbank
  have htail := seqTM_hoareTime _ _ hbank
    (emitPred_transition (parkedInput_parked z) (fun _ => parked_regTape _) [])
    (existingBaseEmit_correct Q C)
  have h := seqTM_hoareTime _ _ hdim
    (emitPred_transition (parkedInput_parked z) (fun _ => parked_regTape _) []) htail
  apply h.mono_bound
  have hd : d ≤ z.length := by simp [z,inputBits]
  have hr : r ≤ z.length := by simp [z,inputBits]; omega
  have hc : baseBankCap d r ≤ 10*(z.length+1)^2 := by
    have hdd := Nat.mul_le_mul hd hd
    unfold baseBankCap
    nlinarith
  have hb : opBudget (baseBankCap d r) ≤ opBudget (10*(z.length+1)^2) := by
    unfold opBudget
    gcongr
  change (2*d+2*r+5)+1+(d+r+2+3)+1+
    ((19*(opBudget (baseBankCap d r)+1)+1)+1+
      (6*(baseRunPhaseTime z.length+1)+1)) ≤ baseCompilerTime z.length
  unfold baseCompilerTime basePreparationTime
  omega

/-- Base bytes are stored in a fixed extra bank, preserving the original CRS input. -/
theorem placedParkedBase_correct {d r : Nat} (n : Nat)
    (Q : CRS (Fin d) (Fin r)) (C : Catalysis (Fin d) (Fin r)) [DecidableRel C] :
    (placeWorkTM n 0 parkedBaseCompilerTM.retargetOutput).HoareTime
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (placedClockWork n 0 (fun _ => regTape 0)
          (frameWork (m := 1) (fun _ : Fin 23 => regTape 0)
            (fun _ => accumulatorTape []))) [])
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (placedClockWork n 0 (fun _ => regTape 0)
          (frameWork (m := 1) (baseRegWork (baseRunState d r 6))
            (fun _ => accumulatorTape (SAT.CNF.encode (assembledBase Q C))))) [])
      (baseCompilerTime (inputBits Q C (Equiv.refl _) (Equiv.refl _)).length) := by
  exact placeEmitter_correct _ n 0 (fun _ => regTape 0) (fun _ _ => parked_regTape _)
    _ _ _ _ _ _ _ (redirectEmitter_correct _ _ _ _ _ _ _ _ (parkedBaseCompiler_correct Q C))

end IrrRAFEnumeration.CompletionQuery

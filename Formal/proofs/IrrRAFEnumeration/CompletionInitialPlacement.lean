import proofs.IrrRAFEnumeration.CompletionInitialCopy

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

def storedBaseBlockTM : TM 24 :=
  seqTM parkedBaseCompilerTM.retargetOutput (rewindWorkTM (Fin.last 23))

def initialBaseSource (n : Nat) : Fin (n+24) := ⟨n+23,by omega⟩
def initialBaseDest (n : Nat) (hn : 6 ≤ n) : Fin (n+24) := ⟨5,by omega⟩

def initialBaseWork (n d r : Nat) (base : List Bool) : Fin (n+24) → Tape :=
  placedClockWork n 0 (fun _ => regTape 0)
    (frameWork (m := 1) (baseRegWork (baseRunState d r 6))
      (fun _ => parkedInput base))

theorem initialBaseWork_parked (n d r : Nat) (base : List Bool) :
    ∀ i, Parked (initialBaseWork n d r base i) := by
  intro i
  unfold initialBaseWork placedClockWork frameWork
  split
  · split
    · exact parked_regTape _
    · exact parkedInput_parked _
  · exact parked_regTape _

theorem initialBaseWork_source (n d r : Nat) (base : List Bool) :
    initialBaseWork n d r base (initialBaseSource n) = parkedInput base := by
  simp [initialBaseWork,initialBaseSource,placedClockWork,placeWorkInMiddle,
    placeWorkCoord,frameWork]

theorem initialBaseWork_prefix (n d r : Nat) (base : List Bool)
    (i : Fin (n+24)) (hi : i.val < n) :
    initialBaseWork n d r base i = regTape 0 := by
  simp [initialBaseWork,placedClockWork,placeWorkInMiddle,show ¬n ≤ i.val by omega]

def initialBaseTM (n : Nat) (hn : 6 ≤ n) : TM (n+24) :=
  seqTM bumpTM (seqTM (placeWorkTM n 0 storedBaseBlockTM)
    (copyParkedBufferTM (initialBaseSource n) (initialBaseDest n hn)))

/-- Original encoded input to its persistent chemistry bank, with all heads and
the retained base scratch specified. No prepared input is assumed. -/
theorem initialBaseTM_correct {d r : Nat} (n : Nat) (hn : 6 ≤ n)
    (Q : CRS (Fin d) (Fin r)) (C : Catalysis (Fin d) (Fin r)) [DecidableRel C] :
    (initialBaseTM n hn).HoareTime
      (fun inp work out =>
        inp = Tape.init ((inputBits Q C (Equiv.refl _) (Equiv.refl _)).map Γ.ofBool) ∧
        (∀ i, work i = Tape.init []) ∧ out = Tape.init [])
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (Function.update (initialBaseWork n d r (SAT.CNF.encode (assembledBase Q C)))
          (initialBaseDest n hn) (parkedInput (SAT.CNF.encode (assembledBase Q C)))) [])
      (50000000*((inputBits Q C (Equiv.refl _) (Equiv.refl _)).length+1)^6+16) := by
  let z := inputBits Q C (Equiv.refl _) (Equiv.refl _)
  let base := SAT.CNF.encode (assembledBase Q C)
  have hp := parkedInput_parked z
  have hzero : accumulatorTape [] = regTape 0 := reg_zero_init_bumped.eq_regT
  have h₁ := redirectEmitter_correct _ _ _ _ _ _ _ _ (parkedBaseCompiler_correct Q C)
  have hw : ∀ i, Parked (frameWork (m := 1) (baseRegWork (baseRunState d r 6))
      (fun _ => accumulatorTape base) i) := by
    intro i
    unfold frameWork
    split
    · exact parked_regTape _
    · exact (accumulatorTape_outAcc base).parked
  have h₂ := rewindQuery_correct (baseRegWork (baseRunState d r 6))
    (parkedInput z) base hp (fun _ => parked_regTape _)
  have hb := seqTM_hoareTime _ _ h₁ (emitPred_transition hp hw []) h₂
  have hplace := placeEmitter_correct storedBaseBlockTM n 0 (fun _ => regTape 0)
    (fun _ _ => parked_regTape _) _ _ _ _ _ _ _ hb
  have he : placedClockWork n 0 (fun _ => regTape 0)
      (frameWork (m := 1) (fun _ : Fin 23 => regTape 0)
        (fun _ => accumulatorTape [])) = fun _ => regTape 0 := by
    funext i
    simp [placedClockWork,frameWork,hzero]
  rw [he] at hplace
  have hne : initialBaseSource n ≠ initialBaseDest n hn := by
    intro h
    have := congrArg Fin.val h
    simp only [initialBaseSource,initialBaseDest] at this
    omega
  have hc := copyParkedBuffer_correct (initialBaseSource n) (initialBaseDest n hn) hne
    base (parkedInput z) (initialBaseWork n d r base) hp
    (initialBaseWork_parked n d r base) (initialBaseWork_source n d r base)
    (initialBaseWork_prefix n d r base _ (by dsimp [initialBaseDest]; omega))
  have htail := seqTM_hoareTime _ _ hplace
    (emitPred_transition hp (initialBaseWork_parked n d r base) []) hc
  have hbump : (bumpTM (n := n+24)).HoareTime _
      (EmitPred (parkedInput z) (fun _ => regTape 0) []) 1 :=
    (bumpTM_hoareTime z).strengthen_post (by
      rintro inp work out ⟨hi,hw,ho⟩
      exact ⟨hi,funext (fun i => (hw i).eq_regT),ho⟩)
  have h := seqTM_hoareTime _ _ hbump
    (emitPred_transition hp (fun _ => parked_regTape _) []) htail
  apply h.mono_bound
  have ht := baseCompilerTime_le z.length
  have hl := assembledBase_encode_length_le Q C
  change 1+1+(baseCompilerTime z.length+1+(base.length+3)+1+(3*base.length+9)) ≤ _
  dsimp [base,z] at *
  omega

end IrrRAFEnumeration.CompletionQuery

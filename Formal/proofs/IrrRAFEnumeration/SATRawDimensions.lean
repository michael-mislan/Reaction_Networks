import proofs.IrrRAFEnumeration.SATClauseCountRegister
import proofs.Complexitylib.Models.TuringMachine.Registers.InputLen

namespace IrrRAFEnumeration.SATSource

open Complexity SAT Complexity.TM

/-- Source length plus two, with every phase boundary charged. -/
def rawLengthPadTM : TM 2 :=
  seqTM (inputLenRegTM 1) (seqTM (incRegTM 1) (incRegTM 1))

theorem rawLengthPadTM_correct (z : List Bool) (work : Fin 2 → Tape)
    (hw : ∀ i, Parked (work i)) (hz : work 1 = regTape 0) :
    rawLengthPadTM.HoareTime
      (EmitPred ⟨1, (Tape.init (z.map Γ.ofBool)).cells⟩ work [])
      (EmitPred ⟨1, (Tape.init (z.map Γ.ofBool)).cells⟩
        (Function.update work 1 (regTape (z.length+2))) []) (6*z.length+16) := by
  let inp : Tape := ⟨1, (Tape.init (z.map Γ.ofBool)).cells⟩
  have hip : Parked inp := ⟨by rfl, Tape.init_ofBool_cells_ne_start z⟩
  have hwp (v : Nat) : ∀ i, Parked (Function.update work 1 (regTape v) i) := by
    intro i
    by_cases hi : i = 1
    · subst i; simp only [Function.update_self]; exact parked_regTape _
    · rw [Function.update_of_ne hi]; exact hw i
  have hlen := inputLenRegTM_hoareTime (1 : Fin 2) z work [] (fun i _ => hw i) hz
  have hinc (v : Nat) := incRegTM_hoareTime (1 : Fin 2) v inp
    (Function.update work 1 (regTape v)) [] hip (fun i _ => hwp v i)
    (Function.update_self ..)
  have h₁ := hinc z.length
  have h₂ := hinc (z.length+1)
  simp only [Function.update_idem] at h₁ h₂
  have htail := seqTM_hoareTime _ _ h₁ (emitPred_transition hip (hwp _) []) h₂
  have hall := seqTM_hoareTime _ _ hlen (emitPred_transition hip (hwp _) []) htail
  exact hall.mono_bound (by omega)

/-- Raw SAT dimension preparation on two work tapes. Tape 0 contains the
clause count; tape 1 contains the padded variable dimension. -/
def rawDimensionsTM : TM 2 :=
  seqTM (clauseCountRegisterTM.liftTM 1) rawLengthPadTM

theorem rawDimensionsTM_correct (z : List Bool) :
    ∃ c t, t ≤ 9*z.length+27 ∧
      rawDimensionsTM.reachesIn t (rawDimensionsTM.initCfg z) c ∧
      rawDimensionsTM.halted c ∧
      c.work 0 = regTape (clauseMarks none z).length ∧
      c.work 1 = regTape (z.length+2) ∧
      c.input = ⟨1, (Tape.init (z.map Γ.ofBool)).cells⟩ ∧ OutAcc [] c.output := by
  obtain ⟨c₀,t₀,ht₀,hr₀,hh₀,hw₀,hc₀,hp₀,ho₀⟩ := clauseCountRegisterTM_correct z
  have hpos : 0 < t₀ := by
    cases hr₀ with
    | zero =>
      simp [clauseCountRegisterTM, seqTM, TM.halted, Cfg.isHalted] at hh₀
    | step => omega
  let c₁ := clauseCountRegisterTM.liftCfg 1 c₀
  have hr₁ := liftTM_reachesIn_initCfg_of_pos clauseCountRegisterTM 1 z hpos hr₀
  change (clauseCountRegisterTM.liftTM 1).reachesIn t₀
    ((clauseCountRegisterTM.liftTM 1).initCfg z) c₁ at hr₁
  have hh₁ : (clauseCountRegisterTM.liftTM 1).halted c₁ := hh₀
  have h0 : c₁.work 0 = regTape (clauseMarks none z).length := by
    exact hw₀
  have h1 : c₁.work 1 = regTape 0 := by
    apply Tape.ext
    · rfl
    · funext j
      by_cases hj : j = 0 <;> simp [c₁, liftCfg, regCells, Tape.init, Tape.move, hj]
  have hi : c₁.input = ⟨1, (Tape.init (z.map Γ.ofBool)).cells⟩ := Tape.ext hp₀ hc₀
  have hip : Parked c₁.input := by
    rw [hi]; exact ⟨by rfl, Tape.init_ofBool_cells_ne_start z⟩
  have hwp : ∀ i, Parked (c₁.work i) := by
    intro i
    fin_cases i
    · change Parked (c₁.work 0)
      rw [h0]; exact parked_regTape _
    · change Parked (c₁.work 1)
      rw [h1]; exact parked_regTape _
  have ho₁ : OutAcc [] c₁.output := ho₀
  obtain ⟨c₂,t₂,ht₂,hr₂,hh₂,hi₂,hw₂,ho₂⟩ :=
    rawLengthPadTM_correct z c₁.work hwp h1 c₁.input c₁.work c₁.output ⟨hi,rfl,ho₀⟩
  have htrans : (fun i => transitionTape (c₁.work i)) = c₁.work :=
    funext fun i => (hwp i).transitionTape_eq_self
  have hrun := seqTM_reachesIn_of_reachesIn (clauseCountRegisterTM.liftTM 1)
    rawLengthPadTM hr₁ hh₁ (by
      simpa only [hip.transitionInput_eq_self, htrans, ho₁.parked.transitionTape_eq_self]
        using hr₂)
  refine ⟨phase2Wrap (clauseCountRegisterTM.liftTM 1) rawLengthPadTM c₂,
    t₀+1+t₂, by omega, hrun, ?_, ?_, ?_, hi₂, ho₂⟩
  · exact (phase2Wrap_halted_iff _ _ _).mpr hh₂
  · change c₂.work 0 = _
    rw [hw₂, Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1), h0]
  · change c₂.work 1 = _
    rw [hw₂, Function.update_self]

theorem rawDimensionsTM_encode_correct (φ : CNF) :
    ∃ c t, t ≤ 9*φ.encode.length+27 ∧
      rawDimensionsTM.reachesIn t (rawDimensionsTM.initCfg φ.encode) c ∧
      rawDimensionsTM.halted c ∧ c.work 0 = regTape φ.length ∧
      c.work 1 = regTape (φ.encode.length+2) ∧
      c.input = ⟨1, (Tape.init (φ.encode.map Γ.ofBool)).cells⟩ ∧ OutAcc [] c.output := by
  simpa [clauseMarks_encode] using rawDimensionsTM_correct φ.encode

end IrrRAFEnumeration.SATSource

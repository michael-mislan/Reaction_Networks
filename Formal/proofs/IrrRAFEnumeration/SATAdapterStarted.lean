import proofs.IrrRAFEnumeration.SATAdapterBranch

namespace IrrRAFEnumeration.SATSource
open Complexity SAT Complexity.TM DeadlineFirstEntry

def startedRectangleTM : TM 4 :=
  { rawRectangleCompilerTM with qstart := firstState rawRectangleCompilerTM }

theorem startedRectangle_run {t : Nat} {c d : Cfg 4 rawRectangleCompilerTM.Q}
    (hr : rawRectangleCompilerTM.reachesIn t c d) : startedRectangleTM.reachesIn t c d := by
  induction hr with
  | zero => exact .zero
  | step hs _ ih => exact .step hs ih

theorem startedRectangleTM_correct (φ : CNF) :
    startedRectangleTM.HoareTime
      (EmitPred ⟨1,(Tape.init (φ.encode.map Γ.ofBool)).cells⟩ (fun _ => regTape 0) [])
      (fun _ _ out => out.HasOutput (libraryRectangle φ) ∧ out.StartInvariant)
      (1000*(φ.encode.length+2)^3) := by
  rintro inp work out ⟨rfl,rfl,hout⟩
  have hoeq := hout.eq outAcc_nil_init
  have hne : rawRectangleCompilerTM.qstart ≠ rawRectangleCompilerTM.qhalt := by
    intro h; cases h
  obtain ⟨c,t,ht,hr,hh,ho⟩ := rawRectangleCompilerTM_correct φ
  have hn : t ≠ 0 := by
    intro he
    subst t
    cases hr
    exact hne hh
  obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have htail := startedRectangle_run (positive_run_tail rawRectangleCompilerTM hne φ.encode hr)
  have hw : (fun _ : Fin 4 => regTape 0) = (firstCfg rawRectangleCompilerTM φ.encode).work :=
    funext (fun _ => reg_zero_init_bumped.eq_regT.symm)
  have hstart : ({
      state := startedRectangleTM.qstart
      input := ⟨1,(Tape.init (φ.encode.map Γ.ofBool)).cells⟩
      work := fun _ => regTape 0
      output := out } : Cfg 4 startedRectangleTM.Q) =
      firstCfg rawRectangleCompilerTM φ.encode := Cfg.ext rfl rfl hw hoeq
  refine ⟨c,s,by omega,hstart ▸ htail,hh,ho,?_,?_⟩
  · exact output_cells_zero_eq_start_of_reachesIn hr rfl
  · exact output_cells_ne_start_of_reachesIn hr Tape.StartInvariant.init_nil.2

def validAdapterBranchTM : TM 4 := seqTM branchPrepareTM startedRectangleTM

theorem validAdapterBranchTM_correct (φ : CNF) :
    validAdapterBranchTM.HoareTime
      (fun inp work out => inp.cells = (Tape.init (φ.encode.map Γ.ofBool)).cells ∧
        inp.head = φ.encode.length+1 ∧ work = (fun _ => regTape 0) ∧ out = syntaxVerdict true)
      (fun _ _ out => out.HasOutput (libraryRectangle φ) ∧ out.StartInvariant)
      (φ.encode.length+6+1000*(φ.encode.length+2)^3) := by
  have h := seqTM_hoareTime _ _ (branchPrepareTM_correct φ.encode true)
    (emitPred_transition (parked_init_input φ.encode) (fun _ => parked_regTape 0) [])
    (startedRectangleTM_correct φ)
  exact h.mono_bound (by omega)

end IrrRAFEnumeration.SATSource

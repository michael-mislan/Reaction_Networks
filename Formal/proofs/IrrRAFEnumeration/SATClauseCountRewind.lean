import proofs.IrrRAFEnumeration.SATClauseCount
import proofs.Complexitylib.Models.TuringMachine.Subroutines.Internal

namespace IrrRAFEnumeration.SATSource

open Complexity SAT Complexity.TM

/-- Count clauses, then restore the raw source head for subsequent queries. -/
def clauseCountRewindTM : TM 0 := seqTM clauseCountTM rewindInputTM

theorem clauseCountRewindTM_correct (z : List Bool) :
    ∃ c t, t ≤ 2*z.length+6 ∧
      clauseCountRewindTM.reachesIn t (clauseCountRewindTM.initCfg z) c ∧
      clauseCountRewindTM.halted c ∧ OutAcc (clauseMarks none z) c.output ∧
      c.input.cells = (Tape.init (z.map Γ.ofBool)).cells ∧ c.input.head = 1 := by
  obtain ⟨c₁, hr₁, hh₁, ho₁, hc₁, hp₁⟩ := clauseCountTM_correct z
  have hzero : c₁.input.cells 0 = Γ.start := by rw [hc₁]; simp [Tape.init]
  have hnostart : ∀ j, 1 ≤ j → c₁.input.cells j ≠ Γ.start := by
    intro j hj
    rw [hc₁]
    exact Tape.init_ofBool_cells_ne_start z j hj
  have hipark : Parked c₁.input := ⟨by rw [hp₁]; omega, hnostart⟩
  let P : Tape → (Fin 0 → Tape) → Tape → Prop := fun inp _ out =>
    inp.cells = (Tape.init (z.map Γ.ofBool)).cells ∧ OutAcc (clauseMarks none z) out
  have hrew := rewindInputTM_hoareTime_frame (n := 0) (z.length+1) (P := P)
    (by
      intro inp work out inp' work' out' hP hc _ _ ho
      exact ⟨hc.trans hP.1, ho ▸ hP.2⟩)
  obtain ⟨c₂, t, ht, hr₂, hh₂, hp₂, hc₂, ho₂⟩ :=
    hrew c₁.input c₁.work c₁.output
      ⟨hzero, hnostart, by rw [hp₁], ho₁.parked.read_ne_start, ho₁.parked.1,
        fun i => Fin.elim0 i, hc₁, ho₁⟩
  have hw : (fun i => transitionTape (c₁.work i)) = c₁.work := Subsingleton.elim _ _
  have hrun := seqTM_reachesIn_of_reachesIn clauseCountTM (rewindInputTM (n := 0))
    hr₁ hh₁ (by
      simpa only [hipark.transitionInput_eq_self, ho₁.parked.transitionTape_eq_self, hw]
        using hr₂)
  refine ⟨phase2Wrap clauseCountTM rewindInputTM c₂, z.length+2+1+t,
    by omega, hrun, ?_, ho₂, hc₂, hp₂⟩
  exact (phase2Wrap_halted_iff clauseCountTM rewindInputTM c₂).mpr hh₂

theorem clauseCountRewindTM_encode_correct (φ : CNF) :
    ∃ c t, t ≤ 2*φ.encode.length+6 ∧
      clauseCountRewindTM.reachesIn t (clauseCountRewindTM.initCfg φ.encode) c ∧
      clauseCountRewindTM.halted c ∧ OutAcc (List.replicate φ.length true) c.output ∧
      c.input.cells = (Tape.init (φ.encode.map Γ.ofBool)).cells ∧ c.input.head = 1 := by
  simpa [clauseMarks_encode] using clauseCountRewindTM_correct φ.encode

end IrrRAFEnumeration.SATSource

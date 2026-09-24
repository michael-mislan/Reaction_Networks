import proofs.IrrRAFEnumeration.SATClauseCountRewind
import proofs.Complexitylib.Models.TuringMachine.Lift

namespace IrrRAFEnumeration.SATSource

open Complexity SAT Complexity.TM

theorem clauseMarks_length_le (p : Option Bool) (z : List Bool) :
    (clauseMarks p z).length ≤ z.length := by
  induction z generalizing p with
  | nil => simp [clauseMarks]
  | cons b bs ih =>
    simp only [clauseMarks]
    split <;> simp only [List.length_cons]
    · exact Nat.succ_le_succ (ih _)
    · exact (ih _).trans (Nat.le_succ _)

theorem clauseMarks_eq_replicate (p : Option Bool) (z : List Bool) :
    clauseMarks p z = List.replicate (clauseMarks p z).length true := by
  induction z generalizing p with
  | nil => rfl
  | cons b bs ih =>
    simp only [clauseMarks]
    split
    · simpa only [List.length_cons, List.replicate_succ] using congrArg (List.cons true) (ih _)
    · exact ih _

def clauseCountRetargetTM : TM 1 := clauseCountRewindTM.retargetOutput

theorem clauseCountRetarget_init_step (z : List Bool) :
    clauseCountRetargetTM.step (clauseCountRetargetTM.initCfg z) = some
      (clauseCountRewindTM.retargetCfg
        (phase1Wrap clauseCountTM rewindInputTM
          (clauseCountCfg none ((Tape.init (z.map Γ.ofBool)).move .right)
            ((Tape.init []).move .right)))) := by
  simp [TM.step, clauseCountRetargetTM, retargetOutput, clauseCountRewindTM, seqTM,
    clauseCountTM, retargetCfg, phase1Wrap, clauseCountCfg, allIdle,
    Tape.read, Tape.writeAndMove, Tape.write, Tape.move, Tape.init, idleDir]

/-- The entire source-preserving count run is redirected to a work tape,
with the full source and real-output frame retained. -/
theorem clauseCountRetarget_correct (z : List Bool) :
    ∃ c t, t ≤ 2*z.length+6 ∧
      clauseCountRetargetTM.reachesIn t (clauseCountRetargetTM.initCfg z) c ∧
      clauseCountRetargetTM.halted c ∧ OutAcc (clauseMarks none z) (c.work 0) ∧
      c.input.cells = (Tape.init (z.map Γ.ofBool)).cells ∧ c.input.head = 1 ∧
      OutAcc [] c.output := by
  obtain ⟨c, t, ht, hr, hh, ho, hc, hp⟩ := clauseCountRewindTM_correct z
  cases hr with
  | zero =>
    have : ¬ clauseCountRewindTM.halted (clauseCountRewindTM.initCfg z) := by
      simp [clauseCountRewindTM, seqTM, TM.halted, Cfg.isHalted]
    exact False.elim (this hh)
  | @step _ cnext t cend hs htail =>
    have hfirst := seqTM_phase1_step clauseCountTM (rewindInputTM (n := 0))
      (clauseCountTM_init_step z)
    have he : cnext = phase1Wrap clauseCountTM rewindInputTM
        (clauseCountCfg none ((Tape.init (z.map Γ.ofBool)).move .right)
          ((Tape.init []).move .right)) := Option.some.inj (hs.symm.trans hfirst)
    subst cnext
    have hret := retargetOutput_reachesIn_retargetCfg_frame clauseCountRewindTM htail
    refine ⟨_, t+1, ht,
      .step (clauseCountRetarget_init_step z) hret, hh, ?_, hc, hp, outAcc_nil_init⟩
    simpa only [retargetCfg, Nat.not_lt_zero, ↓reduceDIte] using ho

/-- Actual initialization: unary clause count in register 0, original source
restored, and real output empty. -/
def clauseCountRegisterTM : TM 1 :=
  seqTM clauseCountRetargetTM (rewindWorkTM 0)

theorem clauseCountRegisterTM_correct (z : List Bool) :
    ∃ c t, t ≤ 3*z.length+10 ∧
      clauseCountRegisterTM.reachesIn t (clauseCountRegisterTM.initCfg z) c ∧
      clauseCountRegisterTM.halted c ∧ c.work 0 = regTape (clauseMarks none z).length ∧
      c.input.cells = (Tape.init (z.map Γ.ofBool)).cells ∧ c.input.head = 1 ∧
      OutAcc [] c.output := by
  obtain ⟨c₁, t₁, ht₁, hr₁, hh₁, hcount, hc₁, hp₁, ho₁⟩ := clauseCountRetarget_correct z
  have hip : Parked c₁.input := by
    refine ⟨by rw [hp₁], ?_⟩
    intro j hj
    rw [hc₁]
    exact Tape.init_ofBool_cells_ne_start z j hj
  have hwp : ∀ i, Parked (c₁.work i) := by
    intro i
    have he : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    exact hcount.parked
  let P : Tape → (Fin 1 → Tape) → Tape → Prop := fun inp work out =>
    inp = c₁.input ∧ (work 0).cells = (c₁.work 0).cells ∧ OutAcc [] out
  have hrew := rewindWorkTM_hoareTime_frame (0 : Fin 1)
    ((clauseMarks none z).length+1) (P := P) (by
      intro inp work out inp' work' out' hP hc _ _ hi hoc hoh
      exact ⟨hi.trans hP.1, hc.trans hP.2.1, (Tape.ext hoh hoc) ▸ hP.2.2⟩)
  obtain ⟨c₂, t₂, ht₂, hr₂, hh₂, hhead, hi₂, hcells, ho₂⟩ :=
    hrew c₁.input c₁.work c₁.output
      ⟨hcount.2.1, hcount.parked.2, by rw [hcount.head_eq], hip.read_ne_start,
        ho₁.parked.read_ne_start, ho₁.parked.1, fun i _ =>
          ⟨(hwp i).read_ne_start, (hwp i).1⟩, rfl, rfl, ho₁⟩
  have hreg : IsReg (clauseMarks none z).length (c₂.work 0) := by
    refine ⟨hhead, ?_, ?_, ?_⟩
    · rw [hcells]; exact hcount.2.1
    · intro i hi
      rw [hcells, hcount.2.2.1 i hi]
      have hv : (clauseMarks none z)[i] = true := by
        have hm := List.getElem_mem hi
        have hm' := (congrArg (fun xs => (clauseMarks none z)[i] ∈ xs)
          (clauseMarks_eq_replicate none z)).mp hm
        exact (List.mem_replicate.mp hm').2
      simp [hv, Γ.ofBool]
    · intro j hj
      rw [hcells]
      exact hcount.2.2.2 j hj
  have hw : (fun i => transitionTape (c₁.work i)) = c₁.work :=
    funext fun i => (hwp i).transitionTape_eq_self
  have hrun := seqTM_reachesIn_of_reachesIn clauseCountRetargetTM (rewindWorkTM 0)
    hr₁ hh₁ (by
      simpa only [hip.transitionInput_eq_self, hw, ho₁.parked.transitionTape_eq_self] using hr₂)
  refine ⟨phase2Wrap clauseCountRetargetTM (rewindWorkTM 0) c₂, t₁+1+t₂,
    ?_, hrun, ?_, hreg.eq_regT, ?_, ?_, ho₂⟩
  · have hl := clauseMarks_length_le none z
    omega
  · exact (phase2Wrap_halted_iff clauseCountRetargetTM (rewindWorkTM 0) c₂).mpr hh₂
  · exact congrArg Tape.cells hi₂ |>.trans hc₁
  · exact congrArg Tape.head hi₂ |>.trans hp₁

theorem clauseCountRegisterTM_encode_correct (φ : CNF) :
    ∃ c t, t ≤ 3*φ.encode.length+10 ∧
      clauseCountRegisterTM.reachesIn t (clauseCountRegisterTM.initCfg φ.encode) c ∧
      clauseCountRegisterTM.halted c ∧ c.work 0 = regTape φ.length ∧
      c.input.cells = (Tape.init (φ.encode.map Γ.ofBool)).cells ∧ c.input.head = 1 ∧
      OutAcc [] c.output := by
  simpa [clauseMarks_encode] using clauseCountRegisterTM_correct φ.encode

end IrrRAFEnumeration.SATSource

import proofs.IrrRAFEnumeration.CompletionClockedSAT

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM PolynomialClockSetup

/-- Redirect arbitrary decision output, retaining the full exit contract. -/
theorem redirectDecision_correct {n : Nat} (M : TM n)
    (inp : Tape) (work : Fin n → Tape) (P : TM.TapePred n) (b : Nat)
    (h : M.HoareTime (EmitPred inp work []) P b) :
    M.retargetOutput.HoareTime
      (EmitPred inp (frameWork (m := 1) work (fun _ => accumulatorTape [])) [])
      (fun a w out => ∃ inner : Fin n → Tape, ∃ verdict : Tape,
        w = frameWork (m := 1) inner (fun _ => verdict) ∧
        P a inner verdict ∧ OutAcc [] out) b := by
  rintro a w out ⟨ha,hw,ho⟩
  subst a
  subst w
  have he : out = (Tape.init []).move Dir3.right := ho.eq outAcc_nil_init
  subst out
  obtain ⟨c,t,ht,hr,hh,hpost⟩ := h inp work (accumulatorTape [])
    ⟨rfl,rfl,accumulatorTape_outAcc []⟩
  have hrun := retargetOutput_reachesIn_retargetCfg_frame M hr
  exact ⟨M.retargetCfg c,t,ht,hrun,hh,c.work,c.output,rfl,hpost,outAcc_nil_init⟩

def bufferedCompletionTM {k : Nat} (q : Polynomial Nat) (M : TM k) :=
  (clockedCompletionTM q M).retargetOutput

/-- The full clocked SAT call writes into work scratch, preserving external output.
Its verdict, sentinel invariants and SAT-phase footprint remain available to reset. -/
theorem bufferedCompletionTM_correct {d r k : Nat} (q : Polynomial Nat)
    (Q : CRS (Fin d) (Fin r)) (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r))
    (M : TM k) (T : Nat → Nat) (hM : M.DecidesInTime SAT.language T)
    (inp : Tape) (hp : Parked inp) :
    let base := SAT.CNF.encode (assembledBase Q C)
    let blocks := SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)
    let query := SAT.CNF.encode (assembledBase Q C ++ PositiveCompletionCNF.outputBlockers G ++
      PositiveCompletionCNF.containerExclusions U)
    (bufferedCompletionTM q M).HoareTime
      (EmitPred inp (frameWork (m := 1) (queryDecisionWork (3+k) U 1 0 base blocks [])
        (fun _ => accumulatorTape [])) [])
      (fun a w out => ∃ inner : Fin (7+(3+k)+1) → Tape, ∃ verdict : Tape,
        w = frameWork (m := 1) inner (fun _ => verdict) ∧
        clockedSATPost q k U base blocks query inp (T query.length+query.length+2)
          (PositiveCompletion.Available (IsRAF Q C) G.toFinset U) a inner verdict ∧
        OutAcc [] out)
      (dynamicQueryTime base.length blocks.length r+query.length+6+
        setupTime q query.length+T query.length) := by
  dsimp only
  exact redirectDecision_correct _ _ _ _ _ (clockedCompletionTM_correct q Q C G U M T hM inp hp)

end IrrRAFEnumeration.CompletionQuery

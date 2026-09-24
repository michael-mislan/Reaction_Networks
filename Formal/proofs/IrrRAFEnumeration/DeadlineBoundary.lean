import proofs.IrrRAFEnumeration.InitializedDeadline

namespace IrrRAFEnumeration.DeadlineBoundary
open Complexity Complexity.TM DeadlineMachine PolynomialClockSetup DeadlineFirstEntry InitializedDeadline
variable {n : Nat}

theorem parked_transition (t : Tape) (h : t.StartInvariant) : Parked (transitionTape t) := by
  refine ⟨one_le_head_transitionTape t h.1,?_⟩
  intro j hj
  rw [transitionTape_cells t h.2]
  exact h.2 j hj

theorem parked_input_transition (t : Tape) (h : t.StartInvariant) : Parked (transitionInput t) :=
  ⟨transitionInput_head_ge t h.1,by simpa only [transitionInput_cells] using h.2⟩

theorem clock_invariant (budget elapsed : Nat) : (clockTape budget elapsed).StartInvariant := by
  refine ⟨rfl,?_⟩
  intro j hj
  simp only [clockTape,show j ≠ 0 from by omega,↓reduceIte]
  split <;> decide

theorem finishCfg_parked (tm : TM n) (c : Cfg n tm.Q) (success : Bool) (budget elapsed : Nat)
    (hi : c.input.StartInvariant) (hw : ∀ i, (c.work i).StartInvariant)
    (ho : c.output.StartInvariant) :
    Parked (finishCfg tm success c (clockTape budget elapsed)).input ∧
      (∀ i, Parked ((finishCfg tm success c (clockTape budget elapsed)).work i)) ∧
      Parked (finishCfg tm success c (clockTape budget elapsed)).output := by
  refine ⟨parked_input_transition c.input hi,?_,parked_transition c.output ho⟩
  intro i
  dsimp only [finishCfg]
  split
  · exact parked_transition _ (hw _)
  · have hinv := (clock_invariant budget elapsed).writeAndMove (Γw.ofBool success)
      (idleDir (clockTape budget elapsed).read)
    refine ⟨?_,hinv.2⟩
    have hn : (clockTape budget elapsed).read ≠ Γ.start := by
      rw [clockTape_read]
      split <;> decide
    rw [idleDir,if_neg hn]
    change 1 ≤ elapsed+1
    omega

theorem run_invariants (tm : TM n) {c d : Cfg n tm.Q} {t : Nat} (hr : tm.reachesIn t c d)
    (hi : c.input.StartInvariant) (hw : ∀ i, (c.work i).StartInvariant)
    (ho : c.output.StartInvariant) :
    d.input.StartInvariant ∧ (∀ i, (d.work i).StartInvariant) ∧ d.output.StartInvariant := by
  induction hr with
  | zero => exact ⟨hi,hw,ho⟩
  | step hs _ ih =>
    obtain ⟨hi',hw',ho'⟩ := Tape.StartInvariant.step tm hs hi hw ho
    exact ih hi' hw' ho'

theorem framed_invariants (tm : TM n) (p : Polynomial Nat) (x : List Bool) (d : Cfg n tm.Q)
    (hi : d.input.StartInvariant) (hw : ∀ i, (d.work i).StartInvariant)
    (ho : d.output.StartInvariant) :
    (framedSourceCfg tm p x d).input.StartInvariant ∧
      (∀ i, ((framedSourceCfg tm p x d).work i).StartInvariant) ∧
      (framedSourceCfg tm p x d).output.StartInvariant := by
  refine ⟨hi,?_,ho⟩
  intro i
  dsimp only [framedSourceCfg]
  split
  · exact hw _
  · unfold sourceFrame
    split <;> exact ⟨rfl,(parked_regTape _).2⟩

def completedCfg (tm : TM n) (p : Polynomial Nat) (x : List Bool)
    (d : Cfg n tm.Q) (t : Nat) (b : Bool) :=
  phase2Wrap (placeWorkTM n 0 (setupTM p)) (entryTM tm)
    (finishCfg (tm.liftTM 2) b (framedSourceCfg tm p x d) (clockTape (p.eval x.length) t))

theorem completedCfg_length_register (tm : TM n) (p : Polynomial Nat) (x : List Bool)
    (d : Cfg n tm.Q) (t : Nat) (b : Bool) :
    (completedCfg tm p x d t b).work ⟨n,by omega⟩ = regTape x.length := by
  simp only [completedCfg,phase2Wrap,finishCfg,show n < n+2 by omega,↓reduceDIte,
    framedSourceCfg,Nat.lt_irrefl,sourceFrame,↓reduceIte]
  exact (parked_regTape _).writeAndMove_readBack_idle

/-- The bounded simulator's actual final boundary, with parked tapes and the
preserved input-length register needed by source-specific header comparison. -/
theorem initialized_boundary (tm : TM n) (hne : tm.qstart ≠ tm.qhalt)
    (p : Polynomial Nat) (x : List Bool) :
    ∃ d t s b,
      t ≤ p.eval x.length ∧ s ≤ setupTime p x.length+p.eval x.length+2 ∧
      tm.reachesIn (t+1) (tm.initCfg x) d ∧
      (initializedTM tm p).reachesIn s ((initializedTM tm p).initCfg x) (completedCfg tm p x d t b) ∧
      (initializedTM tm p).halted (completedCfg tm p x d t b) ∧
      (b = true ↔ ∃ e u, u ≤ p.eval x.length+1 ∧ tm.reachesIn u (tm.initCfg x) e ∧ e.state = tm.qhalt) ∧
      ((completedCfg tm p x d t b).work (Fin.last (n+2))).read = Γ.ofBool b ∧
      (completedCfg tm p x d t b).output.cells = d.output.cells ∧
      Parked (completedCfg tm p x d t b).input ∧
      (∀ i, Parked ((completedCfg tm p x d t b).work i)) ∧
      Parked (completedCfg tm p x d t b).output ∧
      (b = true ↔ tm.halted d) := by
  obtain ⟨a,s,hs,ha,hh,he⟩ := setup_reaches_ready tm p x
  obtain ⟨d,t,b,ht,hd,hb,hbd,hr⟩ := entry_bounded_full tm hne p x
  have hseq := seqTM_reachesIn_of_reachesIn (placeWorkTM n 0 (setupTM p))
    (entryTM tm) ha hh (he ▸ hr)
  obtain ⟨hi,hw,ho⟩ := run_invariants tm hd (Tape.StartInvariant.init_ofBool x)
    (fun _ => Tape.StartInvariant.init_nil) Tape.StartInvariant.init_nil
  obtain ⟨hi',hw',ho'⟩ := framed_invariants tm p x d hi hw ho
  refine ⟨d,t,s+1+(t+1),b,ht,by omega,hd,hseq,rfl,hb,?_,?_,?_⟩
  · exact finishCfg_flag (tm.liftTM 2) b (framedSourceCfg tm p x d) _ t
  · exact finish_output_preserved (tm.liftTM 2) b (framedSourceCfg tm p x d)
      (clockTape (p.eval x.length) t) ho'
  · obtain ⟨hpi,hpw,hpo⟩ := finishCfg_parked (tm.liftTM 2) _ b _ t hi' hw' ho'
    exact ⟨hpi,hpw,hpo,hbd⟩

end IrrRAFEnumeration.DeadlineBoundary

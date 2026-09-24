import proofs.IrrRAFEnumeration.DeadlineFirstEntry

namespace IrrRAFEnumeration.InitializedDeadline
open Complexity Complexity.TM DeadlineMachine PolynomialClockSetup DeadlineFirstEntry
variable {n : Nat}

def entryTM (tm : TM n) : TM (n+3) :=
  { clockTM (tm.liftTM 2) with qstart := some (firstState tm) }

theorem entry_run (tm : TM n) {t : Nat}
    {c d : Cfg (n+3) (clockTM (tm.liftTM 2)).Q}
    (hr : (clockTM (tm.liftTM 2)).reachesIn t c d) :
    (entryTM tm).reachesIn t c d := by
  induction hr with
  | zero => exact .zero
  | step hs _ ih => exact .step hs ih

def initializedTM (tm : TM n) (p : Polynomial Nat) : TM (n+3) :=
  seqTM (placeWorkTM n 0 (setupTM p)) (entryTM tm)

theorem ready_parked (tm : TM n) (p : Polynomial Nat) (x : List Bool) :
    Parked (readyCfg tm p x).input ∧
      (∀ i, Parked ((readyCfg tm p x).work i)) ∧ Parked (readyCfg tm p x).output := by
  refine ⟨parked_init_input x,?_,reg_zero_init_bumped.parked⟩
  intro i
  rw [readyCfg_work]
  dsimp only
  split
  · generalize placeWorkCoord (post := 0) n 3 i _ = j
    fin_cases j <;> exact parked_regTape _
  · exact reg_zero_init_bumped.parked

/-- The genuine initial setup run reaches precisely the prepared source tapes.
The one-step sequence transition preserves these parked tapes. -/
theorem setup_reaches_ready (tm : TM n) (p : Polynomial Nat) (x : List Bool) :
    ∃ c t, t ≤ setupTime p x.length ∧
      (placeWorkTM n 0 (setupTM p)).reachesIn t
        ((placeWorkTM n 0 (setupTM p)).initCfg x) c ∧
      c.state = (placeWorkTM n 0 (setupTM p)).qhalt ∧
      ({ state := (entryTM tm).qstart,
          input := transitionInput c.input,
          work := fun i => transitionTape (c.work i),
          output := transitionTape c.output } : Cfg (n+3) (entryTM tm).Q) =
        readyCfg tm p x := by
  obtain ⟨d,t,ht,hr,hh,hi,hw,ho⟩ := setup_initial_run p x
  obtain ⟨c,hc,hs,_,_,he⟩ := placeWorkTM_reachesIn_init_internal (setupTM p) n 0 x hr
  have ht0 : t ≠ 0 := by
    intro hz
    subst t
    cases hr
    change (setupTM p).qstart = (setupTM p).qhalt at hh
    simp [setupTM,seqTM] at hh
  have heq := he.resolve_left ht0
  subst c
  refine ⟨_,t,ht,hc,hs.trans hh,?_⟩
  have hi' : (placeWorkParkedCfg (setupTM p) n 0 d).input = (readyCfg tm p x).input := hi
  have ho' : (placeWorkParkedCfg (setupTM p) n 0 d).output = (readyCfg tm p x).output := ho
  have hw' : (placeWorkParkedCfg (setupTM p) n 0 d).work = (readyCfg tm p x).work := by
    rw [readyCfg_work]
    simp only [placeWorkParkedCfg,placeWorkCfg,hw]
    rfl
  obtain ⟨hpi,hpw,hpo⟩ := ready_parked tm p x
  simp only [hi',hw',ho',hpi.transitionInput_eq_self,hpo.transitionTape_eq_self]
  have hwt : (fun i => transitionTape ((readyCfg tm p x).work i)) =
      (readyCfg tm p x).work := funext (fun i => (hpw i).transitionTape_eq_self)
  rw [hwt]
  rfl

theorem entry_bounded_full (tm : TM n) (hne : tm.qstart ≠ tm.qhalt)
    (p : Polynomial Nat) (x : List Bool) :
    ∃ d t success, t ≤ p.eval x.length ∧
      tm.reachesIn (t+1) (tm.initCfg x) d ∧
      (success = true ↔ ∃ e s, s ≤ p.eval x.length+1 ∧
        tm.reachesIn s (tm.initCfg x) e ∧ e.state = tm.qhalt) ∧
      (success = true ↔ d.state = tm.qhalt) ∧
      (entryTM tm).reachesIn (t+1) (readyCfg tm p x)
        (finishCfg (tm.liftTM 2) success (framedSourceCfg tm p x d)
          (clockTape (p.eval x.length) t)) := by
  obtain ⟨d,t,ht,hr,he⟩ := prefix_exists tm (p.eval x.length) (firstCfg tm x)
  have hfull : tm.reachesIn (t+1) (tm.initCfg x) d :=
    .step (first_step tm hne x) hr
  have hfr := framed_source_run tm p x hr
  by_cases hh : d.state = tm.qhalt
  · refine ⟨d,t,true,ht,hfull,iff_of_true rfl ⟨d,t+1,by omega,hfull,hh⟩,
      iff_of_true rfl hh,?_⟩
    exact entry_run tm (clock_success_run (tm.liftTM 2) hfr hh _ ht)
  · have heq : t = p.eval x.length := he.resolve_left hh
    subst t
    refine ⟨d,_,false,le_refl _,hfull,?_,iff_of_false (by decide) hh,?_⟩
    · constructor
      · intro hf; cases hf
      · rintro ⟨e,s,hs,hreach,hhalt⟩
        have hle := tm.reachesIn_le_halt hfull hreach hhalt
        have hst : s = p.eval x.length+1 := by omega
        subst s
        have hd := TM.reachesIn_right_unique hfull hreach
        exact False.elim (hh (hd ▸ hhalt))
    · exact entry_run tm (clock_timeout_run (tm.liftTM 2) _ hfr hh)

theorem entry_bounded (tm : TM n) (hne : tm.qstart ≠ tm.qhalt)
    (p : Polynomial Nat) (x : List Bool) :
    ∃ d t success, t ≤ p.eval x.length ∧
      tm.reachesIn (t+1) (tm.initCfg x) d ∧
      (success = true ↔ ∃ e s, s ≤ p.eval x.length+1 ∧
        tm.reachesIn s (tm.initCfg x) e ∧ e.state = tm.qhalt) ∧
      (entryTM tm).reachesIn (t+1) (readyCfg tm p x)
        (finishCfg (tm.liftTM 2) success (framedSourceCfg tm p x d)
          (clockTape (p.eval x.length) t)) := by
  obtain ⟨d,t,b,ht,hr,hb,_,hc⟩ := entry_bounded_full tm hne p x
  exact ⟨d,t,b,ht,hr,hb,hc⟩

/-- A fixed machine initialized from raw input implements a polynomial
deadline, including clock construction. It reports whether the original
machine halted by p(length)+1 and preserves the simulated output cells. -/
theorem initialized_bounded_correct (tm : TM n) (hne : tm.qstart ≠ tm.qhalt)
    (p : Polynomial Nat) (x : List Bool) :
    ∃ c d t s success,
      t ≤ p.eval x.length ∧
      s ≤ setupTime p x.length + p.eval x.length + 2 ∧
      tm.reachesIn (t+1) (tm.initCfg x) d ∧
      (initializedTM tm p).reachesIn s ((initializedTM tm p).initCfg x) c ∧
      (initializedTM tm p).halted c ∧
      (success = true ↔ ∃ e u, u ≤ p.eval x.length+1 ∧
        tm.reachesIn u (tm.initCfg x) e ∧ e.state = tm.qhalt) ∧
      (c.work (Fin.last (n+2))).read = Γ.ofBool success ∧
      c.output.cells = d.output.cells := by
  obtain ⟨a,s,hs,ha,hh,he⟩ := setup_reaches_ready tm p x
  obtain ⟨d,t,b,ht,hd,hb,hr⟩ := entry_bounded tm hne p x
  let z := finishCfg (tm.liftTM 2) b (framedSourceCfg tm p x d)
    (clockTape (p.eval x.length) t)
  have hseq := seqTM_reachesIn_of_reachesIn (placeWorkTM n 0 (setupTM p))
    (entryTM tm) ha hh (he ▸ hr)
  refine ⟨phase2Wrap (placeWorkTM n 0 (setupTM p)) (entryTM tm) z,
    d,t,s+1+(t+1),b,ht,by omega,hd,hseq,rfl,hb,?_,?_⟩
  · exact finishCfg_flag (tm.liftTM 2) b (framedSourceCfg tm p x d) _ t
  · have hinv : d.output.StartInvariant :=
      ⟨output_cells_zero_eq_start_of_reachesIn hd rfl,
        output_cells_ne_start_of_reachesIn hd Tape.StartInvariant.init_nil.2⟩
    exact finish_output_preserved (tm.liftTM 2) b (framedSourceCfg tm p x d)
      (clockTape (p.eval x.length) t) hinv

noncomputable def totalPolynomial (p : Polynomial Nat) : Polynomial Nat :=
  setupPolynomial p + p + Polynomial.C 2

theorem totalPolynomial_eval (p : Polynomial Nat) (x : Nat) :
    (totalPolynomial p).eval x = setupTime p x + p.eval x + 2 := by
  simp only [totalPolynomial,Polynomial.eval_add,Polynomial.eval_C,
    setupTime_eq_polynomial]

end IrrRAFEnumeration.InitializedDeadline

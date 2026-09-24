import proofs.IrrRAFEnumeration.SATRawDimensions
import Mathlib.Tactic.DeriveFintype

namespace IrrRAFEnumeration.SATSource

open Complexity SAT Complexity.TM

/-- Phases 0/1/2/3 mean scan, rewind variable, emit answer, halt. -/
structure RawIncidenceState where
  phase : Fin 4
  pending : Option Bool
  signMatch : Option Bool
  overflow : Bool
  found : Bool
  deriving DecidableEq, Fintype

def incidenceScan (found : Bool) : RawIncidenceState := ⟨0, none, none, false, found⟩
def incidenceAnswer (found : Bool) : RawIncidenceState := ⟨2, none, none, false, found⟩
def incidenceHalt : RawIncidenceState := ⟨3, none, none, false, false⟩

/-- Desired control actions before mandatory sentinel bounces. Query indices
are read from unary work tapes, never stored in the finite state. -/
def incidenceControl (sign : Bool) (q : RawIncidenceState) (ih jh vh : Γ) :
    RawIncidenceState × Dir3 × Dir3 × Dir3 × Option Bool :=
  if q.phase = 1 then
    if vh = Γ.start then (incidenceScan q.found, .stay, .stay, .right, none)
    else (q, .stay, .stay, .left, none)
  else if q.phase = 2 then (incidenceHalt, .stay, .stay, .stay, some q.found)
  else if ih = Γ.blank then (incidenceAnswer q.found, .stay, .stay, .stay, none)
  else
    let b := ih == Γ.one
    match q.pending with
    | none => ({q with pending := some b}, .right, .stay, .stay, none)
    | some a =>
      if jh ≠ Γ.blank then
        (incidenceScan q.found, .right,
          if a && !b then .right else .stay, .stay, none)
      else if a = b then
        match q.signMatch with
        | none => ({q with pending := none, signMatch := some (b == sign)},
            .right, .stay, .stay, none)
        | some _ =>
            ({q with pending := none, overflow := q.overflow || (vh == Γ.blank)},
              .right, .stay, if vh = Γ.one then .right else .stay, none)
      else if a then (incidenceAnswer q.found, .right, .stay, .stay, none)
      else
        (⟨1, none, none, false,
          q.found || (q.signMatch == some true && !q.overflow && vh == Γ.blank)⟩,
          .right, .stay, .left, none)

def incidenceSafeDir (symbol : Γ) (desired : Dir3) : Dir3 :=
  if symbol = Γ.start then .right else desired

/-- Fixed incidence query with parked unary clause and variable query tapes.
Only the answer is written. -/
def rawIncidenceTM (sign : Bool) : TM 2 where
  Q := RawIncidenceState
  qstart := incidenceScan false
  qhalt := incidenceHalt
  δ := fun q ih wh oh =>
    let a := incidenceControl sign q ih (wh 0) (wh 1)
    (a.1, fun i => readBackWrite (wh i),
      match a.2.2.2.2 with
      | none => readBackWrite oh
      | some b => if b then Γw.one else Γw.zero,
      incidenceSafeDir ih a.2.1,
      fun i => incidenceSafeDir (wh i) (if i = 0 then a.2.2.1 else a.2.2.2.1),
      incidenceSafeDir oh (if a.2.2.2.2.isSome then .right else .stay))
  δ_right_of_start := by
    intro q ih wh oh
    exact ⟨by intro h; simp [incidenceSafeDir, h],
      by intro i h; simp [incidenceSafeDir, h],
      by intro h; simp [incidenceSafeDir, h]⟩

theorem incidence_readBack_cells (t : Tape)
    (h : ∀ j, 1 ≤ j → t.cells j ≠ Γ.start) (d : Dir3) :
    (t.writeAndMove (readBackWrite t.read) d).cells = t.cells := by
  by_cases hz : t.head = 0
  · simp [Tape.writeAndMove, Tape.write, hz, Tape.move_cells]
  · rw [writeAndMove_readBack t (h t.head (by omega)), Tape.move_cells]

theorem rawIncidenceTM_step_preserves (sign : Bool)
    {c c' : Cfg 2 (rawIncidenceTM sign).Q}
    (h : ∀ i j, 1 ≤ j → (c.work i).cells j ≠ Γ.start)
    (hs : (rawIncidenceTM sign).step c = some c') :
    c'.input.cells = c.input.cells ∧ ∀ i, (c'.work i).cells = (c.work i).cells := by
  unfold TM.step at hs
  split at hs
  · contradiction
  · cases Option.some.inj hs
    exact ⟨Tape.move_cells _ _, fun i => incidence_readBack_cells _ (h i) _⟩

theorem rawIncidenceTM_run_preserves (sign : Bool)
    {t : Nat} {c c' : Cfg 2 (rawIncidenceTM sign).Q}
    (h : ∀ i j, 1 ≤ j → (c.work i).cells j ≠ Γ.start)
    (hr : (rawIncidenceTM sign).reachesIn t c c') :
    c'.input.cells = c.input.cells ∧ ∀ i, (c'.work i).cells = (c.work i).cells := by
  induction hr with
  | zero => exact ⟨rfl, fun _ => rfl⟩
  | step hs _ ih =>
    obtain ⟨hi, hw⟩ := rawIncidenceTM_step_preserves sign h hs
    have hnext := ih (fun i j hj => by rw [hw i]; exact h i j hj)
    exact ⟨hnext.1.trans hi, fun i => (hnext.2 i).trans (hw i)⟩

def incidenceRewind (found : Bool) : RawIncidenceState := ⟨1, none, none, false, found⟩
def incidenceCfg (q : RawIncidenceState) (inp jt vt out : Tape) :
    Cfg 2 RawIncidenceState := ⟨q, inp, (fun i => if i = 0 then jt else vt), out⟩

theorem incidence_rewind_left (sign found : Bool) (inp jt vt out : Tape)
    (hip : Parked inp) (hjp : Parked jt) (hvp : vt.read ≠ Γ.start) (hop : Parked out) :
    (rawIncidenceTM sign).step (incidenceCfg (incidenceRewind found) inp jt vt out) =
      some (incidenceCfg (incidenceRewind found) inp jt (vt.move .left) out) := by
  simp [TM.step, rawIncidenceTM, incidenceCfg, incidenceRewind, incidenceHalt,
    incidenceControl, incidenceSafeDir, hvp, hip.read_ne_start,
    hop.read_ne_start, Tape.move]
  constructor
  · funext i
    by_cases hi : i = 0
    · simp only [hi, ↓reduceIte, hjp.read_ne_start]
      change jt.writeAndMove (readBackWrite jt.read) .stay = jt
      rw [writeAndMove_readBack jt hjp.read_ne_start]
      rfl
    · simp only [hi, ↓reduceIte, hvp]
      exact writeAndMove_readBack vt hvp .left
  · change out.write (readBackWrite out.read) = out
    exact write_readBack out hop.read_ne_start

theorem incidence_rewind_zero (sign found : Bool) (inp jt out : Tape) (v : Nat)
    (hip : Parked inp) (hjp : Parked jt) (hop : Parked out) :
    (rawIncidenceTM sign).step
      (incidenceCfg (incidenceRewind found) inp jt ⟨0, regCells v⟩ out) =
      some (incidenceCfg (incidenceScan found) inp jt (regTape v) out) := by
  have hv : (⟨0, regCells v⟩ : Tape).read = Γ.start := rfl
  simp [TM.step, rawIncidenceTM, incidenceCfg, incidenceRewind, incidenceHalt,
    incidenceControl, incidenceSafeDir, hv, hip.read_ne_start,
    hop.read_ne_start, Tape.move]
  constructor
  · funext i
    by_cases hi : i = 0
    · simp only [hi, ↓reduceIte, hjp.read_ne_start]
      change jt.writeAndMove (readBackWrite jt.read) .stay = jt
      rw [writeAndMove_readBack jt hjp.read_ne_start]
      rfl
    · simp only [hi, ↓reduceIte, hv]
      rfl
  · change out.write (readBackWrite out.read) = out
    exact write_readBack out hop.read_ne_start

/-- Reset cost depends on the visited prefix, not the whole query length. -/
theorem incidence_rewind_run (sign found : Bool) (inp jt out : Tape) (v h : Nat)
    (hip : Parked inp) (hjp : Parked jt) (hop : Parked out) :
    (rawIncidenceTM sign).reachesIn (h+1)
      (incidenceCfg (incidenceRewind found) inp jt ⟨h, regCells v⟩ out)
      (incidenceCfg (incidenceScan found) inp jt (regTape v) out) := by
  induction h with
  | zero => exact .step (incidence_rewind_zero sign found inp jt out v hip hjp hop) .zero
  | succ h ih =>
    have hns : (⟨h+1, regCells v⟩ : Tape).read ≠ Γ.start := by
      simp [Tape.read, regCells]
      split <;> decide
    exact .step (incidence_rewind_left sign found inp jt ⟨h+1, regCells v⟩ out
      hip hjp hns hop) ih

end IrrRAFEnumeration.SATSource

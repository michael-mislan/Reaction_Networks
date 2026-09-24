import proofs.IrrRAFEnumeration.SATSyntaxMachine
import proofs.Complexitylib.Models.TuringMachine.Registers.Emit

namespace IrrRAFEnumeration.SATSource

open Complexity SAT Complexity.TM

def clauseHit (q : Option Bool) (b : Bool) : Bool := q == some true && !b

def clausePending : Option Bool → Bool → Option Bool
  | none, b => some b
  | some _, _ => none

/-- One unary output mark per aligned 10 pair, with an ignored unmatched bit. -/
def clauseMarks : Option Bool → List Bool → List Bool
  | _, [] => []
  | q, b :: bs =>
      if clauseHit q b then true :: clauseMarks (clausePending q b) bs
      else clauseMarks (clausePending q b) bs

theorem clauseMarks_double_append (data rest : List Bool) :
    clauseMarks none (doubleBits data ++ rest) = clauseMarks none rest := by
  induction data with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simpa [doubleBits, clauseMarks, clauseHit, clausePending] using ih

theorem clauseMarks_clause_append (c : Clause) (rest : List Bool) :
    clauseMarks none (c.encode ++ rest) = clauseMarks none rest := by
  induction c with
  | nil => rfl
  | cons lit cs ih =>
    simp only [Clause.encode_cons, List.append_assoc, clauseMarks_double_append]
    simpa [clauseMarks, clauseHit, clausePending] using ih

theorem clauseMarks_encode (φ : CNF) :
    clauseMarks none φ.encode = List.replicate φ.length true := by
  induction φ with
  | nil => rfl
  | cons c cs ih =>
    simp only [CNF.encode_cons, List.append_assoc, clauseMarks_clause_append]
    simpa [clauseMarks, clauseHit, clausePending, List.replicate_succ] using
      congrArg (List.cons true) ih

inductive ClauseCountPhase where
  | init | scan (pending : Option Bool) | done
  deriving DecidableEq

instance : Fintype ClauseCountPhase where
  elems := {.init, .done} ∪ Finset.univ.image ClauseCountPhase.scan
  complete q := by cases q <;> simp

/-- Fixed finite-state unary clause-count transducer. The caller separately
checks syntax. The source contents survive, with its head at the first blank. -/
def clauseCountTM : TM 0 where
  Q := ClauseCountPhase
  qstart := .init
  qhalt := .done
  δ := fun q ih wh oh =>
    match q with
    | .init => allIdle (.scan none) ih wh oh
    | .done => allIdle .done ih wh oh
    | .scan p =>
      if ih = Γ.blank then
        (.done, Fin.elim0, readBackWrite oh, idleDir ih, Fin.elim0, idleDir oh)
      else
        (.scan (clausePending p (ih == Γ.one)), Fin.elim0,
          if clauseHit p (ih == Γ.one) then Γw.one else readBackWrite oh,
          .right, Fin.elim0,
          if clauseHit p (ih == Γ.one) then .right else idleDir oh)
  δ_right_of_start := by
    intro q ih wh oh
    cases q with
    | init => exact rightOfStart_allIdle ih wh oh
    | done => exact rightOfStart_allIdle ih wh oh
    | scan p =>
      dsimp only []
      split
      · exact ⟨idleDir_right_of_start, fun i => Fin.elim0 i, idleDir_right_of_start⟩
      · refine ⟨fun _ => rfl, fun i => Fin.elim0 i, ?_⟩
        split
        · exact fun _ => rfl
        · exact idleDir_right_of_start

def clauseCountCfg (p : Option Bool) (inp out : Tape) : Cfg 0 clauseCountTM.Q :=
  ⟨.scan p, inp, Fin.elim0, out⟩

def clauseNextOut (p : Option Bool) (b : Bool) (out : Tape) : Tape :=
  if clauseHit p b then out.writeAndMove Γ.one .right else out

theorem clauseCountTM_bit_step (p : Option Bool) (inp out : Tape) (b : Bool)
    (hr : inp.read = Γ.ofBool b) (hout : Parked out) :
    clauseCountTM.step (clauseCountCfg p inp out) =
      some (clauseCountCfg (clausePending p b) (inp.move .right)
        (clauseNextOut p b out)) := by
  by_cases hh : clauseHit p b = true
  · cases b <;>
      simp only [TM.step, clauseCountCfg, clauseCountTM, reduceCtorEq, ↓reduceIte,
        hr, Γ.ofBool, beq_self_eq_true, show (Γ.zero == Γ.one) = false from rfl,
        hh, clauseNextOut] <;>
      apply congrArg some <;>
      exact Cfg.ext rfl rfl (Subsingleton.elim _ _) rfl
  · cases b <;>
      simp only [TM.step, clauseCountCfg, clauseCountTM, reduceCtorEq, ↓reduceIte,
        hr, Γ.ofBool, beq_self_eq_true, show (Γ.zero == Γ.one) = false from rfl,
        hh, clauseNextOut] <;>
      apply congrArg some <;>
      exact Cfg.ext rfl rfl (Subsingleton.elim _ _) hout.writeAndMove_readBack_idle

theorem clauseCountTM_end_step (p : Option Bool) (inp out : Tape)
    (hr : inp.read = Γ.blank) (hout : Parked out) :
    clauseCountTM.step (clauseCountCfg p inp out) =
      some ⟨.done, inp, Fin.elim0, out⟩ := by
  simp only [TM.step, clauseCountCfg, clauseCountTM, reduceCtorEq, ↓reduceIte, hr,
    idleDir, show Γ.blank ≠ Γ.start from by decide]
  apply congrArg some
  refine Cfg.ext rfl ?_ (Subsingleton.elim _ _) ?_
  · rfl
  · exact hout.writeAndMove_readBack_idle

theorem clauseCountTM_scan (bits ys : List Bool) (p : Option Bool) (inp out : Tape)
    (hin : inp.HasBinarySuffix bits) (hout : OutAcc ys out) :
    ∃ c, clauseCountTM.reachesIn (bits.length+1) (clauseCountCfg p inp out) c ∧
      clauseCountTM.halted c ∧ OutAcc (ys ++ clauseMarks p bits) c.output ∧
      c.input.cells = inp.cells ∧ c.input.head = inp.head + bits.length := by
  induction bits generalizing p inp out ys with
  | nil =>
    refine ⟨_, .step (clauseCountTM_end_step p inp out hin.read_nil hout.parked) .zero,
      rfl, ?_, rfl, by simp⟩
    simpa [clauseMarks] using hout
  | cons b bs ih =>
    by_cases hh : clauseHit p b = true
    · have ho : OutAcc (ys ++ [true]) (clauseNextOut p b out) := by
        simpa [clauseNextOut, hh] using outAcc_append_bit hout true
      obtain ⟨c, hc, hhalt, hout', hcells, hhead⟩ := ih (ys ++ [true])
        (clausePending p b) (inp.move .right) (clauseNextOut p b out)
        hin.move_right_cons ho
      refine ⟨c, .step (clauseCountTM_bit_step p inp out b hin.read_cons hout.parked) hc,
        hhalt, ?_, hcells, ?_⟩
      · simpa [clauseMarks, hh, List.append_assoc] using hout'
      · simpa [Tape.move, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hhead
    · have ho : OutAcc ys (clauseNextOut p b out) := by
        simpa [clauseNextOut, hh] using hout
      obtain ⟨c, hc, hhalt, hout', hcells, hhead⟩ := ih ys
        (clausePending p b) (inp.move .right) (clauseNextOut p b out)
        hin.move_right_cons ho
      refine ⟨c, .step (clauseCountTM_bit_step p inp out b hin.read_cons hout.parked) hc,
        hhalt, ?_, hcells, ?_⟩
      · simpa [clauseMarks, hh] using hout'
      · simpa [Tape.move, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hhead

theorem clauseCountTM_init_step (z : List Bool) :
    clauseCountTM.step (clauseCountTM.initCfg z) = some
      (clauseCountCfg none ((Tape.init (z.map Γ.ofBool)).move .right)
        ((Tape.init []).move .right)) := by
  simp [TM.step, clauseCountTM, clauseCountCfg, allIdle, Tape.read,
    Tape.writeAndMove, Tape.write, Tape.move, Tape.init, idleDir]
  exact Subsingleton.elim _ _

theorem clauseCountTM_correct (z : List Bool) :
    ∃ c, clauseCountTM.reachesIn (z.length+2) (clauseCountTM.initCfg z) c ∧
      clauseCountTM.halted c ∧ OutAcc (clauseMarks none z) c.output ∧
      c.input.cells = (Tape.init (z.map Γ.ofBool)).cells ∧
      c.input.head = z.length+1 := by
  obtain ⟨c, hc, hh, ho, hi, hp⟩ := clauseCountTM_scan z [] none _ _
    (Tape.init_move_right_hasBinarySuffix z) outAcc_nil_init
  refine ⟨c, .step (clauseCountTM_init_step z) hc, hh, ?_, hi, ?_⟩
  · simpa using ho
  · simpa [Tape.move, Tape.init, Nat.add_comm] using hp

theorem clauseCountTM_encode_correct (φ : CNF) :
    ∃ c, clauseCountTM.reachesIn (φ.encode.length+2) (clauseCountTM.initCfg φ.encode) c ∧
      clauseCountTM.halted c ∧ OutAcc (List.replicate φ.length true) c.output ∧
      c.input.cells = (Tape.init (φ.encode.map Γ.ofBool)).cells ∧
      c.input.head = φ.encode.length+1 := by
  simpa [clauseMarks_encode] using clauseCountTM_correct φ.encode

end IrrRAFEnumeration.SATSource

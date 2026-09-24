import proofs.IrrRAFEnumeration.SATSyntaxBits
import proofs.Complexitylib.Models.TuringMachine.Combinators
import proofs.Complexitylib.Models.TuringMachine.Tape.Encoding

namespace IrrRAFEnumeration.SATSource

open Complexity SAT Complexity.TM

instance : Fintype RawKind where
  elems := {.empty, .valid, .invalid}
  complete q := by cases q <;> simp

inductive SyntaxPhase where
  | init | scan (q : SyntaxBitState) | done
  deriving DecidableEq

instance : Fintype SyntaxPhase where
  elems := {.init, .done} ∪ Finset.univ.image SyntaxPhase.scan
  complete q := by cases q <;> simp

def syntaxInitial : SyntaxBitState := ((.empty, true), none)

/-- One pass, no work tapes, one verdict bit. Invalid inputs are scanned to
their end as well, giving the same exact linear bound on every bitstring. -/
def syntaxTM : TM 0 where
  Q := SyntaxPhase
  qstart := .init
  qhalt := .done
  δ := fun q ih wh oh =>
    match q with
    | .init => allIdle (.scan syntaxInitial) ih wh oh
    | .done => allIdle .done ih wh oh
    | .scan s =>
      if ih = Γ.blank then
        (.done, Fin.elim0, if syntaxFinish s then Γw.one else Γw.zero,
          idleDir ih, Fin.elim0, idleDir oh)
      else
        (.scan (syntaxBitStep s (ih == Γ.one)), Fin.elim0, readBackWrite oh,
          .right, Fin.elim0, idleDir oh)
  δ_right_of_start := by
    intro q ih wh oh
    cases q with
    | init => exact rightOfStart_allIdle ih wh oh
    | done => exact rightOfStart_allIdle ih wh oh
    | scan s =>
      dsimp only []
      split
      · exact ⟨idleDir_right_of_start, fun i => Fin.elim0 i, idleDir_right_of_start⟩
      · exact ⟨fun _ => rfl, fun i => Fin.elim0 i, idleDir_right_of_start⟩

def syntaxBlankOut : Tape := (Tape.init []).move .right

def syntaxScanCfg (q : SyntaxBitState) (inp : Tape) : Cfg 0 syntaxTM.Q :=
  ⟨.scan q, inp, Fin.elim0, syntaxBlankOut⟩

def syntaxVerdict (b : Bool) : Tape :=
  syntaxBlankOut.writeAndMove (if b then Γw.one else Γw.zero) .stay

theorem syntaxVerdict_cell (b : Bool) : (syntaxVerdict b).cells 1 = Γ.ofBool b := by
  cases b <;> simp [syntaxVerdict, syntaxBlankOut, Tape.writeAndMove, Tape.write, Tape.move, Tape.init, Γ.ofBool]

theorem syntaxTM_bit_step (q : SyntaxBitState) (inp : Tape) (b : Bool)
    (hr : inp.read = Γ.ofBool b) :
    syntaxTM.step (syntaxScanCfg q inp) =
      some (syntaxScanCfg (syntaxBitStep q b) (inp.move .right)) := by
  have ho : syntaxBlankOut.writeAndMove Γ.blank .stay = syntaxBlankOut :=
    writeAndMove_readBack syntaxBlankOut (by decide) .stay
  cases b <;>
    simp only [TM.step, syntaxScanCfg, syntaxTM, reduceCtorEq, ↓reduceIte, hr,
      Γ.ofBool, beq_self_eq_true, show (Γ.zero == Γ.one) = false from rfl] <;>
    apply congrArg some <;>
    exact Cfg.ext rfl rfl (Subsingleton.elim _ _) ho

theorem syntaxTM_end_step (q : SyntaxBitState) (inp : Tape)
    (hr : inp.read = Γ.blank) :
    syntaxTM.step (syntaxScanCfg q inp) =
      some ⟨.done, inp, Fin.elim0, syntaxVerdict (syntaxFinish q)⟩ := by
  simp only [TM.step, syntaxScanCfg, syntaxTM, reduceCtorEq, ↓reduceIte, hr]
  apply congrArg some
  refine Cfg.ext rfl rfl (Subsingleton.elim _ _) ?_
  cases h : syntaxFinish q <;> rfl

theorem syntaxTM_scan (bits : List Bool) (q : SyntaxBitState) (inp : Tape)
    (hin : inp.HasBinarySuffix bits) :
    ∃ c, syntaxTM.reachesIn (bits.length+1) (syntaxScanCfg q inp) c ∧
      syntaxTM.halted c ∧ c.output.cells 1 = Γ.ofBool (syntaxBits q bits) := by
  induction bits generalizing q inp with
  | nil =>
    refine ⟨_, .step (syntaxTM_end_step q inp hin.read_nil) .zero, rfl, ?_⟩
    exact syntaxVerdict_cell (syntaxFinish q)
  | cons b bs ih =>
    obtain ⟨c, hc, hh, ho⟩ := ih (syntaxBitStep q b) (inp.move .right) hin.move_right_cons
    refine ⟨c, ?_, hh, ho⟩
    exact .step (syntaxTM_bit_step q inp b hin.read_cons) hc

theorem syntaxTM_init_step (z : List Bool) :
    syntaxTM.step (syntaxTM.initCfg z) =
      some (syntaxScanCfg syntaxInitial ((Tape.init (z.map Γ.ofBool)).move .right)) := by
  simp [TM.step, syntaxTM, syntaxScanCfg, syntaxBlankOut,
    allIdle, Tape.read, Tape.writeAndMove, Tape.write, Tape.move, Tape.init, idleDir]
  exact Subsingleton.elim _ _

/-- Actual syntax-recognition machine, exact L+2 transitions on every string. -/
theorem syntaxTM_correct (z : List Bool) :
    ∃ c, syntaxTM.reachesIn (z.length+2) (syntaxTM.initCfg z) c ∧
      syntaxTM.halted c ∧ c.output.cells 1 = Γ.ofBool (CNF.decode? z).isSome := by
  obtain ⟨c, hr, hh, ho⟩ := syntaxTM_scan z syntaxInitial _
    (Tape.init_move_right_hasBinarySuffix z)
  refine ⟨c, .step (syntaxTM_init_step z) hr, hh, ?_⟩
  simpa [syntaxInitial, syntaxBits_eq_decode] using ho

end IrrRAFEnumeration.SATSource

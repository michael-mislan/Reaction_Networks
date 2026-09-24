import proofs.IrrRAFEnumeration.GatedHeader

namespace IrrRAFEnumeration.DecisionReporter
open Complexity Complexity.TM HeaderComparison GatedHeader

/-- Rewind the existing output, then put the complement of the saved no-case
verdict in cell one. A decision machine need not erase the trailing output. -/
def reporterTM : TM 2 where
  Q := Fin 3
  qstart := 0
  qhalt := 2
  δ := fun q i w o => if q = 1 then
    (2,fun j => readBackWrite (w j),Γw.ofBool (decide (w 1 ≠ Γ.one)),
      idleDir i,fun j => idleDir (w j),idleDir o)
    else headerTM.δ q i w o
  δ_right_of_start := by
    intro q i w o
    by_cases hq : q = 1
    · simp only [if_pos hq]
      exact ⟨idleDir_right_of_start,fun _ => idleDir_right_of_start,idleDir_right_of_start⟩
    · simp only [if_neg hq]
      exact headerTM.δ_right_of_start q i w o

theorem rewind_step_same (inp expected flag out : Tape) :
    reporterTM.step (config 0 inp expected flag out) =
      headerTM.step (config 0 inp expected flag out) := rfl

theorem reporter_rewind (p : Nat) (inp expected flag out : Tape)
    (hi : Parked inp) (he : Parked expected) (hf : Parked flag)
    (ho : out.StartInvariant) (hp : out.head = p) :
    reporterTM.reachesIn (p+1) (config 0 inp expected flag out)
      (config 1 inp expected flag (parkOutput out)) := by
  induction p generalizing out with
  | zero =>
    have hs := rewind_step_zero inp expected flag out hi he hf ho hp
    rw [← rewind_step_same] at hs
    exact .step hs .zero
  | succ p ih =>
    have hs := rewind_step_left inp expected flag out hi he hf ⟨by omega,ho.2⟩
    rw [← rewind_step_same] at hs
    have ht := ih (out.move .left) ⟨ho.1,ho.2⟩ (by simp [Tape.move,hp])
    simpa [parkOutput,Tape.move] using TM.reachesIn.step hs ht

theorem report_step (inp expected flag out : Tape) (answer : Bool)
    (hi : Parked inp) (he : Parked expected) (hf : Parked flag) (ho : Parked out)
    (hr : flag.read = Γ.ofBool answer) :
    reporterTM.step (config 1 inp expected flag out) =
      some (config 2 inp expected flag (out.write (Γw.ofBool (!answer)))) := by
  have hb : decide (flag.read ≠ Γ.one) = !answer := by
    cases answer <;> simp [hr,Γ.ofBool]
  simp only [TM.step,reporterTM,headerTM,config,
    show (1 : Fin 3) ≠ 2 by decide,↓reduceIte,
    show (1 : Fin 2) ≠ 0 by decide,hb,Option.some.injEq]
  refine Cfg.ext rfl hi.move_idle ?_ ?_
  · funext i
    fin_cases i
    · exact he.writeAndMove_readBack_idle
    · exact hf.writeAndMove_readBack_idle
  · change (out.write (Γw.ofBool (!answer))).move (idleDir out.read) = _
    rw [idleDir,if_neg ho.read_ne_start]
    rfl

theorem reporter_correct (inp expected flag out : Tape) (answer : Bool)
    (hi : Parked inp) (he : Parked expected) (hf : Parked flag)
    (ho : out.StartInvariant) (hr : flag.read = Γ.ofBool answer) :
    ∃ c, reporterTM.reachesIn (out.head+2) (config 0 inp expected flag out) c ∧
      reporterTM.halted c ∧ c.output.cells 1 = Γ.ofBool (!answer) ∧
      c.input = inp ∧ c.work = ![expected,flag] := by
  have hrew := reporter_rewind out.head inp expected flag out hi he hf ho rfl
  have hpark : Parked (parkOutput out) := ⟨by rfl,ho.2⟩
  have hs := report_step inp expected flag (parkOutput out) answer hi he hf hpark hr
  refine ⟨config 2 inp expected flag ((parkOutput out).write (Γw.ofBool (!answer))),
    ?_,rfl,?_,rfl,?_⟩
  · convert TM.reachesIn_trans reporterTM hrew (.step hs .zero) using 1
  · change ((parkOutput out).write (Γw.ofBool (!answer))).cells 1 = _
    cases answer <;> simp [Tape.write,parkOutput,Γw.ofBool,Γ.ofBool]
  · funext i
    fin_cases i <;> rfl

end IrrRAFEnumeration.DecisionReporter

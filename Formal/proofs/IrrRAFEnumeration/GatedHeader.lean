import proofs.IrrRAFEnumeration.HeaderComparison
import proofs.Complexitylib.Models.TuringMachine.Placement.Internal
import Mathlib.Data.Fin.VecNotation

namespace IrrRAFEnumeration.GatedHeader
open Complexity Complexity.TM HeaderComparison

def placedHeader : TM 3 := placeWorkTM 0 1 headerTM

/-- Read the clock success flag before touching the output header. -/
def gateTM : TM 3 where
  Q := Option (Fin 3)
  qstart := none
  qhalt := some 2
  δ := fun q i w o => match q with
    | none => if w 2 = Γ.one then allReadBack (some 0) i w o
      else (some 2,fun j => if j = 1 then Γw.zero else readBackWrite (w j),
        readBackWrite o,idleDir i,fun j => idleDir (w j),idleDir o)
    | some s =>
      let r := placedHeader.δ s i w o
      (some r.1,r.2)
  δ_right_of_start := by
    intro q i w o
    cases q with
    | none =>
      dsimp only
      split
      · exact rightOfStart_allIdle i w o
      · exact ⟨idleDir_right_of_start,fun _ => idleDir_right_of_start,idleDir_right_of_start⟩
    | some s => exact placedHeader.δ_right_of_start s i w o

def wrap (c : Cfg 3 placedHeader.Q) : Cfg 3 gateTM.Q :=
  ⟨some c.state,c.input,c.work,c.output⟩

def gateConfig (q : Option (Fin 3)) (inp expected flag clock out : Tape) : Cfg 3 gateTM.Q :=
  ⟨q,inp,![expected,flag,clock],out⟩

theorem gate_sim_step {c d : Cfg 3 placedHeader.Q} (hs : placedHeader.step c = some d) :
    gateTM.step (wrap c) = some (wrap d) := by
  have hn := TM.state_ne_qhalt_of_step hs
  have hg : (wrap c).state ≠ gateTM.qhalt := fun h => hn (Option.some.inj h)
  simp only [TM.step,hn,↓reduceIte,Option.some.injEq] at hs
  rw [← hs]
  rw [TM.step,if_neg hg]
  rfl

theorem gate_sim_run {t : Nat} {c d : Cfg 3 placedHeader.Q} (hr : placedHeader.reachesIn t c d) :
    gateTM.reachesIn t (wrap c) (wrap d) := by
  induction hr with
  | zero => exact .zero
  | step hs _ ih => exact .step (gate_sim_step hs) ih

theorem frame_eq (q : Fin 3) (inp expected flag clock out : Tape) :
    wrap (placeWorkCfg headerTM 0 1 (fun _ => clock) (config q inp expected flag out)) =
      gateConfig (some q) inp expected flag clock out := by
  unfold wrap gateConfig placeWorkCfg config
  congr 1
  funext i
  fin_cases i <;> rfl

theorem gate_true_step (inp expected flag clock out : Tape)
    (hi : Parked inp) (he : Parked expected) (hf : Parked flag) (hc : Parked clock)
    (ho : Parked out) (hr : clock.read = Γ.one) :
    gateTM.step (gateConfig none inp expected flag clock out) =
      some (gateConfig (some 0) inp expected flag clock out) := by
  simp only [TM.step,gateTM,gateConfig,
    show (![expected,flag,clock] (2 : Fin 3)) = clock by rfl,hr,↓reduceIte]
  apply congrArg some
  refine Cfg.ext rfl hi.move_idle ?_ ho.writeAndMove_readBack_idle
  funext i
  fin_cases i <;> first | exact he.writeAndMove_readBack_idle | exact hf.writeAndMove_readBack_idle |
    exact hc.writeAndMove_readBack_idle

theorem gate_false_step (inp expected flag clock out : Tape)
    (hi : Parked inp) (he : Parked expected) (hf : Parked flag) (hc : Parked clock)
    (ho : Parked out) (hr : clock.read ≠ Γ.one) :
    gateTM.step (gateConfig none inp expected flag clock out) =
      some (gateConfig (some 2) inp expected (flag.write Γw.zero) clock out) := by
  simp only [TM.step,gateTM,gateConfig,
    show (![expected,flag,clock] (2 : Fin 3)) = clock by rfl,hr,↓reduceIte]
  apply congrArg some
  refine Cfg.ext rfl hi.move_idle ?_ ho.writeAndMove_readBack_idle
  funext i
  fin_cases i
  · exact he.writeAndMove_readBack_idle
  · change (flag.write Γw.zero).move (idleDir flag.read) = flag.write Γw.zero
    rw [idleDir,if_neg hf.read_ne_start]
    rfl
  · exact hc.writeAndMove_readBack_idle

theorem parked_write (t : Tape) (h : Parked t) (b : Bool) : Parked (t.write (Γw.ofBool b)) := by
  refine ⟨by unfold Tape.write; split <;> exact h.1,?_⟩
  intro j hj
  simp only [Tape.write]
  split
  · exact h.2 j hj
  · simp only [Function.update]
    split
    · simpa using Γw.toΓ_ne_start (Γw.ofBool b)
    · exact h.2 j hj

theorem parked_advance (t : Tape) (h : Parked t) (k : Nat) : Parked (advance t k) :=
  ⟨Nat.le_trans h.1 (Nat.le_add_right _ _),h.2⟩

theorem gated_comparison_correct (actual supplied : Nat) (success : Bool)
    (inp expected flag clock out : Tape) (hi : Parked inp) (he : Parked expected)
    (hf : Parked flag) (hc : Parked clock) (ho : Parked out) (hInv : out.StartInvariant)
    (hclock : clock.read = Γ.ofBool success) (hE : UnaryPrefix expected supplied Γ.blank)
    (hO : success = true → UnaryPrefix (parkOutput out) actual Γ.zero) :
    ∃ c t, t ≤ out.head+supplied+3 ∧
      gateTM.reachesIn t (gateConfig none inp expected flag clock out) c ∧ gateTM.halted c ∧
      (c.work 1).read = Γ.ofBool (success && decide (actual = supplied)) ∧
      c.output.cells = out.cells ∧ c.input = inp ∧
      (∀ i, Parked (c.work i)) ∧ Parked c.output := by
  cases success with
  | false =>
    have hs := gate_false_step inp expected flag clock out hi he hf hc ho (by rw [hclock]; decide)
    refine ⟨_,1,by omega,.step hs .zero,rfl,?_,rfl,rfl,?_,ho⟩
    · exact verdict_read flag hf false
    · intro i
      fin_cases i <;> first | exact he | exact parked_write flag hf false | exact hc
  | true =>
    have hrewind := rewind_run out.head inp expected flag out hi he hf hInv rfl
    have hpark : Parked (parkOutput out) := ⟨by rfl,hInv.2⟩
    have hscan := scan_header_run actual supplied inp expected flag (parkOutput out)
      hi he hf hpark hE (hO rfl)
    have hr := TM.reachesIn_trans headerTM hrewind hscan
    have hframe := placeWorkTM_reachesIn_placeWorkCfg_stable_internal headerTM 0 1 (fun _ => clock)
      hr (fun _ _ => hc.read_ne_start)
    have hgate := gate_sim_run hframe
    rw [frame_eq,frame_eq] at hgate
    have hs := gate_true_step inp expected flag clock out hi he hf hc ho hclock
    refine ⟨_,1+((out.head+1)+(min actual supplied+1)),?_,
      TM.reachesIn_trans gateTM (.step hs .zero) hgate,rfl,?_,rfl,rfl,?_,?_⟩
    · have := min_le_right actual supplied; omega
    · exact verdict_read flag hf (decide (actual = supplied))
    · intro i
      fin_cases i <;> first | exact parked_advance expected he _ |
        exact parked_write flag hf _ | exact hc
    · exact parked_advance _ hpark _

end IrrRAFEnumeration.GatedHeader

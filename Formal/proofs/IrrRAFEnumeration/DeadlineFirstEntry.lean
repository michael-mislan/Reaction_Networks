import proofs.IrrRAFEnumeration.DeadlineMachine
import proofs.IrrRAFEnumeration.PolynomialClockSetup
import proofs.Complexitylib.Models.TuringMachine.Placement.Internal
import Mathlib.Tactic.FinCases

namespace IrrRAFEnumeration.DeadlineFirstEntry
open Complexity Complexity.TM
open DeadlineMachine PolynomialClockSetup

variable {n : Nat}

def firstState (tm : TM n) : tm.Q :=
  (tm.δ tm.qstart Γ.start (fun _ => Γ.start) Γ.start).1

/-- The compulsory first transition moves every head off the immutable
left marker. Its next state is fixed independently of the input bits. -/
def firstCfg (tm : TM n) (x : List Bool) : Cfg n tm.Q where
  state := firstState tm
  input := ⟨1,(Tape.init (x.map Γ.ofBool)).cells⟩
  work _ := ⟨1,(Tape.init []).cells⟩
  output := ⟨1,(Tape.init []).cells⟩

theorem first_step (tm : TM n) (hne : tm.qstart ≠ tm.qhalt) (x : List Bool) :
    tm.step (tm.initCfg x) = some (firstCfg tm x) := by
  obtain ⟨hi,hw,ho⟩ := tm.δ_right_of_start tm.qstart Γ.start (fun _ => Γ.start) Γ.start
  have hinput := hi rfl
  have houtput := ho rfl
  have hwork : (tm.δ tm.qstart Γ.start (fun _ => Γ.start) Γ.start).2.2.2.2.1 =
      fun _ => Dir3.right := funext (fun i => hw i rfl)
  simp only [TM.step,hne,↓reduceIte,Tape.read,Tape.init,
    Option.some.injEq,Tape.writeAndMove,Tape.write]
  simp only [hinput,houtput,hwork]
  rfl

/-- Any positive source run factors through this first configuration. This
is the entry point compatible with a polynomial setup that parks all heads. -/
theorem positive_run_tail (tm : TM n) (hne : tm.qstart ≠ tm.qhalt) (x : List Bool)
    {t : Nat} {c : Cfg n tm.Q} (hr : tm.reachesIn (t+1) (tm.initCfg x) c) :
    tm.reachesIn t (firstCfg tm x) c := by
  cases hr with
  | step hs htail =>
    have he := Option.some.inj (hs.symm.trans (first_step tm hne x))
    simpa [he] using htail

/-- Exact output of clock setup, including the empty real-output tape. -/
theorem setup_initial_run (p : Polynomial Nat) (x : List Bool) :
    ∃ c t, t ≤ setupTime p x.length ∧
      (setupTM p).reachesIn t ((setupTM p).initCfg x) c ∧
      (setupTM p).halted c ∧
      c.input = ⟨1,(Tape.init (x.map Γ.ofBool)).cells⟩ ∧
      c.work = clockWork p x.length ∧
      c.output = ⟨1,(Tape.init []).cells⟩ := by
  obtain ⟨c,t,ht,hr,hh,hinput,hwork,hout⟩ := setupTM_correct p x
    (Tape.init (x.map Γ.ofBool)) (fun _ => Tape.init []) (Tape.init [])
    ⟨rfl,fun _ => rfl,rfl⟩
  exact ⟨c,t,ht,hr,hh,hinput,hwork,hout.eq outAcc_nil_init⟩

theorem clockTape_zero_eq_regTape (budget : Nat) : clockTape budget 0 = regTape budget := rfl

def sourceFrame (n : Nat) (p : Polynomial Nat) (x : List Bool) : Fin (n+2) → Tape :=
  fun i => if i.val = n then regTape x.length else regTape (p.eval x.length)

def framedSourceCfg (tm : TM n) (p : Polynomial Nat) (x : List Bool)
    (c : Cfg n tm.Q) : Cfg (n+2) (tm.liftTM 2).Q where
  state := c.state
  input := c.input
  work i := if h : i.val < n then c.work ⟨i.val,h⟩ else sourceFrame n p x i
  output := c.output

def readyCfg (tm : TM n) (p : Polynomial Nat) (x : List Bool) :=
  clockCfg (tm.liftTM 2) (framedSourceCfg tm p x (firstCfg tm x))
    (regTape (p.eval x.length))

theorem readyCfg_work (tm : TM n) (p : Polynomial Nat) (x : List Bool) :
    (readyCfg tm p x).work =
      fun i => if h : placeWorkInMiddle (post := 0) n 3 i then
        clockWork p x.length (placeWorkCoord n 3 i h)
      else ⟨1,(Tape.init []).cells⟩ := by
  funext i
  by_cases hi : i.val < n
  · have houter : i.val < n+2 := by omega
    simp [readyCfg,clockCfg,framedSourceCfg,placeWorkInMiddle,
      firstCfg,hi,houter]
  · have hmid : placeWorkInMiddle (post := 0) n 3 i := by
      unfold placeWorkInMiddle
      have := i.isLt
      omega
    obtain ⟨j,hj⟩ : ∃ j : Fin 3, i = placeWorkIdx n 0 j := by
      refine ⟨placeWorkCoord (post := 0) n 3 i hmid,?_⟩
      exact (placeWorkIdx_placeWorkCoord (pre := n) (n := 3) (post := 0) i hmid).symm
    subst i
    simp only [placeWorkInMiddle_placeWorkIdx,↓reduceDIte,
      placeWorkCoord_placeWorkIdx]
    fin_cases j <;>
      simp [readyCfg,clockCfg,framedSourceCfg,sourceFrame,
        placeWorkIdx,clockWork,lengthWork,Fin.ext_iff]

theorem framed_source_step (tm : TM n) (p : Polynomial Nat) (x : List Bool)
    {c c' : Cfg n tm.Q} (hs : tm.step c = some c') :
    (tm.liftTM 2).step (framedSourceCfg tm p x c) =
      some (framedSourceCfg tm p x c') := by
  have hn := TM.state_ne_qhalt_of_step hs
  simp only [TM.step,hn,↓reduceIte,Option.some.injEq] at hs
  rw [← hs]
  simp only [TM.step,liftTM,framedSourceCfg,hn,↓reduceIte,Fin.val_castAdd,
    Fin.isLt,↓reduceDIte,Option.some.injEq]
  congr 1
  funext i
  by_cases hi : i.val < n
  · simp [hi]
  · simp only [hi,↓reduceDIte]
    unfold sourceFrame
    split <;> exact (parked_regTape _).writeAndMove_readBack_idle

theorem framed_source_run (tm : TM n) (p : Polynomial Nat) (x : List Bool)
    {t : Nat} {c c' : Cfg n tm.Q} (hr : tm.reachesIn t c c') :
    (tm.liftTM 2).reachesIn t (framedSourceCfg tm p x c)
      (framedSourceCfg tm p x c') := by
  induction hr with
  | zero => exact TM.reachesIn.zero
  | step hs _ ih => exact TM.reachesIn.step (framed_source_step tm p x hs) ih

end IrrRAFEnumeration.DeadlineFirstEntry

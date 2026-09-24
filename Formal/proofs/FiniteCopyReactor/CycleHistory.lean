import proofs.FiniteCopyReactor.ObservedCycle

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical

/-- An observation keeps the actual pulse categories, terminal state, and all
five counters. Policies may depend on the entire preceding observation list. -/
structure CycleObservation (V : ℕ) where
  before : Counts
  intervention : Intervention
  pulse : PulseOutcome before
  after : BoxCounts V
  counters : ReactorCounters

def recordCycle (V : ℕ) (N : Counts) (p : Intervention) (o : PulseOutcome N)
    (X : BoxCounts V × ReactorCounters) : CycleObservation V := ⟨N,p,o,X.1,X.2⟩

/-- A subprobability law on successful histories. Failed cycles contribute zero;
successful cycles restart from their actual terminal count state. -/
def cycleHistoryLaw (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (policy : List (CycleObservation V) → Intervention) (payoff : List (CycleObservation V) → ℝ) :
    ℕ → (N : Counts) → Restart V N → List (CycleObservation V) → ℝ
  | 0,_,_,H => payoff H
  | n+1,N,hN,H =>
    observedPulseCycle N V (policy H) hN r d hV (by linarith) hr' hd hd'
      (fun o X => if h : CycleSuccess V X then
        cycleHistoryLaw V r d hV hr hr' hd hd' policy payoff n (boxCounts X.1) h.1
          (recordCycle V N (policy H) o X :: H) else 0)

theorem cycle_history_bounds (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (policy : List (CycleObservation V) → Intervention) (payoff : List (CycleObservation V) → ℝ)
    (hp : ∀ H, 0 ≤ payoff H ∧ payoff H ≤ 1)
    (n : ℕ) (N : Counts) (hN : Restart V N) (H : List (CycleObservation V)) :
    0 ≤ cycleHistoryLaw V r d hV hr hr' hd hd' policy payoff n N hN H ∧
      cycleHistoryLaw V r d hV hr hr' hd hd' policy payoff n N hN H ≤ 1 := by
  induction n generalizing N H with
  | zero => exact hp H
  | succ n ih =>
    apply observed_cycle_bounds
    intro o X
    split_ifs with h
    · exact ih (boxCounts X.1) h.1 (recordCycle V N (policy H) o X :: H)
    · norm_num

theorem cycle_history_success_lower (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ)) (hlarge : 1000000 ≤ V)
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (policy : List (CycleObservation V) → Intervention)
    (n : ℕ) (N : Counts) (hN : Restart V N) (H : List (CycleObservation V)) :
    1-(n:ℝ)*oneCycleError V ≤ cycleHistoryLaw V r d hV hr hr' hd hd' policy (fun _ => 1) n N hN H := by
  have heps := oneCycleError_nonneg V
  induction n generalizing N H with
  | zero => simp [cycleHistoryLaw]
  | succ n ih =>
    let e := oneCycleError (V:ℝ)
    let c := 1-(n:ℝ)*e
    have hm : 0 ≤ cycleHistoryLaw V r d hV hr hr' hd hd' policy (fun _ => 1) (n+1) N hN H :=
      (cycle_history_bounds V r d hV hr hr' hd hd' policy (fun _ => 1) (fun _ => by norm_num) (n+1) N hN H).1
    by_cases hc : 0 ≤ c
    · let F := fun (o : PulseOutcome N) (X : BoxCounts V × ReactorCounters) =>
        if h : CycleSuccess V X then cycleHistoryLaw V r d hV hr hr' hd hd' policy (fun _ => 1) n
          (boxCounts X.1) h.1 (recordCycle V N (policy H) o X :: H) else 0
      let g := fun (_ : PulseOutcome N) (X : BoxCounts V × ReactorCounters) => c*FiniteKernel.eventIndicator {Y | CycleSuccess V Y} X
      have hF (o X) : 0 ≤ F o X ∧ F o X ≤ 1 := by
        unfold F
        split_ifs with h
        · exact cycle_history_bounds V r d hV hr hr' hd hd' policy (fun _ => 1) (fun _ => by norm_num) n _ h.1 _
        · norm_num
      have hc1 : c ≤ 1 := by dsimp [c,e]; nlinarith [Nat.cast_nonneg (α := ℝ) n]
      have hg (o X) : 0 ≤ g o X ∧ g o X ≤ 1 := by
        dsimp [g,FiniteKernel.eventIndicator]
        split_ifs
        · simpa only [mul_one] using And.intro hc hc1
        · norm_num
      have hgf (o X) : g o X ≤ F o X := by
        dsimp [g,F,FiniteKernel.eventIndicator]
        split_ifs with h
        · simpa only [mul_one] using ih (boxCounts X.1) h.1 (recordCycle V N (policy H) o X :: H)
        · norm_num
      have hmon := observed_cycle_mono N V (policy H) hN r d hV (by linarith) hr' hd hd' g F 1 1 hg hF hgf
      have hscale : observedPulseCycle N V (policy H) hN r d hV (by linarith) hr' hd hd' g=
          c*pulseCycle N V (policy H) hN r d hV (by linarith) hr' hd hd'
            (FiniteKernel.eventIndicator {X | CycleSuccess V X}) :=
        pulse_cycle_scale N V (policy H) hN r d hV (by linarith) hr' hd hd' _ c
      rw [hscale] at hmon
      have hs := mul_le_mul_of_nonneg_left (pulse_cycle_success_bound N V (policy H) hN hlarge r d hV hr hr' hd hd') hc
      have hfinal := hs.trans hmon
      change c*(1-e) ≤ cycleHistoryLaw V r d hV hr hr' hd hd' policy (fun _ => 1) (n+1) N hN H at hfinal
      have hn := mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sq_nonneg e)
      dsimp [c,e] at hfinal hn
      push_cast
      nlinarith only [hfinal,hn]
    · dsimp [c,e] at hc
      push_cast
      nlinarith only [hm,hc,heps]

end
end FiniteCopyReactor

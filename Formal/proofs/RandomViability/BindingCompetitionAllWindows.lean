import proofs.RandomViability.BindingCompetitionWindowHistory

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped NNReal
variable {V C : ℕ}

theorem competition_monitor_steps_nonneg
    (P : FiniteKernel (CompetitionWindowState V C)) (t : ℝ≥0)
    (f : CompetitionMonitorState V C → ℝ) (hf : ∀ X, 0 ≤ f X)
    (n : ℕ) (X : CompetitionMonitorState V C) :
    0 ≤ competitionMonitorSteps P t n f X := by
  induction n generalizing X with
  | zero => exact hf X
  | succ n ih =>
    exact P.poissonized_nonneg t _ (fun Y => ih (competitionWindowBoundary Y X.2)) X.1

/-- Telescoping the boundary operator, without independence or enumeration. -/
theorem competition_monitor_iterate_bound
    (P : FiniteKernel (CompetitionWindowState V C)) (t : ℝ≥0)
    (p : ℝ) (hp : 0 ≤ p)
    (hstep : ∀ X, competitionMonitorAdvance P t competitionMonitorBad X ≤
      competitionMonitorBad X+p)
    (n : ℕ) (X : CompetitionMonitorState V C) :
    competitionMonitorSteps P t n competitionMonitorBad X ≤
      competitionMonitorBad X+(n:ℝ)*p := by
  induction n generalizing X with
  | zero => simp [competitionMonitorSteps]
  | succ n ih =>
    change P.poissonized t
      (fun Y => competitionMonitorSteps P t n competitionMonitorBad (competitionWindowBoundary Y X.2)) X.1 ≤ _
    have hm := P.poissonized_mono t _
      (fun Y => competitionMonitorBad (competitionWindowBoundary Y X.2)+(n:ℝ)*p)
      (fun Y => competition_monitor_steps_nonneg P t competitionMonitorBad competitionMonitorBad_nonneg n _)
      (fun Y => add_nonneg (competitionMonitorBad_nonneg _) (mul_nonneg (Nat.cast_nonneg n) hp))
      (fun Y => ih (competitionWindowBoundary Y X.2)) X.1
    have ha := P.poissonized_add t
      (fun Y => competitionMonitorBad (competitionWindowBoundary Y X.2))
      (fun _ => (n:ℝ)*p)
      (fun Y => competitionMonitorBad_nonneg _)
      (fun _ => mul_nonneg (Nat.cast_nonneg n) hp) X.1
    rw [ha,P.poissonized_const] at hm
    have hh := hstep X
    change P.poissonized t (fun Y => competitionMonitorBad (competitionWindowBoundary Y X.2)) X.1 ≤ _ at hh
    push_cast
    linarith

/-- All completed windows on the same chemical history with one persistent bit. -/
theorem competition_all_windows_probability (V : ℕ) (eps k r delta : ℝ)
    (hV : 0 < (V:ℝ)) (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r) (hd : 0 ≤ delta)
    (q : ℝ≥0) (hq : 0 < (q:ℝ)) (hclock : (V:ℝ)/27000 ≤ q)
    (hb : ∀ X, (competitionWindowModel V (competitionWindowCap V) eps k r delta hV heps hk hr hd).total X ≤ q)
    (m : ℕ) (X : CompetitionWindowState V (competitionWindowCap V)) :
    competitionMonitorSteps
      ((competitionWindowModel V (competitionWindowCap V) eps k r delta hV heps hk hr hd).uniformize q hq hb) q m
      competitionMonitorBad (X,true) ≤ (m:ℝ)*Real.exp (1/8-(13/1080000)*(V:ℝ)) := by
  let P := (competitionWindowModel V (competitionWindowCap V) eps k r delta hV heps hk hr hd).uniformize q hq hb
  have hs (Z : CompetitionMonitorState V (competitionWindowCap V)) :
      competitionMonitorAdvance P q competitionMonitorBad Z ≤
        competitionMonitorBad Z+Real.exp (1/8-(13/1080000)*(V:ℝ)) := by
    have h := competition_monitor_one_window eps k r delta hV heps hk hr hd q hq hclock hb Z
    apply h.trans (add_le_add le_rfl (Real.exp_le_exp.mpr ?_))
    have hc := competition_window_cap_upper V
    linarith
  have h := competition_monitor_iterate_bound P q _ (Real.exp_pos _).le hs m (X,true)
  simpa [competitionMonitorBad,FiniteKernel.eventIndicator] using h

end
end RandomViability.Binding

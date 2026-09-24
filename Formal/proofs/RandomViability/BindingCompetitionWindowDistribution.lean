import proofs.RandomViability.BindingCompetitionMonitorFoster

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped NNReal

/-- The all-window estimate is uniform under any finite startup law. -/
theorem competition_distributed_windows_probability {α : Type*} [Fintype α]
    (S : FiniteKernel α) (s : ℝ≥0) (start : α → CompetitionWindowState V (competitionWindowCap V))
    (eps k r delta : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r) (hd : 0 ≤ delta)
    (q : ℝ≥0) (hq : 0 < (q:ℝ)) (hclock : (V:ℝ)/27000 ≤ q)
    (hb : ∀ X, (competitionWindowModel V (competitionWindowCap V) eps k r delta hV heps hk hr hd).total X ≤ q)
    (m : ℕ) (X : α) :
    S.poissonized s (fun Z => competitionMonitorSteps
      ((competitionWindowModel V (competitionWindowCap V) eps k r delta hV heps hk hr hd).uniformize q hq hb) q m
      competitionMonitorBad (start Z,true)) X ≤ (m:ℝ)*Real.exp (1/8-(13/1080000)*(V:ℝ)) := by
  have h := S.poissonized_mono s _ (fun _ => (m:ℝ)*Real.exp (1/8-(13/1080000)*(V:ℝ)))
    (fun Z => competition_monitor_steps_nonneg _ q competitionMonitorBad competitionMonitorBad_nonneg m _)
    (fun _ => by positivity)
    (fun Z => competition_all_windows_probability V eps k r delta hV heps hk hr hd q hq hclock hb m (start Z)) X
  simpa only [S.poissonized_const] using h

end
end RandomViability.Binding

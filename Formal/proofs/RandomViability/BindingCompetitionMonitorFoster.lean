import proofs.RandomViability.BindingCompetitionAllWindows

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped NNReal
variable {V C : ℕ}

theorem competition_monitor_foster_iteration
    (P : FiniteKernel (CompetitionWindowState V C)) (t : ℝ≥0)
    (f : CompetitionMonitorState V C → ℝ) (hf : ∀ X, 0 ≤ f X)
    (b : ℝ) (hb : 0 ≤ b)
    (hstep : ∀ X, competitionMonitorAdvance P t f X ≤ f X+b)
    (n : ℕ) (X : CompetitionMonitorState V C) :
    competitionMonitorSteps P t n f X ≤ f X+(n:ℝ)*b := by
  induction n generalizing X with
  | zero => simp [competitionMonitorSteps]
  | succ n ih =>
    change P.poissonized t
      (fun Y => competitionMonitorSteps P t n f (competitionWindowBoundary Y X.2)) X.1 ≤ _
    have hm := P.poissonized_mono t _
      (fun Y => f (competitionWindowBoundary Y X.2)+(n:ℝ)*b)
      (fun Y => competition_monitor_steps_nonneg P t f hf n _)
      (fun Y => add_nonneg (hf _) (mul_nonneg (Nat.cast_nonneg n) hb))
      (fun Y => ih (competitionWindowBoundary Y X.2)) X.1
    have ha := P.poissonized_add t (fun Y => f (competitionWindowBoundary Y X.2))
      (fun _ => (n:ℝ)*b) (fun Y => hf _) (fun _ => mul_nonneg (Nat.cast_nonneg n) hb) X.1
    rw [ha,P.poissonized_const] at hm
    have hh := hstep X
    change P.poissonized t (fun Y => f (competitionWindowBoundary Y X.2)) X.1 ≤ _ at hh
    push_cast
    linarith

/-- Every nonnegative source Foster potential survives counter resets unchanged. -/
theorem competition_monitor_source_foster (eps k r delta : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r) (hd : 0 ≤ delta)
    (q : ℝ≥0) (hq : 0 < (q:ℝ))
    (hbound : ∀ X, (competitionWindowModel V C eps k r delta hV heps hk hr hd).total X ≤ q)
    (f : CompetitionCounts V → ℝ) (hf : ∀ X, 0 ≤ f X) (b : ℝ) (hb : 0 ≤ b)
    (hgen : ∀ X, (competitionModel V eps k r delta hV heps hk hr hd).generator f X ≤ b)
    (n : ℕ) (X : CompetitionMonitorState V C) :
    competitionMonitorSteps
      ((competitionWindowModel V C eps k r delta hV heps hk hr hd).uniformize q hq hbound) q n
      (fun Z => f Z.1.1) X ≤ f X.1.1+(n:ℝ)*b := by
  let M := competitionWindowModel V C eps k r delta hV heps hk hr hd
  let P := M.uniformize q hq hbound
  have hg (Y : CompetitionWindowState V C) : M.generator (fun Z => f Z.1) Y ≤ b := by
    by_cases hp : competitionPhase Y.1=0
    · rw [competition_window_deadline_failure V C eps k r delta hV heps hk hr hd _ Y hp]
      exact hb
    · rw [competition_window_project V C eps k r delta hV heps hk hr hd f Y hp]
      exact hgen Y.1
  apply competition_monitor_foster_iteration P q (fun Z => f Z.1.1) (fun Z => hf _) b hb
  intro Y
  change P.poissonized q (fun Z => f Z.1) Y.1 ≤ f Y.1.1+b
  have hh := P.poissonized_drift_bound q (fun Z => f Z.1) (b/(q:ℝ))
    (fun Z => hf _) (M.uniformize_drift q hq hbound _ b hg) Y.1
  have he : (q:ℝ)*(b/(q:ℝ))=b := by field_simp
  simpa only [he] using hh

theorem competition_monitor_resource_bound (V C : ℕ) (eps k r delta : ℝ)
    (hV : 0 < (V:ℝ)) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hk : 0 ≤ k) (hk1 : k ≤ 1/8) (hr : 0 ≤ r) (hr1 : r ≤ 22) (hd : 0 ≤ delta)
    (q : ℝ≥0) (hq : 0 < (q:ℝ))
    (hbound : ∀ X, (competitionWindowModel V C eps k r delta hV heps hk hr hd).total X ≤ q)
    (n : ℕ) (X : CompetitionMonitorState V C) :
    competitionMonitorSteps
      ((competitionWindowModel V C eps k r delta hV heps hk hr hd).uniformize q hq hbound) q n
      (fun Z => resourcePotential V (boxCounts (competitionCounts Z.1.1))) X ≤
      resourcePotential V (boxCounts (competitionCounts X.1.1))+(n:ℝ)*(4*resourceSource V) := by
  exact competition_monitor_source_foster eps k r delta hV heps hk hr hd q hq hbound
    _ (fun Z => resourcePotential_nonneg V _) _ (by unfold resourceSource; positivity)
    (competition_resource_foster V eps k r delta hV heps heps1 hk hk1 hr hr1 hd) n X

theorem competition_monitor_return_bound (V C : ℕ) (eps k r delta : ℝ)
    (hV : 0 < (V:ℝ)) (heps : 0 ≤ eps) (heps1 : eps ≤ 1/1000000)
    (hk : 0 ≤ k) (hk1 : k ≤ 1/8) (hr : 18 ≤ r) (hr1 : r ≤ 22)
    (hd : 0 ≤ delta) (hd1 : delta ≤ 3/5)
    (q : ℝ≥0) (hq : 0 < (q:ℝ))
    (hbound : ∀ X, (competitionWindowModel V C eps k r delta hV heps hk (by linarith) hd).total X ≤ q)
    (n : ℕ) (X : CompetitionMonitorState V C) :
    competitionMonitorSteps
      ((competitionWindowModel V C eps k r delta hV heps hk (by linarith) hd).uniformize q hq hbound) q n
      (fun Z => competitionTrackedReturnPotential Z.1.1) X ≤
      competitionTrackedReturnPotential X.1.1+(n:ℝ)*competitionReturnSource V := by
  exact competition_monitor_source_foster eps k r delta hV heps hk (by linarith) hd q hq hbound
    _ competition_tracked_return_nonneg _ (by unfold competitionReturnSource; positivity)
    (competition_tracked_return_foster V eps k r delta hV heps heps1 hk hk1 hr hr1 hd hd1) n X

end
end RandomViability.Binding

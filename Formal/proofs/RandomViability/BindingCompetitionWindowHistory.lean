import proofs.RandomViability.BindingCompetitionWindowRounded

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped BigOperators NNReal
variable {V C : ℕ}

def competitionWindowGood (X : CompetitionWindowState V C) : Prop :=
  competitionEnabled X.1 ∧ competitionPhase X.1=1

abbrev CompetitionMonitorState (V C : ℕ) := CompetitionWindowState V C × Bool

/-- Preserve chemical counts and phase. Update the persistent pass bit before
resetting only the current measurement counter. -/
def competitionWindowBoundary (Y : CompetitionWindowState V C) (passed : Bool) : CompetitionMonitorState V C :=
  ((Y.1,0),if C≤Y.2.val then passed else false)

def competitionMonitorBad (X : CompetitionMonitorState V C) : ℝ :=
  FiniteKernel.eventIndicator {Z | competitionWindowGood Z.1 ∧ Z.2=false} X

def competitionMonitorAdvance (P : FiniteKernel (CompetitionWindowState V C)) (t : ℝ≥0)
    (f : CompetitionMonitorState V C → ℝ) (X : CompetitionMonitorState V C) : ℝ :=
  P.poissonized t (fun Y => f (competitionWindowBoundary Y X.2)) X.1

def competitionMonitorSteps (P : FiniteKernel (CompetitionWindowState V C)) (t : ℝ≥0) :
    ℕ → (CompetitionMonitorState V C → ℝ) → CompetitionMonitorState V C → ℝ
  | 0,f => f
  | n+1,f => competitionMonitorAdvance P t (competitionMonitorSteps P t n f)

theorem competitionMonitorBad_nonneg (X : CompetitionMonitorState V C) : 0 ≤ competitionMonitorBad X := by
  unfold competitionMonitorBad FiniteKernel.eventIndicator
  split_ifs <;> norm_num

theorem competition_boundary_true (Y : CompetitionWindowState V C) :
    competitionMonitorBad (competitionWindowBoundary Y true) =
      FiniteKernel.eventIndicator {Z | competitionWindowActive Z} Y := by
  by_cases hc : C≤Y.2.val
  · have hn : ¬Y.2.val<C := by omega
    simp [competitionMonitorBad,competitionWindowBoundary,hc,FiniteKernel.eventIndicator,
      competitionWindowActive,hn]
  · have hn : Y.2.val<C := by omega
    simp [competitionMonitorBad,competitionWindowBoundary,hc,FiniteKernel.eventIndicator,
      competitionWindowActive,competitionWindowGood,hn]

theorem competition_boundary_false (Y : CompetitionWindowState V C) :
    competitionMonitorBad (competitionWindowBoundary Y false) =
      FiniteKernel.eventIndicator {Z | competitionWindowGood Z} Y := by
  simp [competitionMonitorBad,competitionWindowBoundary,FiniteKernel.eventIndicator,
    competitionWindowGood]

theorem competition_window_bad_step (eps k r delta : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r) (hd : 0 ≤ delta)
    (q : ℝ) (hq : 0 < q)
    (hb : ∀ X, (competitionWindowModel V C eps k r delta hV heps hk hr hd).total X ≤ q)
    (X : CompetitionWindowState V C) (h : ¬competitionWindowGood X) (f : CompetitionWindowState V C → ℝ) :
    ((competitionWindowModel V C eps k r delta hV heps hk hr hd).uniformize q hq hb).step f X = f X := by
  by_cases hp : competitionPhase X.1=0
  · simp [FiniteJumpModel.uniformize_step,FiniteJumpModel.generator,competitionWindowModel,hp]
  · have hen : ¬competitionEnabled X.1 := by
      intro he
      have hp1 : competitionPhase X.1=1 := by have hh := he.1; omega
      exact h ⟨he,hp1⟩
    simp [FiniteJumpModel.uniformize_step,FiniteJumpModel.generator,competitionWindowModel,hp,
      competitionModel,hen]

theorem competition_window_bad_poisson (eps k r delta : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r) (hd : 0 ≤ delta)
    (q : ℝ) (hq : 0 < q)
    (hb : ∀ X, (competitionWindowModel V C eps k r delta hV heps hk hr hd).total X ≤ q)
    (X : CompetitionWindowState V C) (h : ¬competitionWindowGood X) (t : ℝ≥0)
    (f : CompetitionWindowState V C → ℝ) :
    ((competitionWindowModel V C eps k r delta hV heps hk hr hd).uniformize q hq hb).poissonized t f X = f X := by
  let P := (competitionWindowModel V C eps k r delta hV heps hk hr hd).uniformize q hq hb
  have hs (n : ℕ) : P.steps n f X = f X := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [FiniteKernel.steps,competition_window_bad_step eps k r delta hV heps hk hr hd q hq hb X h]
      exact ih
  change P.poissonized t f X = f X
  unfold FiniteKernel.poissonized
  simp_rw [hs]
  simpa only [one_mul] using ((poissonWeight_sum t).mul_right (f X)).tsum_eq

/-- The only new failure per boundary is insufficient output while still good.
Already failed chemical histories cannot resurrect; common failures are not
recharged inside the per-window allowance. -/
theorem competition_monitor_one_window (eps k r delta : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r) (hd : 0 ≤ delta)
    (q : ℝ≥0) (hq : 0 < (q:ℝ)) (hclock : (V:ℝ)/27000 ≤ q)
    (hb : ∀ X, (competitionWindowModel V C eps k r delta hV heps hk hr hd).total X ≤ q)
    (X : CompetitionMonitorState V C) :
    competitionMonitorAdvance
      ((competitionWindowModel V C eps k r delta hV heps hk hr hd).uniformize q hq hb) q
      competitionMonitorBad X ≤ competitionMonitorBad X+Real.exp ((C:ℝ)/8-(V:ℝ)/27000) := by
  let P := (competitionWindowModel V C eps k r delta hV heps hk hr hd).uniformize q hq hb
  cases hp : X.2 with
  | true =>
    have hh : competitionMonitorAdvance P q competitionMonitorBad X =
        P.poissonized q (FiniteKernel.eventIndicator {Z | competitionWindowActive Z}) X.1 := by
      simp only [competitionMonitorAdvance,hp,competition_boundary_true]
    change competitionMonitorAdvance P q competitionMonitorBad X ≤ _
    rw [hh]
    have hw := competition_window_probability eps k r delta hV heps hk hr hd q 1 hq hclock hb X.1
    norm_num only [mul_one,NNReal.coe_one,one_mul] at hw
    exact hw.trans (le_add_of_nonneg_left (competitionMonitorBad_nonneg X))
  | false =>
    have hh : competitionMonitorAdvance P q competitionMonitorBad X =
        P.poissonized q (FiniteKernel.eventIndicator {Z | competitionWindowGood Z}) X.1 := by
      simp only [competitionMonitorAdvance,hp,competition_boundary_false]
    change competitionMonitorAdvance P q competitionMonitorBad X ≤ _
    rw [hh]
    by_cases hg : competitionWindowGood X.1
    · have hbX : competitionMonitorBad X=1 := by simp [competitionMonitorBad,FiniteKernel.eventIndicator,hg,hp]
      rw [hbX]
      exact (P.poissonized_event_bounds q _ X.1).2.trans (le_add_of_nonneg_right (Real.exp_pos _).le)
    · rw [competition_window_bad_poisson eps k r delta hV heps hk hr hd q hq hb X.1 hg]
      simp [FiniteKernel.eventIndicator,hg,competitionMonitorBad,hp,(Real.exp_pos _).le]

end
end RandomViability.Binding

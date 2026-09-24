import proofs.RandomViability.BindingCompetitionFailureDecomposition

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped NNReal
variable {V C : ℕ}

theorem competition_monitor_steps_mono (P : FiniteKernel (CompetitionWindowState V C)) (t : ℝ≥0)
    (f g : CompetitionMonitorState V C → ℝ) (hf : ∀ X, 0 ≤ f X) (hg : ∀ X, 0 ≤ g X)
    (hfg : ∀ X, f X ≤ g X) (n : ℕ) (X : CompetitionMonitorState V C) :
    competitionMonitorSteps P t n f X ≤ competitionMonitorSteps P t n g X := by
  induction n generalizing X with
  | zero => exact hfg X
  | succ n ih =>
    exact P.poissonized_mono t _ _
      (fun Y => competition_monitor_steps_nonneg P t f hf n _)
      (fun Y => competition_monitor_steps_nonneg P t g hg n _)
      (fun Y => ih (competitionWindowBoundary Y X.2)) X.1

theorem competition_monitor_steps_add (P : FiniteKernel (CompetitionWindowState V C)) (t : ℝ≥0)
    (f g : CompetitionMonitorState V C → ℝ) (hf : ∀ X, 0 ≤ f X) (hg : ∀ X, 0 ≤ g X)
    (n : ℕ) (X : CompetitionMonitorState V C) :
    competitionMonitorSteps P t n (fun Y => f Y+g Y) X =
      competitionMonitorSteps P t n f X+competitionMonitorSteps P t n g X := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih =>
    change P.poissonized t (fun Y => competitionMonitorSteps P t n (fun Z => f Z+g Z)
      (competitionWindowBoundary Y X.2)) X.1 = _
    simp_rw [ih]
    exact P.poissonized_add t _ _
      (fun Y => competition_monitor_steps_nonneg P t f hf n _)
      (fun Y => competition_monitor_steps_nonneg P t g hg n _) X.1

theorem competition_monitor_steps_const (P : FiniteKernel (CompetitionWindowState V C)) (t : ℝ≥0)
    (c : ℝ) (n : ℕ) (X : CompetitionMonitorState V C) :
    competitionMonitorSteps P t n (fun _ => c) X = c := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih =>
    change P.poissonized t (fun Y => competitionMonitorSteps P t n (fun _ => c)
      (competitionWindowBoundary Y X.2)) X.1 = c
    simp_rw [ih]
    exact P.poissonized_const t c X.1

end
end RandomViability.Binding

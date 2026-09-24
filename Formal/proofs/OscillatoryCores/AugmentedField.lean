import proofs.OscillatoryCores.SmoothBlowup
import proofs.OscillatoryCores.CutoffFlow

namespace OscillatoryCores

open scoped ContDiff NNReal

/-- Source parameter, amplitude, period, and normalized displacement. -/
abbrev ShootingState := ℝ × ℝ × ℝ × State

noncomputable def augmentedField (p : ShootingState) : ShootingState :=
  (0,0,0,p.2.2.1 • amplitudeField p.1 p.2.1 p.2.2.2)

theorem augmentedField_contDiff : ContDiff ℝ ∞ augmentedField := by
  have hp : ContDiff ℝ ∞ (fun p : ShootingState => (p.1,p.2.1,p.2.2.2)) := by fun_prop
  have hG : ContDiff ℝ ∞ (fun p : ShootingState => amplitudeField p.1 p.2.1 p.2.2.2) :=
    amplitudeField_contDiff.comp hp
  exact contDiff_const.prodMk (contDiff_const.prodMk
    (contDiff_const.prodMk ((by fun_prop : ContDiff ℝ ∞ (fun p : ShootingState => p.2.2.1)).smul hG)))

/-- An actual C1 shooting flow for a localized version of the literal
amplitude field. The equality region is stated explicitly for later transport. -/
theorem augmented_cutoff_flow (c : ShootingState) {R : ℝ} (hR : 0 < R) :
    ∃ g : ShootingState → ShootingState,
      (∀ x ∈ Metric.closedBall c R, g x = augmentedField x) ∧
      ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      ∃ Φ : ℝ → ShootingState → ShootingState,
        (∀ x, Φ 0 x = x) ∧
        (∀ x t, HasDerivAt (fun s => Φ s x) (g (Φ t x)) t) ∧
        (∀ T : ℝ≥0, ContDiff ℝ 1 (Φ T)) ∧
        (∀ s t x, Φ s (Φ t x) = Φ (t+s) x) ∧
        Continuous (fun p : ℝ × ShootingState => Φ p.1 p.2) :=
  smooth_field_cutoff_c1_flow augmentedField augmentedField_contDiff c hR

end OscillatoryCores

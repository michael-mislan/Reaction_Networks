import proofs.RandomViability.ExponentialResolvent
import Mathlib.Analysis.SpecificLimits.Basic

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
noncomputable section
set_option maxHeartbeats 30000
variable {S : Type*} [MeasurableSpace S]

/-- Comparison of nonnegative renewal solutions under an explicit half-weight integral bound. -/
theorem weighted_half_renewal_le (μ : S → Measure S) (F G B : S → ℝ≥0∞) (w : S → ℝ)
    (hG : Measurable G) (hw : Measurable w)
    (hFw : ∀ x, F x ≤ ENNReal.ofReal (w x))
    (hF : ∀ x, F x = B x + ∫⁻ y, F y ∂μ x)
    (hGeq : ∀ x, G x = B x + ∫⁻ y, G y ∂μ x)
    (hweight : ∀ x, (∫⁻ y, ENNReal.ofReal (w y) ∂μ x) ≤
      ENNReal.ofReal (1/2 : ℝ)*ENNReal.ofReal (w x)) : ∀ x, F x ≤ G x := by
  have hi : ∀ n : ℕ, ∀ x, F x ≤ G x + ENNReal.ofReal ((1/2 : ℝ)^n)*ENNReal.ofReal (w x) := by
    intro n
    induction n with
    | zero =>
      intro x
      simpa only [pow_zero, ENNReal.ofReal_one, one_mul, zero_add] using
        add_le_add (show (0 : ℝ≥0∞) ≤ G x from bot_le) (hFw x)
    | succ n ih =>
      intro x
      calc
        F x = B x + ∫⁻ y, F y ∂μ x := hF x
        _ ≤ B x + ∫⁻ y, G y + ENNReal.ofReal ((1/2 : ℝ)^n)*ENNReal.ofReal (w y) ∂μ x :=
          add_le_add le_rfl (lintegral_mono ih)
        _ = G x + ENNReal.ofReal ((1/2 : ℝ)^n)*(∫⁻ y, ENNReal.ofReal (w y) ∂μ x) := by
          rw [lintegral_add_left hG, lintegral_const_mul _ hw.ennreal_ofReal, ← add_assoc, ← hGeq x]
        _ ≤ G x + ENNReal.ofReal ((1/2 : ℝ)^n)*
            (ENNReal.ofReal (1/2 : ℝ)*ENNReal.ofReal (w x)) := by
          gcongr
          exact hweight x
        _ = G x + ENNReal.ofReal ((1/2 : ℝ)^(n+1))*ENNReal.ofReal (w x) := by
          rw [pow_succ, ENNReal.ofReal_mul (by positivity)]
          ac_rfl
  intro x
  have hr : Tendsto (fun n : ℕ => (1/2 : ℝ)^n*w x) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
        (by norm_num : (1/2 : ℝ) < 1)).mul_const (w x)
  have he := (ENNReal.continuous_ofReal.tendsto 0).comp hr
  have hl : Tendsto (fun n : ℕ => G x + ENNReal.ofReal ((1/2 : ℝ)^n)*ENNReal.ofReal (w x))
      atTop (𝓝 (G x)) := by
    simp_rw [← ENNReal.ofReal_mul (show 0 ≤ (1/2 : ℝ)^_ from by positivity)]
    simpa only [ENNReal.ofReal_zero, add_zero] using tendsto_const_nhds.add he
  exact ge_of_tendsto hl (Eventually.of_forall (fun n => hi n x))

/-- The common inhomogeneous term and a contracting finite weight determine the solution. -/
theorem weighted_half_renewal_unique (μ : S → Measure S) (F G B : S → ℝ≥0∞) (w : S → ℝ)
    (hFm : Measurable F) (hGm : Measurable G) (hw : Measurable w)
    (hFw : ∀ x, F x ≤ ENNReal.ofReal (w x)) (hGw : ∀ x, G x ≤ ENNReal.ofReal (w x))
    (hF : ∀ x, F x = B x + ∫⁻ y, F y ∂μ x)
    (hG : ∀ x, G x = B x + ∫⁻ y, G y ∂μ x)
    (hweight : ∀ x, (∫⁻ y, ENNReal.ofReal (w y) ∂μ x) ≤
      ENNReal.ofReal (1/2 : ℝ)*ENNReal.ofReal (w x)) : F = G := by
  funext x
  exact le_antisymm (weighted_half_renewal_le μ F G B w hGm hw hFw hF hG hweight x)
    (weighted_half_renewal_le μ G F B w hFm hw hGw hG hF hweight x)

end
end RandomViability

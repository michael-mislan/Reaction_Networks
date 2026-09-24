import proofs.OptimalAffinityRealizability.RoutingStationary

namespace OptimalAffinityRealizability

noncomputable section

/-- Boundary ratios approach one along a positive directional profile. -/
def boundaryRatio {n : ℕ} (epsilon : ℝ) (r : Fin n → ℝ) : Fin n → ℝ :=
  fun i => 1 + epsilon * r i

theorem boundaryRatio_gt_one {n : ℕ} (epsilon : ℝ) (r : Fin n → ℝ)
    (hepsilon : 0 < epsilon) (hr : ∀ i, 0 < r i) :
    ∀ i, 1 < boundaryRatio epsilon r i := by
  intro i
  simp only [boundaryRatio]
  exact lt_add_of_pos_right 1 (mul_pos hepsilon (hr i))

/-- With current gauge `J = epsilon` and `q_i = 1 + epsilon r_i`,
reverse one-way flows are exactly constant rather than blowing up. -/
theorem reconstructedReverseFlow_boundaryGauge {n : ℕ}
    (epsilon : ℝ) (production r : Fin n → ℝ)
    (hepsilon : epsilon ≠ 0) (hr : ∀ i, r i ≠ 0) :
    ∀ i, reconstructedReverseFlow epsilon production
      (boundaryRatio epsilon r) i = production i / r i := by
  intro i
  unfold reconstructedReverseFlow
    OptimalAffinityCorrected.reconstructedReverseFlux boundaryRatio
  field_simp [hepsilon, hr i]
  ring

/-- The corresponding forward flow remains affine in epsilon and converges
to the same finite boundary value. -/
theorem reconstructedForwardFlow_boundaryGauge {n : ℕ}
    (epsilon : ℝ) (production r : Fin n → ℝ)
    (hepsilon : epsilon ≠ 0) (hr : ∀ i, r i ≠ 0) :
    ∀ i, reconstructedForwardFlow epsilon production
      (boundaryRatio epsilon r) i =
        (1 + epsilon * r i) * (production i / r i) := by
  intro i
  unfold reconstructedForwardFlow
    OptimalAffinityCorrected.reconstructedForwardFlux boundaryRatio
  field_simp [hepsilon, hr i]
  ring

theorem boundaryRatio_tendsto_one {n : ℕ} (r : Fin n → ℝ) :
    Filter.Tendsto (fun epsilon => boundaryRatio epsilon r)
      (nhds 0) (nhds 1) := by
  have hc : Continuous (fun epsilon : ℝ => boundaryRatio epsilon r) := by
    unfold boundaryRatio
    fun_prop
  have hc0 : ContinuousAt (fun epsilon : ℝ => boundaryRatio epsilon r) 0 :=
    hc.continuousAt
  change Filter.Tendsto (fun epsilon : ℝ => boundaryRatio epsilon r)
    (nhds 0) (nhds (boundaryRatio 0 r)) at hc0
  have hzero : boundaryRatio 0 r = 1 := by
    funext i
    simp [boundaryRatio]
  rw [hzero] at hc0
  exact hc0

theorem boundaryForwardFlow_tendsto_finite {n : ℕ}
    (production r : Fin n → ℝ) (i : Fin n) :
    Filter.Tendsto
      (fun epsilon => (1 + epsilon * r i) * (production i / r i))
      (nhds 0) (nhds (production i / r i)) := by
  have hc : Continuous
      (fun epsilon : ℝ => (1 + epsilon * r i) * (production i / r i)) := by
    fun_prop
  have hc0 : ContinuousAt
      (fun epsilon : ℝ => (1 + epsilon * r i) * (production i / r i)) 0 :=
    hc.continuousAt
  change Filter.Tendsto
    (fun epsilon : ℝ => (1 + epsilon * r i) * (production i / r i))
    (nhds 0) (nhds ((1 + 0 * r i) * (production i / r i))) at hc0
  simpa using hc0

end
end OptimalAffinityRealizability

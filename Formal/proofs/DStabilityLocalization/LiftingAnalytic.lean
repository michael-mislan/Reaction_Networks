import proofs.DStabilityLocalization.RealEigenvalues

/-!
# Complex-analytic tools for lifting (node N6)

* `differentiableAt_det`: the determinant of a matrix of holomorphic entries is holomorphic.
* `exists_sphere_ne`: a holomorphic function on a connected open set that is not identically
  zero has, around any point, arbitrarily small circles free of zeros (isolated zeros).
* `hurwitz_zero`: if `Φ ε z` is jointly continuous on `[0,1] × closedBall z₀ ρ`, holomorphic in
  `z`, `Φ 0 z₀ = 0` and `Φ 0` has no zero on the circle, then `Φ ε` has a zero in the closed
  ball for some `ε ∈ (0,1]` (Hurwitz's theorem, via the maximum modulus principle).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section
open Matrix Complex Set Filter Topology Metric
open scoped BigOperators

namespace DStabilityLocalization

theorem differentiableAt_det {n : Type*} [Fintype n] [DecidableEq n] (M : ℂ → Matrix n n ℂ)
    (z : ℂ) (h : ∀ i j, DifferentiableAt ℂ (fun w => M w i j) z) :
    DifferentiableAt ℂ (fun w => (M w).det) z := by
  simp_rw [Matrix.det_apply]
  refine DifferentiableAt.fun_sum (fun σ _ => ?_)
  simp_rw [Units.smul_def]
  refine DifferentiableAt.const_smul ?_ _
  exact DifferentiableAt.fun_finsetProd (fun i _ => h (σ i) i)

theorem continuousOn_det {X n : Type*} [TopologicalSpace X] [Fintype n] [DecidableEq n]
    (M : X → Matrix n n ℂ) (S : Set X) (h : ∀ i j, ContinuousOn (fun x => M x i j) S) :
    ContinuousOn (fun x => (M x).det) S := by
  have hM : ContinuousOn M S := continuousOn_pi.mpr (fun i => continuousOn_pi.mpr (h i))
  exact (continuous_id.matrix_det).comp_continuousOn hM

/-- Isolated zeros: small zero-free circles around any point. -/
theorem exists_sphere_ne {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hg : DifferentiableOn ℂ g U) {z₀ z₁ : ℂ} (h₀ : z₀ ∈ U) (h₁ : z₁ ∈ U) (hg1 : g z₁ ≠ 0)
    (R : ℝ) (hR : 0 < R) : ∃ ρ, 0 < ρ ∧ ρ < R ∧ ∀ z ∈ sphere z₀ ρ, g z ≠ 0 := by
  have han : AnalyticOnNhd ℂ g U := (analyticOnNhd_iff_differentiableOn hU).mpr hg
  rcases (han z₀ h₀).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc h₀ h h₁
    exact hg1 this
  · rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
    obtain ⟨ρ₁, hρ₁, hball⟩ := h
    refine ⟨min ρ₁ R / 2, by positivity, by
      have := min_le_right ρ₁ R; linarith, fun z hz => ?_⟩
    have hd : dist z z₀ = min ρ₁ R / 2 := mem_sphere.mp hz
    apply hball
    · rw [hd]; have := min_le_left ρ₁ R; linarith [lt_min hρ₁ hR]
    · intro heq
      rw [heq, dist_self] at hd
      have : 0 < min ρ₁ R / 2 := by positivity
      linarith

/-- **Hurwitz's theorem** in the form used for lifting. -/
theorem hurwitz_zero {Φ : ℝ → ℂ → ℂ} {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hcont : ContinuousOn (fun x : ℝ × ℂ => Φ x.1 x.2) (Icc (0 : ℝ) 1 ×ˢ closedBall z₀ ρ))
    (hdiff : ∀ ε ∈ Icc (0 : ℝ) 1, ∀ z ∈ closedBall z₀ ρ, DifferentiableAt ℂ (Φ ε) z)
    (hz₀ : Φ 0 z₀ = 0) (hsph : ∀ z ∈ sphere z₀ ρ, Φ 0 z ≠ 0) :
    ∃ ε ∈ Ioc (0 : ℝ) 1, ∃ z ∈ closedBall z₀ ρ, Φ ε z = 0 := by
  -- minimum of |Φ 0| on the circle
  have hsne : (sphere z₀ ρ).Nonempty := NormedSpace.sphere_nonempty.mpr hρ.le
  have hc0 : ContinuousOn (fun z => ‖Φ 0 z‖) (sphere z₀ ρ) := by
    have : ContinuousOn (fun z => Φ 0 z) (closedBall z₀ ρ) := by
      have h2 : ContinuousOn (fun z : ℂ => ((0 : ℝ), z)) (closedBall z₀ ρ) :=
        (continuous_const.prodMk continuous_id).continuousOn
      refine (hcont.comp h2 (fun z hz => ⟨⟨le_refl _, zero_le_one⟩, hz⟩))
    exact (this.mono sphere_subset_closedBall).norm
  obtain ⟨w, hw, hwmin⟩ := (isCompact_sphere z₀ ρ).exists_isMinOn hsne hc0
  set m := ‖Φ 0 w‖ with hm
  have hmpos : 0 < m := norm_pos_iff.mpr (hsph w hw)
  -- uniform continuity on the compact product
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ closedBall z₀ ρ) :=
    isCompact_Icc.prod (isCompact_closedBall z₀ ρ)
  have huc := hK.uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδc⟩ := huc (m / 2) (by linarith)
  set ε₁ := min (δ / 2) 1 with hε₁
  have hε₁pos : 0 < ε₁ := lt_min (by linarith) one_pos
  have hε₁le : ε₁ ≤ 1 := min_le_right _ _
  have hclose : ∀ z ∈ closedBall z₀ ρ, ‖Φ ε₁ z - Φ 0 z‖ < m / 2 := by
    intro z hz
    have hd : dist ((ε₁, z) : ℝ × ℂ) ((0 : ℝ), z) < δ := by
      rw [Prod.dist_eq, dist_self, Real.dist_eq, sub_zero, abs_of_pos hε₁pos]
      have : ε₁ ≤ δ / 2 := min_le_left _ _
      rw [max_eq_left (le_of_lt hε₁pos)]
      linarith
    have := hδc (ε₁, z) ⟨⟨hε₁pos.le, hε₁le⟩, hz⟩ (0, z) ⟨⟨le_refl _, zero_le_one⟩, hz⟩ hd
    rwa [dist_eq_norm] at this
  refine ⟨ε₁, ⟨hε₁pos, hε₁le⟩, ?_⟩
  by_contra hno
  push Not at hno
  -- maximum modulus for 1 / Φ ε₁
  set f : ℂ → ℂ := fun z => (Φ ε₁ z)⁻¹ with hf
  have hfd : DifferentiableOn ℂ f (closedBall z₀ ρ) := by
    intro z hz
    exact ((hdiff ε₁ ⟨hε₁pos.le, hε₁le⟩ z hz).inv (hno z hz)).differentiableWithinAt
  have hdc : DiffContOnCl ℂ f (ball z₀ ρ) := hfd.diffContOnCl_ball (subset_refl _)
  have hbound : ∀ z ∈ frontier (ball z₀ ρ), ‖f z‖ ≤ 2 / m := by
    intro z hz
    rw [frontier_ball z₀ hρ.ne'] at hz
    have h1 : m ≤ ‖Φ 0 z‖ := hwmin hz
    have h2 := hclose z (sphere_subset_closedBall hz)
    have h3 : m / 2 ≤ ‖Φ ε₁ z‖ := by
      have := norm_sub_norm_le (Φ 0 z) (Φ 0 z - Φ ε₁ z)
      rw [sub_sub_cancel, norm_sub_rev] at this
      linarith
    simp only [hf, norm_inv]
    rw [inv_le_comm₀ (by linarith) (by positivity)]
    linarith [show (2 / m)⁻¹ = m / 2 by field_simp]
  have hz0 := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc hbound
    (subset_closure (mem_ball_self hρ))
  have h4 : ‖Φ ε₁ z₀‖ < m / 2 := by
    have := hclose z₀ (mem_closedBall_self hρ.le)
    rwa [hz₀, sub_zero] at this
  simp only [hf, norm_inv] at hz0
  have hpos : 0 < ‖Φ ε₁ z₀‖ := norm_pos_iff.mpr (hno z₀ (mem_closedBall_self hρ.le))
  rw [inv_le_comm₀ hpos (by positivity)] at hz0
  have : (2 / m)⁻¹ = m / 2 := by field_simp
  linarith

end DStabilityLocalization

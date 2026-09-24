import proofs.OscillatoryCores.AugmentedField

namespace OscillatoryCores

open Set Filter
open scoped Topology ContDiff NNReal

/-- Uniform localization on the complete unit-time shooting segment. -/
theorem eventually_unit_curve_in_ball
    {P : Type*} [TopologicalSpace P] (y : P → ℝ → ShootingState)
    (p : P) (c : ShootingState) (R : ℝ)
    (hy : ∀ s ∈ Icc (0 : ℝ) 1, ContinuousAt (fun q : P × ℝ => y q.1 q.2) (p,s))
    (hb : ∀ s ∈ Icc (0 : ℝ) 1, y p s ∈ Metric.ball c R) :
    ∀ᶠ q in 𝓝 p, ∀ s ∈ Icc (0 : ℝ) 1, y q s ∈ Metric.ball c R := by
  apply isCompact_Icc.eventually_forall_of_forall_eventually
  intro s hs
  exact (hy s hs).eventually (Metric.isOpen_ball.mem_nhds (hb s hs))

/-- An explicit original-field curve inside the equality ball agrees with
the constructed cutoff flow, so its endpoint identities and derivatives
can be transported to the actual C1 shooting map. -/
theorem localized_curve_eq_flow
    (g : ShootingState → ShootingState) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (Φ : ℝ → ShootingState → ShootingState)
    (hΦ0 : ∀ x, Φ 0 x=x)
    (hΦ : ∀ x t, HasDerivAt (fun s => Φ s x) (g (Φ t x)) t)
    (c : ShootingState) (R : ℝ)
    (hge : ∀ x ∈ Metric.closedBall c R, g x=augmentedField x)
    (y : ℝ → ShootingState)
    (hy : ∀ s, HasDerivAt y (augmentedField (y s)) s)
    (hb : ∀ s ∈ Icc (0 : ℝ) 1, y s ∈ Metric.closedBall c R) :
    ∀ s ∈ Icc (0 : ℝ) 1, Φ s (y 0)=y s := by
  obtain ⟨K,hK⟩ := compact_field_lipschitz g hg hgc
  apply ODE_solution_unique_of_mem_Icc_right
    (v := fun _ x => g x) (s := fun _ => Set.univ) (K := K)
  · intro s _
    exact hK.lipschitzOnWith
  · exact (continuous_iff_continuousAt.mpr (fun s => (hΦ (y 0) s).continuousAt)).continuousOn
  · intro s _
    exact (hΦ (y 0) s).hasDerivWithinAt
  · intro s _
    exact Set.mem_univ _
  · exact (continuous_iff_continuousAt.mpr (fun s => (hy s).continuousAt)).continuousOn
  · intro s hs
    rw [hge (y s) (hb s ⟨hs.1,hs.2.le⟩)]
    exact (hy s).hasDerivWithinAt
  · intro s _
    exact Set.mem_univ _
  · exact hΦ0 (y 0)

theorem localized_family_endpoint
    {P : Type*} [TopologicalSpace P] (p : P)
    (g : ShootingState → ShootingState) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (Φ : ℝ → ShootingState → ShootingState)
    (hΦ0 : ∀ x, Φ 0 x=x)
    (hΦ : ∀ x t, HasDerivAt (fun s => Φ s x) (g (Φ t x)) t)
    (c : ShootingState) (R : ℝ)
    (hge : ∀ x ∈ Metric.closedBall c R, g x=augmentedField x)
    (y : P → ℝ → ShootingState)
    (hyc : ∀ s ∈ Icc (0 : ℝ) 1, ContinuousAt (fun q : P × ℝ => y q.1 q.2) (p,s))
    (hy : ∀ᶠ q in 𝓝 p, ∀ s, HasDerivAt (y q) (augmentedField (y q s)) s)
    (hb : ∀ s ∈ Icc (0 : ℝ) 1, y p s ∈ Metric.ball c R) :
    ∀ᶠ q in 𝓝 p, Φ 1 (y q 0)=y q 1 := by
  have htube := eventually_unit_curve_in_ball y p c R hyc hb
  filter_upwards [htube,hy] with q hq hqy
  exact localized_curve_eq_flow g hg hgc Φ hΦ0 hΦ c R hge (y q) hqy
    (fun s hs => Metric.ball_subset_closedBall (hq s hs)) 1 ⟨by norm_num,le_rfl⟩

end OscillatoryCores

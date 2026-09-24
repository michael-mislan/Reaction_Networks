import proofs.OverlappingSiphonInvasion.Root

noncomputable section
open Filter Topology
namespace OverlappingSiphonInvasion

theorem trajectory_total_bound (p : Rates) (hp : PositiveRates p)
    (X : ℝ → State) (hX : IsTrajectory p X) :
    ∀ t, 0 ≤ t → total (X t) ≤ sourceRadius p (X 0) := by
  apply CoreCouplingGlobal.scalar_upper_barrier (fun t => total (X t))
    (fun t => p.recruitment-p.mu0*X t 0-p.mu1*X t 1-
      p.mu2*X t 2-p.mu3*X t 3) (sourceRadius p (X 0))
  · intro t ht
    convert (((hX.derivative t ht 0).add (hX.derivative t ht 1)).add
      (hX.derivative t ht 2)).add (hX.derivative t ht 3) using 1
    exact (total_field p (X t)).symm
  · exact le_max_left _ _
  · intro t ht hlevel
    have hm := deathFloor_pos p hp
    have hb := total_mortality_bound p (X t) (fun i => (hX.positive t ht i).le)
    have hr : p.recruitment/deathFloor p ≤ sourceRadius p (X 0) := by
      have hh := le_max_right (total (X 0)) (p.recruitment/deathFloor p+1)
      dsimp [sourceRadius]
      linarith
    have hmR := (div_le_iff₀ hm).mp hr
    have hmN := mul_le_mul_of_nonneg_left hlevel hm.le
    nlinarith only [hb,hmR,hmN]

/-- Uniqueness on the forward time domain; values at negative times are irrelevant. -/
theorem positive_trajectory_unique (p : Rates) (hp : PositiveRates p)
    (X Y : ℝ → State) (hX : IsTrajectory p X) (hY : IsTrajectory p Y)
    (h0 : X 0 = Y 0) : ∀ t, 0 ≤ t → X t = Y t := by
  apply bounded_source_unique p (sourceRadius p (X 0)) X Y
    (fun t ht => hasDerivAt_pi.2 (hX.derivative t ht))
    (fun t ht => hasDerivAt_pi.2 (hY.derivative t ht))
  · exact fun t ht => ⟨fun i => (hX.positive t ht i).le,
      trajectory_total_bound p hp X hX t ht⟩
  · intro t ht
    refine ⟨fun i => (hY.positive t ht i).le,?_⟩
    simpa only [h0] using trajectory_total_bound p hp Y hY t ht
  · exact h0

/-- The publication endpoint: one floor for every positive trajectory, together
with positive global existence and uniqueness for each positive initial state. -/
theorem publication_permanence (p : Rates) (hp : PositiveRates p)
    (he1 : p.mu1/p.alpha1 < p.recruitment/p.mu0)
    (he2 : p.mu2/p.alpha2 < p.recruitment/p.mu0) (hi : StrictMutualInvasion p) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ X : ℝ → State, IsTrajectory p X →
        ∀ᶠ t in atTop, ∀ i, ε ≤ X t i ∧ X t i ≤ p.recruitment/deathFloor p+1) ∧
      (∀ x0 : State, (∀ i, 0 < x0 i) →
        ∃ X : ℝ → State, X 0 = x0 ∧ IsTrajectory p X ∧
          ∀ Y : ℝ → State, Y 0 = x0 → IsTrajectory p Y →
            ∀ t, 0 ≤ t → Y t = X t) := by
  obtain ⟨ε,hε,hfloor⟩ := general_trajectory_permanence p hp he1 he2 hi
  refine ⟨ε,hε,hfloor,?_⟩
  intro x0 hx0
  obtain ⟨X,hX0,hX⟩ := general_positive_global p hp x0 hx0
  refine ⟨X,hX0,hX,?_⟩
  intro Y hY0 hY
  exact positive_trajectory_unique p hp Y X hY hX (hY0.trans hX0.symm)

end OverlappingSiphonInvasion

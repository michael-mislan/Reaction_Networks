import proofs.OverlappingSiphonInvasion.SourceProductFloor

noncomputable section
open Set Filter Topology
namespace OverlappingSiphonInvasion

theorem normalized_trajectory_unique (p : Rates) (ru rv rj R : ℝ)
    (hru : 0 < ru) (hrv : 0 < rv) (hrj : 0 < rj) (X Y : ℝ → LiftState)
    (hX : ∀ t, 0 ≤ t → X t ∈ physicalLiftClosure ru rv rj R)
    (hY : ∀ t, 0 ≤ t → Y t ∈ physicalLiftClosure ru rv rj R)
    (hdX : ∀ t, 0 ≤ t → HasDerivAt X (normalizedField p ru rv rj (X t)) t)
    (hdY : ∀ t, 0 ≤ t → HasDerivAt Y (normalizedField p ru rv rj (Y t)) t)
    (h0 : X 0 = Y 0) (t : ℝ) (ht : 0 ≤ t) : X t = Y t := by
  obtain ⟨K,hK⟩ := (normalizedField_contDiff p ru rv rj).contDiffOn.exists_lipschitzOnWith
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0) (convex_closedBall (0:LiftState) (max R 1))
    (isCompact_closedBall (0:LiftState) (max R 1))
  have hmX : ∀ s ∈ Ico (0:ℝ) t, X s ∈ Metric.closedBall (0:LiftState) (max R 1) := by
    intro s hs
    simpa only [Metric.mem_closedBall,dist_zero_right] using
      physicalLiftClosure_norm_le ru rv rj R hru hrv hrj (X s) (hX s hs.1)
  have hmY : ∀ s ∈ Ico (0:ℝ) t, Y s ∈ Metric.closedBall (0:LiftState) (max R 1) := by
    intro s hs
    simpa only [Metric.mem_closedBall,dist_zero_right] using
      physicalLiftClosure_norm_le ru rv rj R hru hrv hrj (Y s) (hY s hs.1)
  have hh := dist_le_of_trajectories_ODE_of_mem (v := fun _ => normalizedField p ru rv rj)
    (s := fun _ => Metric.closedBall (0:LiftState) (max R 1)) (fun _ _ => hK)
    (fun s hs => (hdX s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hdX s hs.1).hasDerivWithinAt) hmX
    (fun s hs => (hdY s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hdY s hs.1).hasDerivWithinAt) hmY
    (le_refl (dist (X 0) (Y 0))) t ⟨ht,le_rfl⟩
  apply dist_le_zero.mp
  simpa only [h0,dist_self,zero_mul] using hh

/-- The uniform floor applies to every original positive source trajectory,
after its source-derived absorbing time. There is no boundedness, convergence,
or eventual-floor premise in the trajectory input. -/
theorem source_trajectory_product_floor (p : Rates) (hp : PositiveRates p)
    (he1 : p.mu1/p.alpha1 < p.recruitment/p.mu0)
    (he2 : p.mu2/p.alpha2 < p.recruitment/p.mu0) (hi : StrictMutualInvasion p) :
    ∃ ru rv rj : ℝ, ∃ k : ℕ, ∃ δ : ℝ,
      0 < ru ∧ 0 < rv ∧ 0 < rj ∧ 0 < k ∧ 0 < δ ∧
      ∀ X : ℝ → State, IsTrajectory p X → ∀ᶠ t in atTop,
        δ ≤ massU ru (X t)*massV rv (X t)*massJ rj (X t)^k := by
  let R := p.recruitment/deathFloor p+1
  obtain ⟨ru,rv,rj,k,δ,Φ,hru,hrv,hrj,hk,hδ,hΦ0,hflow,hfloor⟩ :=
    source_flow_product_floor p hp he1 he2 hi R le_rfl
  refine ⟨ru,rv,rj,k,δ,hru,hrv,hrj,hk,hδ,?_⟩
  intro X hX
  obtain ⟨T,hT⟩ := eventually_atTop.1
    ((general_eventual_total_upper p hp X hX).and (eventually_ge_atTop (0:ℝ)))
  have hT0 := (hT T le_rfl).2
  let Y : ℝ → State := fun t => X (t+T)
  let Z : ℝ → LiftState := fun t => normalizedEmbedding ru rv rj (Y t)
  have hpY : ∀ t, 0 ≤ t → ∀ i, 0 < Y t i :=
    fun t ht => hX.positive (t+T) (by linarith)
  have hdY : ∀ t, 0 ≤ t → HasDerivAt Y (field p (Y t)) t := by
    intro t ht
    have hh : HasDerivAt X (field p (X (t+T))) (t+T) :=
      hasDerivAt_pi.2 (hX.derivative (t+T) (by linarith))
    simpa [Y] using hh.scomp t ((hasDerivAt_id t).add_const T)
  have hZ : ∀ t, 0 ≤ t → Z t ∈ physicalLiftClosure ru rv rj R := by
    intro t ht
    apply subset_closure
    exact ⟨Y t,⟨hpY t ht,(hT (t+T) (by linarith)).1.le⟩,rfl⟩
  have hdZ : ∀ t, 0 ≤ t → HasDerivAt Z (normalizedField p ru rv rj (Z t)) t := by
    intro t ht
    obtain ⟨hU,hV,hJ⟩ := positive_masses ru rv rj (Y t) hru hrv hrj (hpY t ht)
    exact normalizedEmbedding_derivative p ru rv rj Y t hru.ne' hrv.ne' hrj.ne'
      hU.ne' hV.ne' hJ.ne' (hdY t ht)
  have hpZ0 : 0 < extinctionProduct ru rv rj k (Z 0) := by
    obtain ⟨hU,hV,hJ⟩ := positive_masses ru rv rj (Y 0) hru hrv hrj (hpY 0 le_rfl)
    change 0 < massU ru (Y 0)*massV rv (Y 0)*massJ rj (Y 0)^k
    positivity
  have heq : ∀ t, 0 ≤ t → Z t = Φ (Z 0) t := by
    intro t ht
    exact normalized_trajectory_unique p ru rv rj R hru hrv hrj Z (Φ (Z 0)) hZ
      (fun s hs => (hflow (Z 0) (hZ 0 le_rfl) s hs).1) hdZ
      (fun s hs => (hflow (Z 0) (hZ 0 le_rfl) s hs).2) (hΦ0 (Z 0)).symm t ht
  have hZfloor : ∀ᶠ t in atTop, δ ≤ extinctionProduct ru rv rj k (Z t) := by
    filter_upwards [hfloor (Z 0) (hZ 0 le_rfl) hpZ0,eventually_ge_atTop (0:ℝ)] with t ht ht0
    rw [heq t ht0]
    exact ht
  have hshift : Tendsto (fun t : ℝ => t-T) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-T) tendsto_id
  simpa only [Z,Y,extinctionProduct,normalizedEmbedding,sub_add_cancel] using hshift.eventually hZfloor

end OverlappingSiphonInvasion

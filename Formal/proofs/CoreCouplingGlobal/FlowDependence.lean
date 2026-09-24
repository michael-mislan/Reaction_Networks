import proofs.CoreCouplingGlobal.PositiveFlow

namespace CoreCouplingGlobal
open CoreCouplingCAC Set

def InBoundedRegion (S W : ℝ) (s : State) : Prop :=
  s.A+s.B ≤ S ∧ s.z+(7/4:ℝ)*s.H ≤ W

theorem bounded_region_forward (e S W : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (hS : 34 ≤ S) (hW : (7/2)*(S+76) ≤ W)
    (X : ℝ → State) (hX : IsPositiveTrajectory e X) (h0 : InBoundedRegion S W (X 0)) :
    ∀ t, 0 ≤ t → InBoundedRegion S W (X t) ∧ ‖encodeState (X t)‖ ≤ max S W := by
  have hSt : ∀ t, 0 ≤ t → (X t).A+(X t).B ≤ S := by
    apply scalar_upper_barrier _ _ S (fun t ht => (hX.dA t ht).add (hX.dB t ht)) h0.1
    intro t ht hlarge
    change S ≤ (X t).A+(X t).B at hlarge
    have hc := total_upper_comparison (X t).A (X t).B (X t).z e (hX.positive t ht).1.le he
    have hm := mul_nonneg (show 0 ≤ 1-e by linarith) (show 0 ≤ (X t).A+(X t).B-34 by linarith)
    nlinarith
  have hWt : ∀ t, 0 ≤ t → (X t).z+(7/4:ℝ)*(X t).H ≤ W := by
    apply scalar_upper_barrier _ _ W
      (fun t ht => (hX.dz t ht).add ((hX.dH t ht).const_mul (7/4))) h0.2
    intro t ht hlarge
    change W ≤ (X t).z+(7/4:ℝ)*(X t).H at hlarge
    have hp := hX.positive t ht
    have hst := hSt t ht
    have hc := weighted_upper_comparison_general (X t).A (X t).B (X t).z (X t).H e S
      (by linarith [hp.2.1]) hp.2.1.le hp.2.2.1.le hp.2.2.2.le
    linarith
  intro t ht
  have hp := hX.positive t ht
  have hs := hSt t ht
  have hw := hWt t ht
  refine ⟨⟨hs,hw⟩,?_⟩
  have hR : 0 ≤ max S W := le_trans (by linarith : 0 ≤ S) (le_max_left _ _)
  apply (pi_norm_le_iff_of_nonneg hR).2
  intro i
  fin_cases i
  · change ‖(X t).A‖ ≤ max S W
    rw [Real.norm_eq_abs,abs_of_pos hp.1]
    linarith [le_max_left S W,hp.2.1]
  · change ‖(X t).B‖ ≤ max S W
    rw [Real.norm_eq_abs,abs_of_pos hp.2.1]
    linarith [le_max_left S W,hp.1]
  · change ‖(X t).z‖ ≤ max S W
    rw [Real.norm_eq_abs,abs_of_pos hp.2.2.1]
    linarith [le_max_right S W,hp.2.2.2]
  · change ‖(X t).H‖ ≤ max S W
    rw [Real.norm_eq_abs,abs_of_pos hp.2.2.2]
    linarith [le_max_right S W,hp.2.2.1,hp.2.2.2]

/-- Uniform dependence on initial concentrations for every bounded initial family.
The bound uses the actual trajectories and applies at every finite forward time. -/
theorem bounded_initial_data_dependence (e S W : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (hS : 34 ≤ S) (hW : (7/2)*(S+76) ≤ W) :
    ∃ K : NNReal, ∀ X Y : ℝ → State, IsPositiveTrajectory e X → IsPositiveTrajectory e Y →
      InBoundedRegion S W (X 0) → InBoundedRegion S W (Y 0) →
      ∀ t, 0 ≤ t → dist (encodeState (X t)) (encodeState (Y t)) ≤
        dist (encodeState (X 0)) (encodeState (Y 0))*Real.exp (K*t) := by
  obtain ⟨K,hK⟩ := (responseVectorField_contDiff e).contDiffOn.exists_lipschitzOnWith
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0) (convex_closedBall (0 : ResponseVector) (max S W))
    (isCompact_closedBall (0 : ResponseVector) (max S W))
  refine ⟨K,?_⟩
  intro X Y hX hY hX0 hY0 t ht
  have hmX : ∀ s ∈ Ico (0:ℝ) t, encodeState (X s) ∈ Metric.closedBall (0:ResponseVector) (max S W) := by
    intro s hs
    simpa only [Metric.mem_closedBall,dist_zero_right] using
      (bounded_region_forward e S W he hu hS hW X hX hX0 s hs.1).2
  have hmY : ∀ s ∈ Ico (0:ℝ) t, encodeState (Y s) ∈ Metric.closedBall (0:ResponseVector) (max S W) := by
    intro s hs
    simpa only [Metric.mem_closedBall,dist_zero_right] using
      (bounded_region_forward e S W he hu hS hW Y hY hY0 s hs.1).2
  have hbound := dist_le_of_trajectories_ODE_of_mem (v := fun _ => responseVectorField e)
    (s := fun _ => Metric.closedBall (0:ResponseVector) (max S W)) (fun _ _ => hK)
    ((positive_trajectory_vector_continuous e X hX).mono (fun _ hs => hs.1))
    (fun s hs => (positive_trajectory_vector_derivative e X hX s hs.1).hasDerivWithinAt) hmX
    ((positive_trajectory_vector_continuous e Y hY).mono (fun _ hs => hs.1))
    (fun s hs => (positive_trajectory_vector_derivative e Y hY s hs.1).hasDerivWithinAt) hmY
    (le_refl (dist (encodeState (X 0)) (encodeState (Y 0)))) t ⟨ht,le_rfl⟩
  simpa only [sub_zero] using hbound

end CoreCouplingGlobal

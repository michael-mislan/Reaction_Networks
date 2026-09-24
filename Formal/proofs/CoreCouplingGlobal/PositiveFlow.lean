import proofs.CoreCouplingGlobal.GlobalConvergence

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter Topology

theorem positive_trajectory_vector_derivative (e : ℝ) (X : ℝ → State)
    (hX : IsPositiveTrajectory e X) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun t => encodeState (X t)) (responseVectorField e (encodeState (X t))) t := by
  apply hasDerivAt_pi.2
  intro i
  fin_cases i
  · exact hX.dA t ht
  · exact hX.dB t ht
  · exact hX.dz t ht
  · exact hX.dH t ht

theorem positive_trajectory_vector_continuous (e : ℝ) (X : ℝ → State)
    (hX : IsPositiveTrajectory e X) : ContinuousOn (fun t => encodeState (X t)) (Ici (0:ℝ)) :=
  fun t ht => (positive_trajectory_vector_derivative e X hX t ht).continuousAt.continuousWithinAt

/-- The polynomial vector field is locally Lipschitz; finite trajectory segments
lie in a common compact ball, where the standard ODE uniqueness theorem applies. -/
theorem positive_trajectory_unique (e : ℝ) (X Y : ℝ → State)
    (hX : IsPositiveTrajectory e X) (hY : IsPositiveTrajectory e Y) (h0 : X 0 = Y 0) :
    ∀ t, 0 ≤ t → X t = Y t := by
  intro t ht
  have hcX : ContinuousOn (fun s => encodeState (X s)) (Icc 0 t) :=
    (positive_trajectory_vector_continuous e X hX).mono (fun _ hs => hs.1)
  have hcY : ContinuousOn (fun s => encodeState (Y s)) (Icc 0 t) :=
    (positive_trajectory_vector_continuous e Y hY).mono (fun _ hs => hs.1)
  have hcompact := (isCompact_Icc.image_of_continuousOn hcX).union
    (isCompact_Icc.image_of_continuousOn hcY)
  obtain ⟨R,hR⟩ := hcompact.isBounded.subset_closedBall (0 : ResponseVector)
  obtain ⟨K,hK⟩ := (responseVectorField_contDiff e).contDiffOn.exists_lipschitzOnWith
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0) (convex_closedBall (0 : ResponseVector) R)
    (isCompact_closedBall (0 : ResponseVector) R)
  have hmX : ∀ s ∈ Ico (0:ℝ) t, encodeState (X s) ∈ Metric.closedBall (0:ResponseVector) R := by
    intro s hs
    exact hR (Or.inl ⟨s,⟨hs.1,hs.2.le⟩,rfl⟩)
  have hmY : ∀ s ∈ Ico (0:ℝ) t, encodeState (Y s) ∈ Metric.closedBall (0:ResponseVector) R := by
    intro s hs
    exact hR (Or.inr ⟨s,⟨hs.1,hs.2.le⟩,rfl⟩)
  have heq := ODE_solution_unique_of_mem_Icc_right (v := fun _ => responseVectorField e)
    (s := fun _ => Metric.closedBall (0:ResponseVector) R) (fun _ _ => hK)
    hcX (fun s hs => (positive_trajectory_vector_derivative e X hX s hs.1).hasDerivWithinAt) hmX
    hcY (fun s hs => (positive_trajectory_vector_derivative e Y hY s hs.1).hasDerivWithinAt) hmY
    (congrArg encodeState h0) ⟨ht,le_rfl⟩
  have hd := congrArg decodeState heq
  simpa only [decode_encodeState] using hd

theorem positive_trajectory_time_shift (e : ℝ) (X : ℝ → State)
    (hX : IsPositiveTrajectory e X) (a : ℝ) (ha : 0 ≤ a) :
    IsPositiveTrajectory e (fun t => X (t+a)) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro t ht
    exact hX.positive (t+a) (by linarith)
  · intro t ht
    simpa using (hX.dA (t+a) (by linarith)).comp t ((hasDerivAt_id t).add_const a)
  · intro t ht
    simpa using (hX.dB (t+a) (by linarith)).comp t ((hasDerivAt_id t).add_const a)
  · intro t ht
    simpa using (hX.dz (t+a) (by linarith)).comp t ((hasDerivAt_id t).add_const a)
  · intro t ht
    simpa using (hX.dH (t+a) (by linarith)).comp t ((hasDerivAt_id t).add_const a)

noncomputable def positiveFlow (e : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (x : {s : State // s.Positive}) : ℝ → State :=
  (positive_global_solution e he hu x x.property).choose

theorem positiveFlow_spec (e : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (x : {s : State // s.Positive}) :
    positiveFlow e he hu x 0 = x ∧ IsPositiveTrajectory e (positiveFlow e he hu x) :=
  (positive_global_solution e he hu x x.property).choose_spec

theorem positiveFlow_eq_trajectory (e : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (x : {s : State // s.Positive}) (X : ℝ → State) (hX : IsPositiveTrajectory e X)
    (h0 : X 0 = x) : ∀ t, 0 ≤ t → positiveFlow e he hu x t = X t :=
  positive_trajectory_unique e _ X (positiveFlow_spec e he hu x).2 hX
    ((positiveFlow_spec e he hu x).1.trans h0.symm)

/-- The selected global positive solution satisfies the forward semigroup law. -/
theorem positiveFlow_add (e : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (x : {s : State // s.Positive}) (a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    positiveFlow e he hu x (t+a) =
      positiveFlow e he hu ⟨positiveFlow e he hu x a,(positiveFlow_spec e he hu x).2.positive a ha⟩ t := by
  have hshift := positive_trajectory_time_shift e (positiveFlow e he hu x)
    (positiveFlow_spec e he hu x).2 a ha
  exact (positiveFlow_eq_trajectory e he hu
    ⟨positiveFlow e he hu x a,(positiveFlow_spec e he hu x).2.positive a ha⟩
    (fun s => positiveFlow e he hu x (s+a)) hshift (by simp) t ht).symm

end CoreCouplingGlobal

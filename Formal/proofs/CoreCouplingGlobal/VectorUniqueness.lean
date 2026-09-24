import proofs.CoreCouplingGlobal.PhysicalUnstable

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter
open scoped Topology ContDiff

theorem smooth_vector_trajectory_unique (f : ResponseVector → ResponseVector)
    (hf : ContDiff ℝ 1 f) (X Y : ℝ → ResponseVector)
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (f (X t)) t)
    (hY : ∀ t, 0 ≤ t → HasDerivAt Y (f (Y t)) t) (h0 : X 0=Y 0) :
    ∀ t, 0 ≤ t → X t=Y t := by
  intro t ht
  have hcX : ContinuousOn X (Icc 0 t) := fun u hu =>
    (hX u hu.1).continuousAt.continuousWithinAt
  have hcY : ContinuousOn Y (Icc 0 t) := fun u hu =>
    (hY u hu.1).continuousAt.continuousWithinAt
  have hcompact := (isCompact_Icc.image_of_continuousOn hcX).union
    (isCompact_Icc.image_of_continuousOn hcY)
  obtain ⟨R,hR⟩ := hcompact.isBounded.subset_closedBall (0 : ResponseVector)
  obtain ⟨K,hK⟩ := hf.contDiffOn.exists_lipschitzOnWith
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0) (convex_closedBall (0 : ResponseVector) R)
    (isCompact_closedBall (0 : ResponseVector) R)
  have hmX : ∀ u ∈ Ico (0:ℝ) t, X u ∈ Metric.closedBall (0:ResponseVector) R := by
    intro u hu
    exact hR (Or.inl ⟨u,⟨hu.1,hu.2.le⟩,rfl⟩)
  have hmY : ∀ u ∈ Ico (0:ℝ) t, Y u ∈ Metric.closedBall (0:ResponseVector) R := by
    intro u hu
    exact hR (Or.inr ⟨u,⟨hu.1,hu.2.le⟩,rfl⟩)
  exact ODE_solution_unique_of_mem_Icc_right (v := fun _ => f)
    (s := fun _ => Metric.closedBall (0:ResponseVector) R) (fun _ _ => hK)
    hcX (fun u hu => (hX u hu.1).hasDerivWithinAt) hmX
    hcY (fun u hu => (hY u hu.1).hasDerivWithinAt) hmY h0 ⟨ht,le_rfl⟩

/-- A reversed trajectory converging to the middle cannot start at a different
stationary state. No equilibrium enumeration is needed for this conclusion. -/
theorem reversed_convergent_nonstationary (e : ℝ) (Y : ℝ → ResponseVector)
    (hY : ∀ t, 0 ≤ t → HasDerivAt Y (-responseVectorField e (Y t)) t)
    (s : State) (hl : Tendsto Y atTop (𝓝 (encodeState s)))
    (hne : Y 0 ≠ encodeState s) :
    ¬ Stationary (flagshipRates e) (decodeState (Y 0)) := by
  intro hss
  have hf0 : responseVectorField e (Y 0)=0 := by
    simpa only [encode_decodeState] using stationary_vectorField_zero e (decodeState (Y 0)) hss
  have hf : ContDiff ℝ 1 (fun x => -responseVectorField e x) :=
    (responseVectorField_contDiff e).neg
  have hconst : ∀ t, 0 ≤ t → HasDerivAt (fun _ : ℝ => Y 0)
      (-responseVectorField e (Y 0)) t := by
    intro t _ht
    simpa [hf0] using hasDerivAt_const t (Y 0)
  have heq := smooth_vector_trajectory_unique _ hf Y (fun _ => Y 0) hY hconst rfl
  have hlim : Tendsto Y atTop (𝓝 (Y 0)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact (heq t ht).symm
  exact hne (tendsto_nhds_unique hlim hl)

end CoreCouplingGlobal

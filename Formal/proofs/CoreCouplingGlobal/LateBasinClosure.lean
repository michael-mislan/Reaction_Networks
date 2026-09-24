import proofs.CoreCouplingGlobal.PositivePerturbations

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter Topology

theorem saddleCoordinates_decode_continuous (e : ℝ) :
    Continuous (fun x : ResponseVector => saddleCoordinates e (decodeState x)) := by
  have hc := responseA_continuous e
  unfold saddleCoordinates decodeState responseTotal
  fun_prop

/-- Every middle-convergent positive trajectory eventually lies in the closure
of each outer basin. This constructs basin points near the trajectory, without
assuming a negative-cone perturbation as an input. -/
theorem middle_trajectory_eventually_two_basin_closures (e : ℝ)
    (hl : (1/200000:ℝ) ≤ e) (hu : e ≤ 1/50000) :
    ∃ low mid high : State, low.Positive ∧ mid.Positive ∧ high.Positive ∧
      Stationary (flagshipRates e) low ∧ Stationary (flagshipRates e) mid ∧
      Stationary (flagshipRates e) high ∧ low.z < mid.z ∧ mid.z < high.z ∧
      ∀ X : ℝ → State, IsPositiveTrajectory e X →
      Tendsto (fun t => encodeState (X t)) atTop (𝓝 (encodeState mid)) →
      ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t →
        encodeState (X t) ∈ closure (positiveBasin e low) ∧
        encodeState (X t) ∈ closure (positiveBasin e high) := by
  obtain ⟨low,mid,high,hlo,hm,hhi,hslo,hsm,hshi,hlm,hmh,η,hη,hnear⟩ :=
    nearby_reference_two_destinations e hl hu
  refine ⟨low,mid,high,hlo,hm,hhi,hslo,hsm,hshi,hlm,hmh,?_⟩
  intro X hX hlim
  have hlimc : Tendsto (fun t => saddleCoordinates e (X t)) atTop
      (𝓝 (saddleCoordinates e mid)) := by
    have hh := (saddleCoordinates_decode_continuous e).continuousAt.tendsto.comp hlim
    simpa only [Function.comp_def,decode_encodeState] using hh
  have hevent := hlimc.eventually (Metric.ball_mem_nhds (saddleCoordinates e mid) hη)
  obtain ⟨N,hN⟩ := eventually_atTop.1 hevent
  refine ⟨max N 0,le_max_right _ _,?_⟩
  intro t ht
  have ht0 : 0 ≤ t := (le_max_right N 0).trans ht
  have htN : N ≤ t := (le_max_left N 0).trans ht
  let W : ℝ → State := fun u => X (u+t)
  have hW : IsPositiveTrajectory e W := positive_trajectory_time_shift e X hX t ht0
  have hstay : ∀ u : ℝ, 0 ≤ u →
      dist (saddleCoordinates e (W u)) (saddleCoordinates e mid) < η := by
    intro u hu0
    exact hN (u+t) (by linarith)
  have hpoints : ∀ ε : ℝ, 0 < ε →
      (∃ y ∈ positiveBasin e low, dist (encodeState (X t)) y < ε) ∧
      (∃ y ∈ positiveBasin e high, dist (encodeState (X t)) y < ε) := by
    intro ε hε
    obtain ⟨Y,Z,hY,hZ,hYε,hZε,hYlim,hZlim⟩ := hnear W hW hstay ε hε
    have hW0 : W 0 = X t := by simp [W]
    constructor
    · refine ⟨encodeState (Y 0),⟨Y,hY,?_,hYlim⟩,?_⟩
      · exact (decode_encodeState (Y 0)).symm
      · simpa only [hW0,dist_comm] using hYε
    · refine ⟨encodeState (Z 0),⟨Z,hZ,?_,hZlim⟩,?_⟩
      · exact (decode_encodeState (Z 0)).symm
      · simpa only [hW0,dist_comm] using hZε
  exact ⟨Metric.mem_closure_iff.2 (fun ε hε => (hpoints ε hε).1),
    Metric.mem_closure_iff.2 (fun ε hε => (hpoints ε hε).2)⟩

/-- The same late-time statement holds for the actual basin boundaries, since
the reference still converges to the distinct middle equilibrium. -/
theorem middle_trajectory_eventually_common_frontier (e : ℝ)
    (hl : (1/200000:ℝ) ≤ e) (hu : e ≤ 1/50000) :
    ∃ low mid high : State, low.Positive ∧ mid.Positive ∧ high.Positive ∧
      Stationary (flagshipRates e) low ∧ Stationary (flagshipRates e) mid ∧
      Stationary (flagshipRates e) high ∧ low.z < mid.z ∧ mid.z < high.z ∧
      ∀ X : ℝ → State, IsPositiveTrajectory e X →
      Tendsto (fun t => encodeState (X t)) atTop (𝓝 (encodeState mid)) →
      ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t →
        encodeState (X t) ∈ frontier (positiveBasin e low) ∧
        encodeState (X t) ∈ frontier (positiveBasin e high) := by
  obtain ⟨low,mid,high,hlo,hm,hhi,hslo,hsm,hshi,hlm,hmh,hclose⟩ :=
    middle_trajectory_eventually_two_basin_closures e hl hu
  refine ⟨low,mid,high,hlo,hm,hhi,hslo,hsm,hshi,hlm,hmh,?_⟩
  intro X hX hlim
  obtain ⟨T,hT,htail⟩ := hclose X hX hlim
  refine ⟨T,hT,?_⟩
  intro t ht
  have ht0 : 0 ≤ t := hT.trans ht
  have hmid : encodeState (X t) ∈ positiveBasin e mid := by
    refine ⟨(fun u => X (u+t)),positive_trajectory_time_shift e X hX t ht0,?_,?_⟩
    · simp only [zero_add,decode_encodeState]
    · exact hlim.comp (tendsto_atTop_add_const_right atTop t tendsto_id)
  have hlne : low ≠ mid := by intro h; rw [h] at hlm; exact (lt_irrefl _ hlm)
  have hhne : high ≠ mid := by intro h; rw [h] at hmh; exact (lt_irrefl _ hmh)
  have hdl := positiveBasins_disjoint e low mid hlne
  have hdh := positiveBasins_disjoint e high mid hhne
  exact ⟨⟨(htail t ht).1,fun hi => Set.disjoint_left.1 hdl (interior_subset hi) hmid⟩,
    ⟨(htail t ht).2,fun hi => Set.disjoint_left.1 hdh (interior_subset hi) hmid⟩⟩

end CoreCouplingGlobal

import proofs.CoreCouplingGlobal.PhysicalAnnulus

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter
open scoped Topology

/-- Middle-convergent trajectories starting sufficiently near the middle remain
in any prescribed neighborhood. This is relative stability of the actual basin,
not stability of the saddle against arbitrary positive perturbations. -/
theorem middle_basin_local_no_return (e : ℝ) (hl : (1/200000:ℝ) ≤ e)
    (hu : e ≤ 1/50000) (s : State) (hs : s.Positive)
    (hss : Stationary (flagshipRates e) s) (hz : s.z ∈ Icc (19/10:ℝ) (21/10))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ X : ℝ → State, IsPositiveTrajectory e X →
      Tendsto (fun t => encodeState (X t)) atTop (𝓝 (encodeState s)) →
      dist (encodeState (X 0)) (encodeState s) < δ →
      ∀ t, 0 ≤ t → dist (encodeState (X t)) (encodeState s) < ε := by
  have he : 0 ≤ e := by linarith
  obtain ⟨r,M,d,hr,hrε,hM,hd,hreg,hspeed,hcost⟩ :=
    middle_physical_annulus e hl hu s hs hss hz ε hε
  obtain ⟨p,_hp⟩ := extendedPotentialPrimitives_nonempty e he hu
  have hbnhds : responseBox ∈ 𝓝 (encodeState s) := by
    apply Filter.mem_of_superset (Metric.ball_mem_nhds (encodeState s) hr)
    intro x hx
    obtain ⟨hpos,hsel⟩ := hreg x (le_of_lt hx)
    exact (responseBox_iff x).2 (positive_selection_response_box (decodeState x) hpos hsel)
  have hVc : ContinuousAt (fun x : ResponseVector => statePotential e p (decodeState x))
      (encodeState s) := (statePotential_continuousOn e p).continuousAt hbnhds
  have hΔ : 0 < d*(r/(2*M)) := by positivity
  obtain ⟨b,hb,hVclose⟩ := Metric.continuousAt_iff.1 hVc (d*(r/(2*M))) hΔ
  refine ⟨min (r/2) b,lt_min (by positivity) hb,?_⟩
  intro X hX hlim hinit t ht
  have hinitr : dist (encodeState (X 0)) (encodeState s) < r/2 :=
    hinit.trans_le (min_le_left _ _)
  have hsel : InSelectionRegion (X 0) := by
    have hh := (hreg (encodeState (X 0)) (by linarith)).2
    simpa only [decode_encodeState] using hh
  have hbox : ∀ t, 0 ≤ t → InResponseBox (X t) :=
    fun t ht => (selection_region_forward e he hu X hX hsel t ht).2
  let V := fun t => statePotential e p (X t)
  have hanti : AntitoneOn V (Ici 0) :=
    trajectory_potential_antitone e p he hu X hX 0 le_rfl hbox
  have hsmem : encodeState s ∈ responseBox := mem_of_mem_nhds hbnhds
  have hwithin : Tendsto (fun t => encodeState (X t)) atTop (𝓝[responseBox] (encodeState s)) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨hlim,?_⟩
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact (responseBox_iff _).2 (by simpa only [decode_encodeState] using hbox t ht)
  have hVlim : Tendsto V atTop (𝓝 (statePotential e p s)) := by
    simpa only [V,Function.comp_apply,decode_encodeState] using
      ((statePotential_continuousOn e p) _ hsmem).tendsto.comp hwithin
  have hlower : ∀ t, 0 ≤ t → statePotential e p s ≤ V t := by
    intro t ht
    apply le_of_tendsto hVlim
    filter_upwards [eventually_ge_atTop t] with u hu
    exact hanti ht (ht.trans hu) hu
  have hbudget : V 0 < statePotential e p s+d*(r/(2*M)) := by
    have hh := hVclose (hinit.trans_le (min_le_right _ _))
    simp only [decode_encodeState,Real.dist_eq] at hh
    have hh' := (abs_lt.1 hh).2
    dsimp [V]
    linarith
  have henergy : ∀ t, 0 ≤ t → ∃ v, HasDerivAt V v t ∧
      v ≤ -responseResidualNorm e (decodeState (encodeState (X t))) := by
    intro t ht
    simpa only [decode_encodeState] using trajectory_energy_derivative e p he hu X hX t ht (hbox t ht)
  have hstay := annular_energy_prevents_exit (responseVectorField e)
    (fun x => responseResidualNorm e (decodeState x)) (fun t => encodeState (X t)) V
    (encodeState s) r M d (statePotential e p s) hr hM
    (positive_trajectory_vector_derivative e X hX) hspeed hcost henergy hanti hlower hinitr hbudget
  exact (hstay t ht).trans hrε

end CoreCouplingGlobal

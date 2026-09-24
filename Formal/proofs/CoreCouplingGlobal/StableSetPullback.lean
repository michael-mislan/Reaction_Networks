import proofs.CoreCouplingGlobal.SpectralCoverage

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter
open scoped Topology ContDiff

/-- Every trajectory converging to the middle eventually reaches the actual
analytic stable patch, and reaching that patch suffices for convergence.
This is the global finite-time pullback characterization; smooth dependence
of the finite-time pullback is a separate geometric statement. -/
theorem middle_convergence_iff_reaches_stable_patch (e : ℝ) (he : 0 ≤ e)
    (hu : e ≤ 1/50000) (s : State) (hs : s.Positive)
    (hss : Stationary (flagshipRates e) s) (hz : s.z ∈ Icc (19/10:ℝ) (21/10)) :
    ∃ μ : Fin 4 → ℝ, ∃ C : ResponseVector ≃L[ℝ] ResponseVector,
      MiddlePerronCoordinates e s μ C ∧ ∃ φ : StableData → ResponseVector,
      ∃ U : Set StableData, IsOpen U ∧ 0 ∈ U ∧ φ 0=encodeState s ∧
        HasFDerivAt φ (C.toContinuousLinearMap.comp stableInclusion) 0 ∧
        ContDiffOn ℝ ω φ U ∧ InjOn φ U ∧
        (∀ ξ ∈ U, middleStableProjection C s (φ ξ)=ξ) ∧
        (∀ ξ ∈ U, φ ξ ∈ positiveBasin e s) ∧
        ∀ X : ℝ → State, IsPositiveTrajectory e X →
          (Tendsto (fun t => encodeState (X t)) atTop (𝓝 (encodeState s)) ↔
            ∃ T : ℝ, 0 ≤ T ∧ ∃ ξ ∈ U, encodeState (X T)=φ ξ) := by
  obtain ⟨μ,C,hC,φ,U,δ,hU,hU0,hδ,hφ0,hder,hcd,hinj,hleft,_htraj,hbasin,hcoverage⟩ :=
    middle_stable_patch_coverage e he hu s hs hss hz
  refine ⟨μ,C,hC,φ,U,hU,hU0,hφ0,hder,hcd,hinj,hleft,hbasin,?_⟩
  intro X hX
  constructor
  · intro hlim
    have hc : Continuous (fun x : ResponseVector => C.symm (x-encodeState s)) :=
      C.symm.continuous.comp (continuous_id.sub continuous_const)
    have ht : Tendsto (fun t => C.symm (encodeState (X t)-encodeState s)) atTop
        (𝓝 (0:ResponseVector)) := by
      simpa using (hc.tendsto (encodeState s)).comp hlim
    have hn : ∀ᶠ t in atTop, ‖C.symm (encodeState (X t)-encodeState s)‖ < δ :=
      ht.norm.eventually_lt_const (by simpa using hδ)
    have hpc : Continuous (fun v : ResponseVector => (fun i : Fin 3 => v i.castSucc)) :=
      continuous_pi fun i => continuous_apply i.castSucc
    have hpt : Tendsto (fun t => middleStableProjection C s (encodeState (X t))) atTop
        (𝓝 (0:StableData)) := by
      exact (hpc.tendsto 0).comp ht
    have hp := hpt.eventually (hU.mem_nhds hU0)
    obtain ⟨T,hTall⟩ := eventually_atTop.1 ((hn.and hp).and (eventually_ge_atTop (0:ℝ)))
    have hT : 0 ≤ T := (hTall T le_rfl).2
    let Z := fun t => encodeState (X (t+T))
    have hZd : ∀ t, 0 ≤ t → HasDerivAt Z (responseVectorField e (Z t)) t :=
      vector_trajectory_forward_shift e (fun t => encodeState (X t))
        (positive_trajectory_vector_derivative e X hX) T hT
    have hZb : ∀ t, 0 ≤ t → ‖C.symm (Z t-encodeState s)‖ < δ := by
      intro t ht0
      exact (hTall (t+T) (by linarith)).1.1
    have hproj : middleStableProjection C s (Z 0) ∈ U := by
      simpa [Z] using (hTall T le_rfl).1.2
    refine ⟨T,hT,middleStableProjection C s (Z 0),hproj,?_⟩
    simpa only [Z,zero_add] using hcoverage Z hZd hZb 0 le_rfl hproj
  · rintro ⟨T,hT,ξ,hξ,harrive⟩
    obtain ⟨Y,hY,hY0,hYlim⟩ := hbasin ξ hξ
    have hshiftX := positive_trajectory_time_shift e X hX T hT
    have hsame : X (0+T)=Y 0 := by
      rw [zero_add,hY0,← harrive,decode_encodeState]
    have heq := positive_trajectory_unique e (fun t => X (t+T)) Y hshiftX hY hsame
    have hevent : (fun t => encodeState (Y t)) =ᶠ[atTop] (fun t => encodeState (X (t+T))) := by
      filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht0
      exact congrArg encodeState (heq t ht0).symm
    have hshift := hYlim.congr' hevent
    have hmap : Tendsto (fun t => encodeState (X t)) (Filter.map (fun t : ℝ => t+T) atTop)
        (𝓝 (encodeState s)) := (tendsto_map'_iff).2 hshift
    simpa only [map_add_atTop_eq] using hmap

end CoreCouplingGlobal

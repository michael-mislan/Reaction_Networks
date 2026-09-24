import proofs.CoreCouplingGlobal.MiddleNoReturn

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter
open scoped Topology ContDiff

/-- The actual middle basin equals the analytic stable graph in an ambient
neighborhood. Coverage now uses no assumed future trapping of a basin point. -/
theorem middle_basin_local_graph (e : ℝ) (hl : (1/200000:ℝ) ≤ e)
    (hu : e ≤ 1/50000) (s : State) (hs : s.Positive)
    (hss : Stationary (flagshipRates e) s) (hz : s.z ∈ Icc (19/10:ℝ) (21/10)) :
    ∃ μ : Fin 4 → ℝ, ∃ C : ResponseVector ≃L[ℝ] ResponseVector,
      MiddlePerronCoordinates e s μ C ∧ ∃ φ : StableData → ResponseVector,
      ∃ U : Set StableData, ∃ N : Set ResponseVector,
      IsOpen U ∧ 0 ∈ U ∧ IsOpen N ∧ encodeState s ∈ N ∧ φ 0=encodeState s ∧
      HasFDerivAt φ (C.toContinuousLinearMap.comp stableInclusion) 0 ∧
      ContDiffOn ℝ ω φ U ∧ InjOn φ U ∧
      (∀ ξ ∈ U, middleStableProjection C s (φ ξ)=ξ) ∧
      (∀ ξ ∈ U, φ ξ ∈ positiveBasin e s) ∧
      ∀ x ∈ N, middleStableProjection C s x ∈ U ∧
        (x ∈ positiveBasin e s ↔ x=φ (middleStableProjection C s x)) := by
  have he : 0 ≤ e := by linarith
  obtain ⟨μ,C,hC,φ,U,δ,hU,hU0,hδ,hφ0,hd,hcd,hinj,hleft,_htraj,hbasin,hcover⟩ :=
    middle_stable_patch_coverage e he hu s hs hss hz
  let K := ‖C.symm.toContinuousLinearMap‖+1
  have hK : 0 < K := by dsimp [K]; positivity
  have hε : 0 < δ/K := div_pos hδ hK
  obtain ⟨r,hr,hstay⟩ := middle_basin_local_no_return e hl hu s hs hss hz (δ/K) hε
  have hp : Continuous (middleStableProjection C s) := by
    apply continuous_pi
    intro i
    exact (continuous_apply i.castSucc).comp
      (C.symm.continuous.comp (continuous_id.sub continuous_const))
  let N := Metric.ball (encodeState s) r ∩ (middleStableProjection C s) ⁻¹' U
  have hN : IsOpen N := Metric.isOpen_ball.inter (hU.preimage hp)
  have hsN : encodeState s ∈ N := by
    constructor
    · simpa only [Metric.mem_ball,dist_self] using hr
    · change middleStableProjection C s (encodeState s) ∈ U
      have hz0 : middleStableProjection C s (encodeState s)=0 := by
        ext i
        simp [middleStableProjection]
      rw [hz0]
      exact hU0
  refine ⟨μ,C,hC,φ,U,N,hU,hU0,hN,hsN,hφ0,hd,hcd,hinj,hleft,hbasin,?_⟩
  intro x hx
  have hpx : middleStableProjection C s x ∈ U := hx.2
  refine ⟨hpx,?_⟩
  constructor
  · rintro ⟨X,hX,hX0,hlim⟩
    have hinit : dist (encodeState (X 0)) (encodeState s) < r := by
      simpa only [hX0,encode_decodeState] using hx.1
    have hsmall := hstay X hX hlim hinit
    have hbound : ∀ t, 0 ≤ t → ‖C.symm (encodeState (X t)-encodeState s)‖ < δ := by
      intro t ht
      have hh := hsmall t ht
      rw [dist_eq_norm] at hh
      calc
        _ ≤ ‖C.symm.toContinuousLinearMap‖*‖encodeState (X t)-encodeState s‖ :=
          C.symm.toContinuousLinearMap.le_opNorm _
        _ ≤ K*‖encodeState (X t)-encodeState s‖ :=
          mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) (norm_nonneg _)
        _ < K*(δ/K) := mul_lt_mul_of_pos_left hh hK
        _ = δ := by field_simp
    have hh := hcover (fun t => encodeState (X t))
      (positive_trajectory_vector_derivative e X hX) hbound 0 le_rfl (by
        simpa only [hX0,encode_decodeState] using hpx)
    simpa only [hX0,encode_decodeState] using hh
  · intro heq
    rw [heq]
    exact hbasin _ hpx

end CoreCouplingGlobal

import proofs.CoreCouplingGlobal.FiniteFlowDifferential
import proofs.CoreCouplingGlobal.BasinBoundary

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter
open scoped Topology ContDiff

/-- Analytic finite-time transport at every positive physical trajectory, with
an invertible derivative and preservation of every positive equilibrium basin.
This binds the endpoint maps to the actual global positive dynamics. -/
theorem positive_finite_analytic_basin_transport (e : ℝ) (he : 0 ≤ e)
    (hu : e ≤ 1/50000) (X : ℝ → State) (hX : IsPositiveTrajectory e X)
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ F R : ResponseVector → ResponseVector,
      F (encodeState (X 0))=encodeState (X T) ∧
      R (encodeState (X T))=encodeState (X 0) ∧
      ContDiffAt ℝ ω F (encodeState (X 0)) ∧
      ContDiffAt ℝ ω R (encodeState (X T)) ∧
      (∀ᶠ x in 𝓝 (encodeState (X 0)), R (F x)=x) ∧
      (∀ᶠ y in 𝓝 (encodeState (X T)), F (R y)=y) ∧
      Function.Bijective (fderiv ℝ F (encodeState (X 0))) ∧
      ∀ᶠ x in 𝓝 (encodeState (X 0)), x ∈ positiveDomain ∧ F x ∈ positiveDomain ∧
        ∀ s : State, (x ∈ positiveBasin e s ↔ F x ∈ positiveBasin e s) := by
  have hd : ∀ t ∈ Icc 0 T, HasDerivAt (fun t => encodeState (X t))
      ((1:ℝ) • responseVectorField e (encodeState (X t))) t := by
    intro t ht
    simpa only [one_smul] using positive_trajectory_vector_derivative e X hX t ht.1
  obtain ⟨F,R,hF0,hR0,hF,hR,hl,hr,hbij,_hdl,_hdr,htraj⟩ :=
    physical_finite_nonsingular_endpoint e 1 T hT (fun t => encodeState (X t)) hd
  have hp : encodeState (X 0) ∈ positiveDomain := by
    simpa only [positiveDomain,mem_setOf_eq,decode_encodeState] using hX.positive 0 le_rfl
  refine ⟨F,R,hF0,hR0,hF,hR,hl,hr,hbij,?_⟩
  filter_upwards [htraj,positiveDomain_isOpen.mem_nhds hp] with x hx hxp
  obtain ⟨Y,hY0,hYT,hY⟩ := hx
  have hend : ∀ W : ℝ → State, IsPositiveTrajectory e W → W 0=decodeState x →
      encodeState (W T)=F x := by
    intro W hW hW0
    have hWd : ∀ t ∈ Icc 0 T, HasDerivAt (fun t => encodeState (W t))
        ((1:ℝ) • responseVectorField e (encodeState (W t))) t := by
      intro t ht
      simpa only [one_smul] using positive_trajectory_vector_derivative e W hW t ht.1
    have hsame : encodeState (W 0)=Y 0 := by rw [hW0,encode_decodeState,hY0]
    exact (scaled_physical_segment_unique e 1 T hT _ Y hWd hY hsame).trans hYT
  obtain ⟨W,hW0,hW⟩ := positive_global_solution e he hu (decodeState x) hxp
  have hWT := hend W hW hW0
  have hFp : F x ∈ positiveDomain := by
    rw [← hWT]
    simpa only [positiveDomain,mem_setOf_eq,decode_encodeState] using hW.positive T hT
  refine ⟨hxp,hFp,?_⟩
  intro s
  constructor
  · rintro ⟨Z,hZ,hZ0,hlim⟩
    have hZT := hend Z hZ hZ0
    refine ⟨fun t => Z (t+T),positive_trajectory_time_shift e Z hZ T hT,?_,?_⟩
    · simpa only [zero_add,decode_encodeState] using congrArg decodeState hZT
    · exact hlim.comp (tendsto_atTop_add_const_right atTop T tendsto_id)
  · intro hs
    have hh := positive_basin_at_initial_of_endpoint e s W hW T hT (by
      simpa only [hWT] using hs)
    simpa only [hW0,encode_decodeState] using hh

end CoreCouplingGlobal

import proofs.CoreCouplingGlobal.QuadraticCoefficientBinding

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter
open scoped Topology ContDiff

/-- The returned coordinates retain their actual spectral and nonlinear binding,
so later coverage arguments use the same coordinates as the constructed patch. -/
structure MiddlePerronCoordinates (e : ℝ) (s : State) (μ : Fin 4 → ℝ)
    (C : ResponseVector ≃L[ℝ] ResponseVector) : Prop where
  stable : ∀ i : Fin 3, μ i.castSucc < -(1/2:ℝ)
  unstable : 0 < μ 3
  equation : ∀ x : ResponseVector,
    C.symm (responseVectorField e (encodeState s+C x)) =
      (fun i => μ i*x i)+C.symm (physicalQuadratic e (C x))

theorem MiddlePerronCoordinates.shiftedStable {e : ℝ} {s : State}
    {μ : Fin 4 → ℝ} {C : ResponseVector ≃L[ℝ] ResponseVector}
    (hC : MiddlePerronCoordinates e s μ C) :
    ∀ i : Fin 4, i ≠ 3 → μ i+(1/4:ℝ) < 0 := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · intro hi
    exact False.elim (hi rfl)
  · intro _hj
    linarith [hC.stable j]

/-- The weighted local family is bound to the literal physical vector field,
with three freely prescribed stable coordinates and exact decaying representation.
Local manifold coverage and the unstable branches are not assumed or concluded. -/
theorem middle_actual_perron_family (e : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (s : State) (hs : s.Positive) (hss : Stationary (flagshipRates e) s)
    (hz : s.z ∈ Icc (19/10:ℝ) (21/10)) :
    ∃ μ : Fin 4 → ℝ, ∃ C : ResponseVector ≃L[ℝ] ResponseVector,
    ∃ hC : MiddlePerronCoordinates e s μ C,
    ∃ ψ : StableData → PerronSpace, ψ 0=0 ∧ ContDiffAt ℝ ω ψ 0 ∧
      HasFDerivAt ψ (perronLinear μ (1/4) hC.shiftedStable) 0 ∧
      ∀ᶠ ξ in 𝓝 (0:StableData), ∃ Y : ℝ → ResponseVector,
        (∀ t, 0 ≤ t → HasDerivAt Y (responseVectorField e (Y t)) t) ∧
        (∀ i : Fin 3, C.symm (Y 0-encodeState s) i.castSucc=ξ i) ∧
        ∀ t, 0 ≤ t → Y t=encodeState s+
          C (Real.exp (-(1/4:ℝ)*t) • (fun i => ψ ξ i t)) := by
  obtain ⟨μ,C,hstable,hu0,_hu1,hcoord⟩ :=
    middle_exact_quadratic_coordinates e he hu s hs hss hz
  obtain ⟨q,hq⟩ := physical_quadratic_has_coefficients e C
  have hst : ∀ i : Fin 4, i ≠ 3 → μ i+(1/4:ℝ) < 0 := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro hi
      exact False.elim (hi rfl)
    · intro _hj
      linarith [hstable j]
  have hun : 0 < μ 3+(1/4:ℝ) := by linarith
  obtain ⟨ψ,hzero,hcd,hd,htraj⟩ :=
    perron_local_actual_trajectories μ (1/4) (by norm_num) hst hun q
  refine ⟨μ,C,⟨hstable,hu0,hcoord⟩,ψ,hzero,hcd,hd,?_⟩
  filter_upwards [htraj] with ξ hξ
  let X := weightedPerron μ (1/4) (stableExtension ξ)
    (weightedTrajectoryBilinear (1/4) (by norm_num) q (ψ ξ) (ψ ξ))
  change (∀ t, 0 ≤ t → HasDerivAt X
    (fun i => μ i*X t i+coefficientQuadratic q (X t) i) t) ∧
    (∀ i : Fin 3, X 0 i.castSucc=ξ i) ∧
    (∀ t, 0 ≤ t → X t=Real.exp (-(1/4:ℝ)*t) • (fun i => ψ ξ i t)) at hξ
  let Y : ℝ → ResponseVector := fun t => encodeState s+C (X t)
  refine ⟨Y,?_,?_,?_⟩
  · intro t ht
    have h := (C.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hξ.1 t ht)).const_add
      (encodeState s)
    have hid : C (fun i => μ i*X t i+coefficientQuadratic q (X t) i)=
        responseVectorField e (Y t) := by
      change C ((fun i => μ i*X t i)+coefficientQuadratic q (X t))=_
      rw [hq]
      have hc := congrArg C (hcoord (X t))
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using hc.symm
    change HasDerivAt Y (C (fun i => μ i*X t i+coefficientQuadratic q (X t) i)) t at h
    rw [hid] at h
    exact h
  · intro i
    simpa [Y] using hξ.2.1 i
  · intro t ht
    change encodeState s+C (X t)=_
    rw [hξ.2.2 t ht]

end CoreCouplingGlobal

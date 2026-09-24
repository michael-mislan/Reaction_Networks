import proofs.CoreCouplingGlobal.PerronChart
import proofs.CoreCouplingGlobal.SpectralCone

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter
open scoped Topology ContDiff

theorem positive_vector_trajectory (e : ℝ) (Y : ℝ → ResponseVector)
    (hd : ∀ t, 0 ≤ t → HasDerivAt Y (responseVectorField e (Y t)) t)
    (hp : ∀ t, 0 ≤ t → Y t ∈ positiveDomain) :
    IsPositiveTrajectory e (fun t => decodeState (Y t)) := by
  constructor
  · exact hp
  · intro t ht
    exact hasDerivAt_pi.1 (hd t ht) 0
  · intro t ht
    exact hasDerivAt_pi.1 (hd t ht) 1
  · intro t ht
    exact hasDerivAt_pi.1 (hd t ht) 2
  · intro t ht
    exact hasDerivAt_pi.1 (hd t ht) 3

theorem convergent_vector_initial_in_basin (e : ℝ) (s : State) (Y : ℝ → ResponseVector)
    (hd : ∀ t, 0 ≤ t → HasDerivAt Y (responseVectorField e (Y t)) t)
    (hp : ∀ t, 0 ≤ t → Y t ∈ positiveDomain)
    (hl : Tendsto Y atTop (𝓝 (encodeState s))) : Y 0 ∈ positiveBasin e s := by
  refine ⟨fun t => decodeState (Y t),positive_vector_trajectory e Y hd hp,rfl,?_⟩
  simpa only [encode_decodeState] using hl

theorem vector_trajectory_forward_shift (e : ℝ) (Z : ℝ → ResponseVector)
    (hd : ∀ t, 0 ≤ t → HasDerivAt Z (responseVectorField e (Z t)) t)
    (T : ℝ) (hT : 0 ≤ T) :
    ∀ t, 0 ≤ t → HasDerivAt (fun u => Z (u+T)) (responseVectorField e (Z (t+T))) t := by
  intro t ht
  have hh := (hd (t+T) (add_nonneg ht hT)).scomp t ((hasDerivAt_id t).add_const T)
  simpa using hh

noncomputable def middleConjugatedField (e : ℝ) (s : State)
    (C : ResponseVector ≃L[ℝ] ResponseVector) (x : ResponseVector) : ResponseVector :=
  C.symm (responseVectorField e (encodeState s+C x))

theorem middleConjugatedField_hasStrictFDerivAt (e : ℝ) (s : State)
    (μ : Fin 4 → ℝ) (C : ResponseVector ≃L[ℝ] ResponseVector)
    (hC : MiddlePerronCoordinates e s μ C) :
    HasStrictFDerivAt (middleConjugatedField e s C) (spectralLinear μ) 0 := by
  let B := (physicalBilinear e).bilinearComp C.toContinuousLinearMap C.toContinuousLinearMap
  let CB : ResponseVector →L[ℝ] ResponseVector →L[ℝ] ResponseVector :=
    (ContinuousLinearMap.compL ℝ ResponseVector ResponseVector ResponseVector
      C.symm.toContinuousLinearMap).comp B
  have heq : middleConjugatedField e s C=(fun x => spectralLinear μ x+CB x x) := by
    funext x
    rw [middleConjugatedField,hC.equation]
    change (fun i => μ i*x i)+C.symm (physicalQuadratic e (C x))=
      spectralLinear μ x+C.symm (physicalBilinear e (C x) (C x))
    rw [physicalBilinear_diagonal]
    rfl
  rw [heq]
  exact spectral_bilinear_hasStrictFDerivAt μ CB

theorem middle_conjugated_trajectory (e : ℝ) (s : State)
    (C : ResponseVector ≃L[ℝ] ResponseVector) (X : ℝ → ResponseVector)
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (responseVectorField e (X t)) t) :
    ∀ t, 0 ≤ t → HasDerivAt (fun u => C.symm (X u-encodeState s))
      (middleConjugatedField e s C (C.symm (X t-encodeState s))) t := by
  intro t ht
  have h := C.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    ((hX t ht).sub_const (encodeState s))
  have hr : encodeState s+C (C.symm (X t-encodeState s))=X t := by
    rw [C.apply_symm_apply]
    abel
  change HasDerivAt _ (C.symm (responseVectorField e (encodeState s+
    C (C.symm (X t-encodeState s))))) t
  rw [hr]
  exact h

theorem middle_physical_trapped_unique (e : ℝ) (s : State)
    (μ : Fin 4 → ℝ) (C : ResponseVector ≃L[ℝ] ResponseVector)
    (hC : MiddlePerronCoordinates e s μ C) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ X Y : ℝ → ResponseVector,
      (∀ t, 0 ≤ t → HasDerivAt X (responseVectorField e (X t)) t) →
      (∀ t, 0 ≤ t → HasDerivAt Y (responseVectorField e (Y t)) t) →
      (∀ t, 0 ≤ t → ‖C.symm (X t-encodeState s)‖ < δ) →
      (∀ t, 0 ≤ t → ‖C.symm (Y t-encodeState s)‖ < δ) →
      (∀ i : Fin 3, C.symm (X 0-encodeState s) i.castSucc=
        C.symm (Y 0-encodeState s) i.castSucc) → X 0=Y 0 := by
  obtain ⟨δ,hδ,hunique⟩ := spectral_trapped_initial_unique
    (middleConjugatedField e s C) μ (middleConjugatedField_hasStrictFDerivAt e s μ C hC)
    hC.stable hC.unstable
  refine ⟨δ,hδ,?_⟩
  intro X Y hX hY hXt hYt hstable
  have h := hunique (fun t => C.symm (X t-encodeState s))
    (fun t => C.symm (Y t-encodeState s))
    (middle_conjugated_trajectory e s C X hX) (middle_conjugated_trajectory e s C Y hY)
    (fun t ht => by simpa using hXt t ht) (fun t ht => by simpa using hYt t ht) hstable
  have hh := congrArg (fun v => v+encodeState s) (C.symm.injective h)
  simpa using hh

noncomputable def middleStableProjection (C : ResponseVector ≃L[ℝ] ResponseVector)
    (s : State) (x : ResponseVector) : StableData :=
  fun i => C.symm (x-encodeState s) i.castSucc

/-- The constructed analytic patch covers every forever-locally-trapped actual
trajectory whose stable projection lies in its parameter domain. No assumed
exponential convergence or prescribed nonlinear forcing is used for that trajectory. -/
theorem middle_stable_patch_coverage (e : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (s : State) (hs : s.Positive) (hss : Stationary (flagshipRates e) s)
    (hz : s.z ∈ Icc (19/10:ℝ) (21/10)) :
    ∃ μ : Fin 4 → ℝ, ∃ C : ResponseVector ≃L[ℝ] ResponseVector,
    MiddlePerronCoordinates e s μ C ∧ ∃ φ : StableData → ResponseVector,
    ∃ U : Set StableData, ∃ δ : ℝ,
      IsOpen U ∧ 0 ∈ U ∧ 0 < δ ∧ φ 0=encodeState s ∧
      HasFDerivAt φ (C.toContinuousLinearMap.comp stableInclusion) 0 ∧
      ContDiffOn ℝ ω φ U ∧ InjOn φ U ∧
      (∀ ξ ∈ U, middleStableProjection C s (φ ξ)=ξ) ∧
      (∀ ξ ∈ U, ∃ Y : ℝ → ResponseVector, Y 0=φ ξ ∧
        (∀ t, 0 ≤ t → HasDerivAt Y (responseVectorField e (Y t)) t) ∧
        (∀ t, 0 ≤ t → Y t ∈ positiveDomain ∧ ‖C.symm (Y t-encodeState s)‖ < δ) ∧
        Tendsto Y atTop (𝓝 (encodeState s))) ∧
      (∀ ξ ∈ U, φ ξ ∈ positiveBasin e s) ∧
      ∀ Z : ℝ → ResponseVector,
        (∀ t, 0 ≤ t → HasDerivAt Z (responseVectorField e (Z t)) t) →
        (∀ t, 0 ≤ t → ‖C.symm (Z t-encodeState s)‖ < δ) →
        ∀ T, 0 ≤ T → middleStableProjection C s (Z T) ∈ U →
        Z T=φ (middleStableProjection C s (Z T)) := by
  obtain ⟨μ,C,hC,φ,hderiv,hpatch⟩ := middle_analytic_stable_patch e he hu s hs hss hz
  obtain ⟨δ,hδ,hunique⟩ := middle_physical_trapped_unique e s μ C hC
  let K := ‖C.symm.toContinuousLinearMap‖+1
  have hK : 0 < K := by dsimp [K]; positivity
  let ε := δ/K
  have hε : 0 < ε := div_pos hδ hK
  obtain ⟨U,hUopen,hUzero,hφzero,hcd,hinj,hleft,htraj⟩ := hpatch ε hε
  have hbound : ∀ x : ResponseVector, dist x (encodeState s) < ε →
      ‖C.symm (x-encodeState s)‖ < δ := by
    intro x hx
    rw [dist_eq_norm] at hx
    calc
      _ ≤ ‖C.symm.toContinuousLinearMap‖*‖x-encodeState s‖ :=
        C.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ K*‖x-encodeState s‖ := mul_le_mul_of_nonneg_right (by dsimp [K]; linarith)
        (norm_nonneg _)
      _ < K*ε := mul_lt_mul_of_pos_left hx hK
      _ = δ := by dsimp [ε]; field_simp
  have hactual : ∀ ξ ∈ U, ∃ Y : ℝ → ResponseVector, Y 0=φ ξ ∧
      (∀ t, 0 ≤ t → HasDerivAt Y (responseVectorField e (Y t)) t) ∧
      (∀ t, 0 ≤ t → Y t ∈ positiveDomain ∧ ‖C.symm (Y t-encodeState s)‖ < δ) ∧
      Tendsto Y atTop (𝓝 (encodeState s)) := by
    intro ξ hξ
    obtain ⟨Y,h0,hY,hp,hl⟩ := htraj ξ hξ
    exact ⟨Y,h0,hY,fun t ht => ⟨(hp t ht).1,hbound (Y t) (hp t ht).2⟩,hl⟩
  refine ⟨μ,C,hC,φ,U,δ,hUopen,hUzero,hδ,hφzero,hderiv,hcd,hinj,?_,hactual,?_,?_⟩
  · intro ξ hξ
    funext i
    exact hleft ξ hξ i
  · intro ξ hξ
    obtain ⟨Y,h0,hY,hp,hl⟩ := hactual ξ hξ
    have hh := convergent_vector_initial_in_basin e s Y hY (fun t ht => (hp t ht).1) hl
    simpa only [h0] using hh
  · intro Z hZ hZt T hT hproj
    let ξ := middleStableProjection C s (Z T)
    obtain ⟨Y,h0,hY,hYt,_hl⟩ := hactual ξ hproj
    have heq : Z T=Y 0 := by
      have hh := hunique (fun u => Z (u+T)) Y (vector_trajectory_forward_shift e Z hZ T hT)
        hY (fun t ht => hZt (t+T) (add_nonneg ht hT)) (fun t ht => (hYt t ht).2) (by
          intro i
          dsimp only
          rw [zero_add,h0]
          exact (hleft ξ hproj i).symm)
      simpa only [zero_add] using hh
    exact heq.trans h0

end CoreCouplingGlobal

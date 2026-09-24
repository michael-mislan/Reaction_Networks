import proofs.CoreCouplingGlobal.PhysicalUnstable
import proofs.CoreCouplingGlobal.SpectralCoverage
import proofs.CoreCouplingGlobal.ReverseCone

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter
open scoped Topology ContDiff

theorem middle_reversed_conjugated_trajectory (e : ℝ) (s : State)
    (C : ResponseVector ≃L[ℝ] ResponseVector) (X : ℝ → ResponseVector)
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (-responseVectorField e (X t)) t) :
    ∀ t, 0 ≤ t → HasDerivAt (fun u => C.symm (X u-encodeState s))
      (-middleConjugatedField e s C (C.symm (X t-encodeState s))) t := by
  intro t ht
  have h := C.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    ((hX t ht).sub_const (encodeState s))
  have hr : encodeState s+C (C.symm (X t-encodeState s))=X t := by
    rw [C.apply_symm_apply]
    abel
  change HasDerivAt _ (-C.symm (responseVectorField e (encodeState s+
    C (C.symm (X t-encodeState s))))) t
  rw [hr]
  change HasDerivAt (fun u => C.symm (X u-encodeState s))
    (C.symm (-responseVectorField e (X t))) t at h
  rw [map_neg] at h
  exact h

theorem middle_reversed_physical_trapped_unique (e : ℝ) (s : State)
    (μ : Fin 4 → ℝ) (C : ResponseVector ≃L[ℝ] ResponseVector)
    (hC : MiddlePerronCoordinates e s μ C) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ X Y : ℝ → ResponseVector,
      (∀ t, 0 ≤ t → HasDerivAt X (-responseVectorField e (X t)) t) →
      (∀ t, 0 ≤ t → HasDerivAt Y (-responseVectorField e (Y t)) t) →
      (∀ t, 0 ≤ t → ‖C.symm (X t-encodeState s)‖ < δ) →
      (∀ t, 0 ≤ t → ‖C.symm (Y t-encodeState s)‖ < δ) →
      C.symm (X 0-encodeState s) 3=C.symm (Y 0-encodeState s) 3 → X 0=Y 0 := by
  obtain ⟨δ,hδ,hunique⟩ := reversed_spectral_trapped_initial_unique
    (middleConjugatedField e s C) μ (middleConjugatedField_hasStrictFDerivAt e s μ C hC)
    hC.stable hC.unstable
  refine ⟨δ,hδ,?_⟩
  intro X Y hX hY hXt hYt hstable
  have h := hunique (fun t => C.symm (X t-encodeState s))
    (fun t => C.symm (Y t-encodeState s))
    (middle_reversed_conjugated_trajectory e s C X hX)
    (middle_reversed_conjugated_trajectory e s C Y hY)
    (fun t ht => by simpa using hXt t ht) (fun t ht => by simpa using hYt t ht) hstable
  have hh := congrArg (fun v => v+encodeState s) (C.symm.injective h)
  simpa using hh

theorem past_trajectory_reversed_shift (e : ℝ) (Z : ℝ → ResponseVector)
    (hZ : ∀ t, t ≤ 0 → HasDerivAt Z (responseVectorField e (Z t)) t)
    (T : ℝ) (hT : T ≤ 0) :
    ∀ u, 0 ≤ u → HasDerivAt (fun t => Z (T-t))
      (-responseVectorField e (Z (T-u))) u := by
  intro u hu
  have h := (hZ (T-u) (by linarith)).scomp u ((hasDerivAt_id u).const_sub T)
  simpa using h

/-- The analytic one-dimensional patch covers every locally past-trapped
trajectory over its unstable-coordinate domain, including conditional backward
invariance at every nonpositive time. -/
theorem middle_unstable_patch_coverage (e : ℝ) (s : State) (hs : s.Positive)
    (μ : Fin 4 → ℝ) (C : ResponseVector ≃L[ℝ] ResponseVector)
    (hC : MiddlePerronCoordinates e s μ C) (εmax : ℝ) (hεmax : 0 < εmax) :
    ∃ φ : ℝ → ResponseVector, ∃ U : Set ℝ, ∃ δ : ℝ,
      IsOpen U ∧ 0 ∈ U ∧ 0 < δ ∧ φ 0=encodeState s ∧
      HasFDerivAt φ (C.toContinuousLinearMap.comp unstableInclusion) 0 ∧
      ContDiffOn ℝ ω φ U ∧ InjOn φ U ∧
      (∀ a ∈ U, C.symm (φ a-encodeState s) 3=a) ∧
      (∀ a ∈ U, ∃ Y : ℝ → ResponseVector, Y 0=φ a ∧
        (∀ t, t ≤ 0 → HasDerivAt Y (responseVectorField e (Y t)) t) ∧
        (∀ t, t ≤ 0 → Y t ∈ positiveDomain ∧ ‖C.symm (Y t-encodeState s)‖ < δ ∧
          dist (Y t) (encodeState s) < εmax) ∧
        Tendsto (fun t => Y (-t)) atTop (𝓝 (encodeState s))) ∧
      ∀ Z : ℝ → ResponseVector,
        (∀ t, t ≤ 0 → HasDerivAt Z (responseVectorField e (Z t)) t) →
        (∀ t, t ≤ 0 → ‖C.symm (Z t-encodeState s)‖ < δ) →
        ∀ T, T ≤ 0 → C.symm (Z T-encodeState s) 3 ∈ U →
          Z T=φ (C.symm (Z T-encodeState s) 3) := by
  obtain ⟨δ,hδ,hunique⟩ := middle_reversed_physical_trapped_unique e s μ C hC
  obtain ⟨φ,hφzero,hderiv,hpatch⟩ := middle_analytic_unstable_patch e s hs μ C hC
  let K := ‖C.symm.toContinuousLinearMap‖+1
  have hK : 0 < K := by dsimp [K]; positivity
  let ε := δ/K
  have hε : 0 < ε := div_pos hδ hK
  obtain ⟨U,hUopen,hUzero,hcd,hinj,hleft,htraj⟩ := hpatch (min ε εmax) (lt_min hε hεmax)
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
  have hactual : ∀ a ∈ U, ∃ Y : ℝ → ResponseVector, Y 0=φ a ∧
      (∀ t, t ≤ 0 → HasDerivAt Y (responseVectorField e (Y t)) t) ∧
      (∀ t, t ≤ 0 → Y t ∈ positiveDomain ∧ ‖C.symm (Y t-encodeState s)‖ < δ ∧
          dist (Y t) (encodeState s) < εmax) ∧
      Tendsto (fun t => Y (-t)) atTop (𝓝 (encodeState s)) := by
    intro a ha
    obtain ⟨Y,h0,hY,hp,hl⟩ := htraj a ha
    exact ⟨Y,h0,hY,fun t ht => ⟨(hp t ht).1,
      hbound (Y t) ((hp t ht).2.trans_le (min_le_left _ _)),
      (hp t ht).2.trans_le (min_le_right _ _)⟩,hl⟩
  refine ⟨φ,U,δ,hUopen,hUzero,hδ,hφzero,hderiv,hcd,hinj,hleft,hactual,?_⟩
  intro Z hZ hZt T hT hproj
  let a := C.symm (Z T-encodeState s) 3
  obtain ⟨Y,h0,hY,hYt,_hl⟩ := hactual a hproj
  have heq := hunique (fun t => Z (T-t)) (fun t => Y (0-t))
    (past_trajectory_reversed_shift e Z hZ T hT)
    (past_trajectory_reversed_shift e Y hY 0 le_rfl)
    (fun t ht => hZt (T-t) (by linarith))
    (fun t ht => (hYt (0-t) (by linarith)).2.1) (by
      dsimp only
      rw [sub_zero,sub_self,h0]
      exact (hleft a hproj).symm)
  have hh : Z T=Y 0 := by simpa only [sub_zero,sub_self] using heq
  exact hh.trans h0

end CoreCouplingGlobal

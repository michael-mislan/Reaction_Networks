import proofs.CoreCouplingGlobal.ReversePerron
import proofs.CoreCouplingGlobal.PerronChart

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter
open scoped Topology ContDiff BoundedContinuousFunction

noncomputable def unstableInclusion : ℝ →L[ℝ] ResponseVector :=
  ContinuousLinearMap.pi fun i => if i=3 then ContinuousLinearMap.id ℝ ℝ else 0

theorem perronEvaluation_zero_reverseLinear (μ : Fin 4 → ℝ) (β : ℝ)
    (hs : μ 3+β < 0) :
    (perronEvaluation 0).comp (reversePerronLinear μ β hs)=unstableInclusion := by
  apply ContinuousLinearMap.ext
  intro a
  funext i
  by_cases hi : i=3
  · subst i
    simpa [perronEvaluation,unstableInclusion] using
      reversePerronLinear_stable μ β hs a 0 (by norm_num)
  · simpa [perronEvaluation,unstableInclusion,hi] using
      reversePerronLinear_unstable μ β hs a 0 i hi

/-- The same physical spectral coordinates admit an actual analytic
one-parameter family for the reversed physical ODE. -/
theorem middle_reversed_physical_family (e : ℝ) (s : State)
    (μ : Fin 4 → ℝ) (C : ResponseVector ≃L[ℝ] ResponseVector)
    (hC : MiddlePerronCoordinates e s μ C) :
    ∃ ψ : ℝ → PerronSpace, ψ 0=0 ∧ ContDiffAt ℝ ω ψ 0 ∧
      HasFDerivAt (fun a => encodeState s+C (perronEvaluation 0 (ψ a)))
        (C.toContinuousLinearMap.comp unstableInclusion) 0 ∧
      ∀ᶠ a in 𝓝 (0:ℝ), ∃ Y : ℝ → ResponseVector,
        (∀ t, 0 ≤ t → HasDerivAt Y (-responseVectorField e (Y t)) t) ∧
        C.symm (Y 0-encodeState s) 3=a ∧
        ∀ t, 0 ≤ t → Y t=encodeState s+
          C (Real.exp (-(μ 3/2)*t) • (fun i => ψ a i t)) := by
  let β := μ 3/2
  have hβ : 0 < β := half_pos hC.unstable
  let ν : Fin 4 → ℝ := fun i => -μ i
  have hst : ν 3+β < 0 := by dsimp [ν,β]; linarith [hC.unstable]
  have hun : ∀ i : Fin 4, i ≠ 3 → 0 < ν i+β := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro hi
      exact False.elim (hi rfl)
    · intro _hj
      dsimp [ν]
      linarith [hC.stable j]
  obtain ⟨q,hq⟩ := physical_quadratic_has_coefficients e C
  let nq : Fin 4 → Fin 4 → Fin 4 → ℝ := fun i j k => -q i j k
  have hnq : ∀ x, coefficientQuadratic nq x= -C.symm (physicalQuadratic e (C x)) := by
    intro x
    rw [← hq]
    ext i
    simp [coefficientQuadratic,nq,Finset.sum_neg_distrib]
  obtain ⟨ψ,hzero,hcd,hd,htraj⟩ := reversePerron_local_actual_trajectories ν β hβ hst hun nq
  have he := (perronEvaluation 0).hasFDerivAt.comp 0 hd
  rw [perronEvaluation_zero_reverseLinear] at he
  refine ⟨ψ,hzero,hcd,(C.toContinuousLinearMap.hasFDerivAt.comp 0 he).const_add
    (encodeState s),?_⟩
  filter_upwards [htraj] with a ha
  let X := weightedReversePerron ν β (unstableExtension a)
    (weightedTrajectoryBilinear β hβ nq (ψ a) (ψ a))
  change (∀ t, 0 ≤ t → HasDerivAt X
    (fun i => ν i*X t i+coefficientQuadratic nq (X t) i) t) ∧
    X 0 3=a ∧ (∀ t, 0 ≤ t → X t=Real.exp (-β*t) • (fun i => ψ a i t)) at ha
  let Y : ℝ → ResponseVector := fun t => encodeState s+C (X t)
  refine ⟨Y,?_,?_,ha.2.2 |> fun hr t ht => congrArg (fun x => encodeState s+C x) (hr t ht)⟩
  · intro t ht
    have h := (C.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (ha.1 t ht)).const_add
      (encodeState s)
    have hid : C (fun i => ν i*X t i+coefficientQuadratic nq (X t) i)=
        -responseVectorField e (Y t) := by
      change C ((fun i => ν i*X t i)+coefficientQuadratic nq (X t))=_
      rw [hnq]
      have hv : (fun i => ν i*X t i)= -(fun i => μ i*X t i) := by
        ext i
        simp [ν]
      rw [hv,← neg_add,C.map_neg]
      have hc := congrArg C (hC.equation (X t))
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using congrArg Neg.neg hc.symm
    change HasDerivAt Y (C (fun i => ν i*X t i+coefficientQuadratic nq (X t) i)) t at h
    rw [hid] at h
    exact h
  · simpa [Y] using ha.2.1

theorem reversed_to_past_trajectory (e : ℝ) (Y : ℝ → ResponseVector)
    (hY : ∀ t, 0 ≤ t → HasDerivAt Y (-responseVectorField e (Y t)) t) :
    ∀ t, t ≤ 0 → HasDerivAt (fun u => Y (-u))
      (responseVectorField e (Y (-t))) t := by
  intro t ht
  have h := (hY (-t) (neg_nonneg.mpr ht)).scomp t (hasDerivAt_id t).neg
  simpa using h

/-- An actual analytic unstable patch, with physical backward trajectories,
positivity, arbitrarily small past trapping, and convergence as reversed time
tends to infinity. Invariance/coverage and branch destinations are separate. -/
theorem middle_analytic_unstable_patch (e : ℝ) (s : State) (hs : s.Positive)
    (μ : Fin 4 → ℝ) (C : ResponseVector ≃L[ℝ] ResponseVector)
    (hC : MiddlePerronCoordinates e s μ C) :
    ∃ φ : ℝ → ResponseVector,
      φ 0=encodeState s ∧
      HasFDerivAt φ (C.toContinuousLinearMap.comp unstableInclusion) 0 ∧
      ∀ ε : ℝ, 0 < ε → ∃ U : Set ℝ,
        IsOpen U ∧ 0 ∈ U ∧ ContDiffOn ℝ ω φ U ∧ InjOn φ U ∧
        (∀ a ∈ U, C.symm (φ a-encodeState s) 3=a) ∧
        ∀ a ∈ U, ∃ Y : ℝ → ResponseVector,
          Y 0=φ a ∧
          (∀ t, t ≤ 0 → HasDerivAt Y (responseVectorField e (Y t)) t) ∧
          (∀ t, t ≤ 0 → Y t ∈ positiveDomain ∧ dist (Y t) (encodeState s) < ε) ∧
          Tendsto (fun t => Y (-t)) atTop (𝓝 (encodeState s)) := by
  obtain ⟨ψ,hzero,hcd,hd,htraj⟩ := middle_reversed_physical_family e s μ C hC
  let φ : ℝ → ResponseVector := fun a => encodeState s+C (perronEvaluation 0 (ψ a))
  refine ⟨φ,by simp [φ,hzero],hd,?_⟩
  intro ε hε
  have hp : encodeState s ∈ positiveDomain := by
    simpa only [positiveDomain,mem_setOf_eq,decode_encodeState] using hs
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.1 positiveDomain_isOpen (encodeState s) hp
  have hsmall : ∀ᶠ a in 𝓝 (0:ℝ), ‖C.toContinuousLinearMap‖*‖ψ a‖ < min r ε := by
    have hc : ContinuousAt (fun a => ‖C.toContinuousLinearMap‖*‖ψ a‖) 0 :=
      continuousAt_const.mul hcd.continuousAt.norm
    exact hc.eventually_lt_const (by simpa [hzero] using lt_min hr hε)
  have hreg := hcd.eventually (by simp : (ω : ℕ∞ω) ≠ ∞)
  obtain ⟨U,hUsub,hUopen,hUzero⟩ := mem_nhds_iff.mp ((htraj.and hsmall).and hreg)
  have hdata : ∀ a ∈ U, ∃ Y : ℝ → ResponseVector,
      Y 0=φ a ∧ (∀ t, 0 ≤ t → HasDerivAt Y (-responseVectorField e (Y t)) t) ∧
      (∀ t, 0 ≤ t → Y t ∈ positiveDomain ∧ dist (Y t) (encodeState s) < ε) ∧
      Tendsto Y atTop (𝓝 (encodeState s)) ∧ C.symm (φ a-encodeState s) 3=a := by
    intro a ha
    obtain ⟨Y,hY,hinit,hrep⟩ := (hUsub ha).1.1
    have h0 : Y 0=φ a := by simpa [φ,perronEvaluation] using hrep 0 (by norm_num)
    refine ⟨Y,h0,hY,?_,weighted_physical_tendsto C (μ 3/2) (half_pos hC.unstable)
      (ψ a) (encodeState s) Y hrep,by simpa only [h0] using hinit⟩
    intro t ht
    have hdist : dist (Y t) (encodeState s) < min r ε := by
      rw [dist_eq_norm,hrep t ht,add_sub_cancel_left]
      exact (weighted_physical_uniform_norm C (μ 3/2) (half_pos hC.unstable)
        (ψ a) t ht).trans_lt (hUsub ha).1.2
    exact ⟨hball (hdist.trans_le (min_le_left _ _)),hdist.trans_le (min_le_right _ _)⟩
  have hleft : ∀ a ∈ U, C.symm (φ a-encodeState s) 3=a := by
    intro a ha
    obtain ⟨_Y,_h0,_hY,_hp,_hl,hi⟩ := hdata a ha
    exact hi
  refine ⟨U,hUopen,hUzero,?_,?_,hleft,?_⟩
  · intro a ha
    have he := (perronEvaluation 0).contDiff.contDiffAt.comp a (hUsub ha).2
    exact (contDiffAt_const.add (C.toContinuousLinearMap.contDiff.contDiffAt.comp a he)).contDiffWithinAt
  · intro a ha b hb heq
    rw [← hleft a ha,← hleft b hb,heq]
  · intro a ha
    obtain ⟨Y,h0,hY,hp,hl,_hi⟩ := hdata a ha
    refine ⟨fun t => Y (-t),by simpa using h0,reversed_to_past_trajectory e Y hY,?_,?_⟩
    · intro t ht
      exact hp (-t) (neg_nonneg.mpr ht)
    · simpa using hl

end CoreCouplingGlobal

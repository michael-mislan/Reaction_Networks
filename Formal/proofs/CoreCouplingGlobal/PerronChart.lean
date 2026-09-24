import proofs.CoreCouplingGlobal.PerronBounds

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter
open scoped Topology ContDiff BoundedContinuousFunction

noncomputable def perronEvaluation (t : ℝ) : PerronSpace →L[ℝ] ResponseVector :=
  ContinuousLinearMap.pi fun i => (BoundedContinuousFunction.evalCLM ℝ t).comp
    (ContinuousLinearMap.proj i)

noncomputable def stableInclusion : StableData →L[ℝ] ResponseVector :=
  ContinuousLinearMap.pi (Fin.lastCases 0 (fun i : Fin 3 => ContinuousLinearMap.proj i))

theorem perronEvaluation_zero_linear (μ : Fin 4 → ℝ) (β : ℝ)
    (hs : ∀ i : Fin 4, i ≠ 3 → μ i+β < 0) :
    (perronEvaluation 0).comp (perronLinear μ β hs)=stableInclusion := by
  ext ξ i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change perronLinear μ β hs ξ 3 0=0
    exact perronLinear_unstable μ β hs ξ 0
  · simpa [perronEvaluation,stableInclusion] using
      perronLinear_stable μ β hs ξ j 0 (by norm_num)

noncomputable def perronInitial (C : ResponseVector ≃L[ℝ] ResponseVector)
    (p : ResponseVector) (ψ : StableData → PerronSpace) (ξ : StableData) : ResponseVector :=
  p+C (perronEvaluation 0 (ψ ξ))

theorem perronInitial_contDiffAt (C : ResponseVector ≃L[ℝ] ResponseVector)
    (p : ResponseVector) (ψ : StableData → PerronSpace) (ξ : StableData)
    (hψ : ContDiffAt ℝ ω ψ ξ) : ContDiffAt ℝ ω (perronInitial C p ψ) ξ := by
  have he := (perronEvaluation 0).contDiff.contDiffAt.comp ξ hψ
  exact contDiffAt_const.add (C.toContinuousLinearMap.contDiff.contDiffAt.comp ξ he)

theorem perronInitial_hasFDerivAt (C : ResponseVector ≃L[ℝ] ResponseVector)
    (p : ResponseVector) (ψ : StableData → PerronSpace) (μ : Fin 4 → ℝ) (β : ℝ)
    (hs : ∀ i : Fin 4, i ≠ 3 → μ i+β < 0)
    (hψ : HasFDerivAt ψ (perronLinear μ β hs) 0) :
    HasFDerivAt (perronInitial C p ψ) (C.toContinuousLinearMap.comp stableInclusion) 0 := by
  have he := (perronEvaluation 0).hasFDerivAt.comp 0 hψ
  rw [perronEvaluation_zero_linear] at he
  exact (C.toContinuousLinearMap.hasFDerivAt.comp 0 he).const_add p

/-- An open three-parameter analytic patch of positive, locally trapped,
middle-convergent initial states, with an explicit continuous linear-coordinate
left inverse. Coverage of every locally trapped trajectory remains separate. -/
theorem middle_analytic_stable_patch (e : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (s : State) (hs : s.Positive) (hss : Stationary (flagshipRates e) s)
    (hz : s.z ∈ Icc (19/10:ℝ) (21/10)) :
    ∃ μ : Fin 4 → ℝ, ∃ C : ResponseVector ≃L[ℝ] ResponseVector,
    MiddlePerronCoordinates e s μ C ∧
    ∃ φ : StableData → ResponseVector,
      HasFDerivAt φ (C.toContinuousLinearMap.comp stableInclusion) 0 ∧ ∀ ε : ℝ, 0 < ε → ∃ U : Set StableData,
      IsOpen U ∧ 0 ∈ U ∧ φ 0=encodeState s ∧ ContDiffOn ℝ ω φ U ∧ InjOn φ U ∧
      (∀ ξ ∈ U, ∀ i : Fin 3, C.symm (φ ξ-encodeState s) i.castSucc=ξ i) ∧
      ∀ ξ ∈ U, ∃ Y : ℝ → ResponseVector,
        Y 0=φ ξ ∧ (∀ t, 0 ≤ t → HasDerivAt Y (responseVectorField e (Y t)) t) ∧
        (∀ t, 0 ≤ t → Y t ∈ positiveDomain ∧ dist (Y t) (encodeState s) < ε) ∧
        Tendsto Y atTop (𝓝 (encodeState s)) := by
  obtain ⟨μ,C,hC,ψ,hzero,hcd,hd,htraj⟩ := middle_positive_trapped_perron_family e he hu s hs hss hz
  let φ := perronInitial C (encodeState s) ψ
  refine ⟨μ,C,hC,φ,perronInitial_hasFDerivAt C (encodeState s) ψ μ (1/4) hC.shiftedStable hd,?_⟩
  intro ε hε
  have hreg := hcd.eventually (by simp : (ω : ℕ∞ω) ≠ ∞)
  have hall := (htraj ε hε).and hreg
  obtain ⟨U,hUsub,hUopen,hUzero⟩ := mem_nhds_iff.mp hall
  have hφzero : φ 0=encodeState s := by simp [φ,perronInitial,hzero]
  have hdata : ∀ ξ ∈ U, ∃ Y : ℝ → ResponseVector,
      Y 0=φ ξ ∧ (∀ t, 0 ≤ t → HasDerivAt Y (responseVectorField e (Y t)) t) ∧
      (∀ t, 0 ≤ t → Y t ∈ positiveDomain ∧ dist (Y t) (encodeState s) < ε) ∧
      Tendsto Y atTop (𝓝 (encodeState s)) ∧
      ∀ i : Fin 3, C.symm (φ ξ-encodeState s) i.castSucc=ξ i := by
    intro ξ hξ
    obtain ⟨Y,hY,hpos,hlim,hinit,hrep⟩ := (hUsub hξ).1
    have hinit' : Y 0=φ ξ := by
      simpa [φ,perronInitial,perronEvaluation] using hrep 0 (by norm_num)
    refine ⟨Y,hinit',hY,hpos,hlim,?_⟩
    simpa only [hinit'] using hinit
  have hleft : ∀ ξ ∈ U, ∀ i : Fin 3,
      C.symm (φ ξ-encodeState s) i.castSucc=ξ i := by
    intro ξ hξ
    obtain ⟨_Y,_h0,_hY,_hp,_hl,hli⟩ := hdata ξ hξ
    exact hli
  refine ⟨U,hUopen,hUzero,hφzero,?_,?_,hleft,?_⟩
  · intro ξ hξ
    exact (perronInitial_contDiffAt C (encodeState s) ψ ξ (hUsub hξ).2).contDiffWithinAt
  · intro ξ hξ ζ hζ hsame
    ext i
    rw [← hleft ξ hξ i,← hleft ζ hζ i,hsame]
  · intro ξ hξ
    obtain ⟨Y,h0,hY,hp,hl,_hli⟩ := hdata ξ hξ
    exact ⟨Y,h0,hY,hp,hl⟩

end CoreCouplingGlobal

import Mathlib.Analysis.Calculus.ImplicitContDiff

namespace CoreCouplingGlobal
open Filter
open scoped Topology ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A quadratic trajectory equation has an actual smooth local solution, with
the prescribed linear tangent. No fixed point is supplied as a hypothesis. -/
theorem quadratic_implicit_solution (L : E →L[ℝ] F) (B : F →L[ℝ] F →L[ℝ] F) :
    ∃ ψ : E → F, ψ 0=0 ∧ ContDiffAt ℝ ω ψ 0 ∧ HasFDerivAt ψ L 0 ∧
      (∀ᶠ ξ in 𝓝 (0:E), ψ ξ=L ξ+B (ψ ξ) (ψ ξ)) ∧
      ∀ᶠ z : E × F in 𝓝 (0,0), z.2=L z.1+B z.2 z.2 ↔ ψ z.1=z.2 := by
  let f : E × F → F := fun z => z.2-L z.1-B z.2 z.2
  let D : E × F →L[ℝ] F := ContinuousLinearMap.snd ℝ E F-
    L.comp (ContinuousLinearMap.fst ℝ E F)
  have hB : HasFDerivAt (fun z : E × F => B z.2 z.2)
      (0 : E × F →L[ℝ] F) (0,0) := by
    simpa using B.hasFDerivAt_of_bilinear
      ((ContinuousLinearMap.snd ℝ E F).hasFDerivAt (x := ((0,0) : E × F)))
      ((ContinuousLinearMap.snd ℝ E F).hasFDerivAt (x := ((0,0) : E × F)))
  have hd : HasFDerivAt f D (0,0) := by
    simpa [f,D] using
      ((ContinuousLinearMap.snd ℝ E F).hasFDerivAt.sub
        (L.hasFDerivAt.comp (0,0)
          (ContinuousLinearMap.fst ℝ E F).hasFDerivAt)).sub hB
  have hc : ContDiffAt ℝ ω f (0,0) := by
    have : ContDiff ℝ ω f := by dsimp [f]; fun_prop
    exact this.contDiffAt
  have hr : fderiv ℝ f (0,0) ∘L ContinuousLinearMap.inr ℝ E F =
      ContinuousLinearMap.id ℝ F := by
    rw [hd.fderiv]
    ext y
    simp [D]
  have hl : fderiv ℝ f (0,0) ∘L ContinuousLinearMap.inl ℝ E F = -L := by
    rw [hd.fderiv]
    ext x
    simp [D]
  have hi : (fderiv ℝ f (0,0) ∘L ContinuousLinearMap.inr ℝ E F).IsInvertible := by
    rw [hr]
    exact ContinuousLinearMap.isInvertible_equiv (f := ContinuousLinearEquiv.refl ℝ F)
  have hn : (ω : ℕ∞ω) ≠ 0 := by simp
  let ψ := hc.implicitFunction hn hi
  have hp : ψ 0=0 := hc.implicitFunction_apply_self hn hi
  have ht : HasFDerivAt ψ L 0 := by
    have h := (hc.hasStrictFDerivAt_implicitFunction hn hi).hasFDerivAt
    simpa [hr,hl] using h
  refine ⟨ψ,hp,hc.contDiffAt_implicitFunction hn hi,ht,?_,?_⟩
  · filter_upwards [hc.eventually_apply_implicitFunction hn hi] with ξ hξ
    change ψ ξ-L ξ-B (ψ ξ) (ψ ξ)=f (0,0) at hξ
    have hzero : f (0,0)=0 := by simp [f]
    rw [hzero] at hξ
    exact sub_eq_zero.mp ((sub_sub _ _ _).symm.trans hξ)
  · filter_upwards [hc.eventually_apply_eq_iff_implicitFunction hn hi] with z hz
    have he : f z=f (0,0) ↔ z.2=L z.1+B z.2 z.2 := by
      simp only [f,map_zero,sub_zero]
      rw [sub_sub,sub_eq_zero]
    exact he.symm.trans hz

end CoreCouplingGlobal

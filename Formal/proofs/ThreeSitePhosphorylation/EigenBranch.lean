import proofs.ThreeSitePhosphorylation.SimpleRoot

namespace ThreeSitePhosphorylation
noncomputable section
open scoped Topology
set_option maxHeartbeats 200000

def complexScalar (d : ℂ) : ℂ →L[ℝ] ℂ :=
  (d • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ

@[simp] theorem complexScalar_apply (d z : ℂ) : complexScalar d z = d*z := rfl

theorem complexScalar_invertible (d : ℂ) (hd : d ≠ 0) :
    (complexScalar d).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := complexScalar d⁻¹)
  · ext z; simp [hd]
  · ext z; simp [hd]

def spectralResidual (p : ℝ × ℂ) : ℂ := candidatePolynomial p.1 p.2

theorem spectralResidual_smooth : ContDiff ℝ ⊤ spectralResidual := by
  have hc : ContDiff ℝ ⊤ (fun p : ℝ × ℂ => (p.1:ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_fst
  unfold spectralResidual candidatePolynomial
  fun_prop

theorem spectralResidual_partial (r : ℝ) (z : ℂ) :
    fderiv ℝ spectralResidual (r,z) ∘L ContinuousLinearMap.inr ℝ ℝ ℂ =
      complexScalar (candidateSlope r z) := by
  have hi : HasFDerivAt (fun u : ℂ => (r,u))
      (ContinuousLinearMap.inr ℝ ℝ ℂ) z := by
    convert (hasFDerivAt_const r z).prodMk (hasFDerivAt_id z) using 1
  have h := (spectralResidual_smooth.differentiable (by norm_num) (r,z)).hasFDerivAt
  have hc := h.comp z hi
  have hp := (candidate_hasDerivAt r z).hasFDerivAt.restrictScalars ℝ
  have he : (ContinuousLinearMap.toSpanSingleton ℂ
      (candidateSlope r z)).restrictScalars ℝ = complexScalar (candidateSlope r z) := by
    ext u
    simp [complexScalar,mul_comm]
  rw [he] at hp
  exact hc.unique hp

theorem simple_root_branch (r : ℝ) (z : ℂ)
    (hp : candidatePolynomial r z=0) (hs : candidateSlope r z ≠ 0) :
    ∃ g : ℝ → ℂ, ContDiffAt ℝ ⊤ g r ∧ g r=z ∧
      ∀ᶠ s in 𝓝 r, candidatePolynomial s (g s)=0 := by
  have hi : (fderiv ℝ spectralResidual (r,z) ∘L
      ContinuousLinearMap.inr ℝ ℝ ℂ).IsInvertible := by
    rw [spectralResidual_partial]
    exact complexScalar_invertible _ hs
  let h := spectralResidual_smooth.contDiffAt (x := (r,z))
  refine ⟨h.implicitFunction (by simp) hi,h.contDiffAt_implicitFunction (by simp) hi,
    h.implicitFunction_apply_self (by simp) hi,?_⟩
  simpa only [spectralResidual,hp] using h.eventually_apply_implicitFunction (by simp) hi

end
end ThreeSitePhosphorylation

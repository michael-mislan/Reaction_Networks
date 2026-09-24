import proofs.CoreCouplingGlobal.FiniteFlowInverse

namespace CoreCouplingGlobal
open Set Filter
open scoped Topology ContDiff

/-- A pair of differentiable inverse germs has inverse differentials. -/
theorem inverse_germs_fderiv (F R : ResponseVector → ResponseVector) (p q : ResponseVector)
    (hF0 : F p=q) (hR0 : R q=p)
    (hF : DifferentiableAt ℝ F p) (hR : DifferentiableAt ℝ R q)
    (hleft : ∀ᶠ x in 𝓝 p, R (F x)=x) (hright : ∀ᶠ y in 𝓝 q, F (R y)=y) :
    (fderiv ℝ R q).comp (fderiv ℝ F p)=ContinuousLinearMap.id ℝ ResponseVector ∧
    (fderiv ℝ F p).comp (fderiv ℝ R q)=ContinuousLinearMap.id ℝ ResponseVector := by
  have hdR : HasFDerivAt R (fderiv ℝ R q) (F p) := by
    rw [hF0]
    exact hR.hasFDerivAt
  have hdF : HasFDerivAt F (fderiv ℝ F p) (R q) := by
    rw [hR0]
    exact hF.hasFDerivAt
  have hl := hdR.comp p hF.hasFDerivAt
  have hr := hdF.comp q hR.hasFDerivAt
  have hidl : HasFDerivAt (R ∘ F) (ContinuousLinearMap.id ℝ ResponseVector) p :=
    (hasFDerivAt_id p).congr_of_eventuallyEq hleft
  have hidr : HasFDerivAt (F ∘ R) (ContinuousLinearMap.id ℝ ResponseVector) q :=
    (hasFDerivAt_id q).congr_of_eventuallyEq hright
  exact ⟨hl.unique hidl,hr.unique hidr⟩

/-- The actual finite physical endpoint map has an invertible differential,
proved from actual reversed trajectories rather than an assumed flow theorem. -/
theorem physical_finite_nonsingular_endpoint (e σ T : ℝ) (hT : 0 ≤ T)
    (X : ℝ → ResponseVector)
    (hX : ∀ t ∈ Icc 0 T, HasDerivAt X (σ • responseVectorField e (X t)) t) :
    ∃ F R : ResponseVector → ResponseVector,
      F (X 0)=X T ∧ R (X T)=X 0 ∧
      ContDiffAt ℝ ω F (X 0) ∧ ContDiffAt ℝ ω R (X T) ∧
      (∀ᶠ x in 𝓝 (X 0), R (F x)=x) ∧
      (∀ᶠ y in 𝓝 (X T), F (R y)=y) ∧
      Function.Bijective (fderiv ℝ F (X 0)) ∧
      (fderiv ℝ R (X T)).comp (fderiv ℝ F (X 0))=ContinuousLinearMap.id ℝ ResponseVector ∧
      (fderiv ℝ F (X 0)).comp (fderiv ℝ R (X T))=ContinuousLinearMap.id ℝ ResponseVector ∧
      (∀ᶠ x in 𝓝 (X 0), ∃ Y : ℝ → ResponseVector, Y 0=x ∧ Y T=F x ∧
        ∀ t ∈ Icc 0 T, HasDerivAt Y (σ • responseVectorField e (Y t)) t) := by
  obtain ⟨F,R,hF0,hR0,hF,hR,hl,hr,htraj⟩ := physical_finite_inverse_germs e σ T hT X hX
  obtain ⟨hdl,hdr⟩ := inverse_germs_fderiv F R (X 0) (X T) hF0 hR0
    (hF.differentiableAt (by simp)) (hR.differentiableAt (by simp)) hl hr
  have hli : Function.LeftInverse (fderiv ℝ R (X T)) (fderiv ℝ F (X 0)) := by
    intro v
    exact congrArg (fun L : ResponseVector →L[ℝ] ResponseVector => L v) hdl
  have hri : Function.RightInverse (fderiv ℝ R (X T)) (fderiv ℝ F (X 0)) := by
    intro v
    exact congrArg (fun L : ResponseVector →L[ℝ] ResponseVector => L v) hdr
  exact ⟨F,R,hF0,hR0,hF,hR,hl,hr,⟨hli.injective,hri.surjective⟩,hdl,hdr,htraj⟩

end CoreCouplingGlobal

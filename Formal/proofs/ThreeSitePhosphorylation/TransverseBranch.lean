import proofs.ThreeSitePhosphorylation.EigenBranch
import proofs.ThreeSitePhosphorylation.CrossingQuotient
import proofs.ThreeSitePhosphorylation.SourceSimple

namespace ThreeSitePhosphorylation
noncomputable section
open scoped Topology
set_option maxHeartbeats 200000

theorem root_branch_derivative (r : ℝ) (g : ℝ → ℂ)
    (hg : DifferentiableAt ℝ g r)
    (he : ∀ᶠ s in 𝓝 r, candidatePolynomial s (g s)=0)
    (hs : candidateSlope r (g r) ≠ 0) :
    deriv g r = -candidateParameter (g r)/candidateSlope r (g r) := by
  have hcomp := (candidate_hasDerivAt r (g r)).scomp r hg.hasDerivAt
  have hparam : DifferentiableAt ℝ (fun s => candidateParameter (g s)) r := by
    have hp : Differentiable ℝ candidateParameter := by
      unfold candidateParameter candidatePolynomial
      fun_prop
    exact (hp (g r)).comp r hg
  have hlin : HasDerivAt (fun s : ℝ => ((s-r:ℝ):ℂ)) (1:ℂ) r := by
    exact Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_id r).sub_const r)
  have hsum := hcomp.add (hlin.mul hparam.hasDerivAt)
  have hf : (fun s => candidatePolynomial s (g s)) =
      (fun s => candidatePolynomial r (g s)+((s-r:ℝ):ℂ)*candidateParameter (g s)) := by
    funext s
    exact candidate_affine r s (g s)
  have hd : HasDerivAt (fun s => candidatePolynomial s (g s))
      (deriv g r*candidateSlope r (g r)+candidateParameter (g r)) r := by
    rw [hf]
    simpa [Function.comp_def] using hsum
  have he' : (fun s => candidatePolynomial s (g s)) =ᶠ[𝓝 r] (fun _ => (0:ℂ)) := he
  have hz := (hd.congr_of_eventuallyEq he'.symm).unique
    (hasDerivAt_const (x := r) (c := (0:ℂ)))
  apply (eq_div_iff hs).2
  linear_combination hz

theorem source_root_eigenvector (r : ℝ) (z : ℂ) (hp : candidatePolynomial r z=0) :
    adjugateVector z ≠ 0 ∧ (complexSource r).mulVec (adjugateVector z) = z • adjugateVector z := by
  constructor
  · intro hz
    have hh : companionBasis.mulVec (powerVector z)=0 := by rw [basis_powerVector,hz]
    have hi := congrArg companionInverse.mulVec hh
    simp only [Matrix.mulVec_mulVec,companion_inverse_complex,Matrix.one_mulVec,
      Matrix.mulVec_zero] at hi
    have h0 := congrFun hi 0
    simp [powerVector] at h0
  · ext i
    change ((sourceMatrix r).map (algebraMap ℝ ℂ)).mulVec (adjugateVector z) i = _
    rw [adjugate_residual,hp]
    simp

theorem source_transverse_eigenvalue_branch : ∃ r w : ℝ, ∃ g : ℝ → ℂ,
    0 < r ∧ 0 < w ∧ ContDiffAt ℝ ⊤ g r ∧ g r=Complex.I*(w:ℂ) ∧
    HasDerivAt (fun s => (g s).re) (deriv g r).re r ∧ (deriv g r).re < 0 ∧
    ∀ᶠ s in 𝓝 r, ∃ v : Fin 9 → ℂ, v ≠ 0 ∧ (complexSource s).mulVec v=g s • v := by
  obtain ⟨r,w,v,hr,hw,hv,he⟩ := source_imaginary_eigenpair
  have hp := source_eigenvalue_root r (Complex.I*(w:ℂ)) v hv he
  have hs := candidate_imaginary_root_simple r w (ne_of_gt hw) hp
  obtain ⟨g,hg,hgr,hge⟩ := simple_root_branch r (Complex.I*(w:ℂ)) hp hs
  have hd := (hg.differentiableAt (by simp)).hasDerivAt
  have hq := root_branch_derivative r g (hg.differentiableAt (by simp)) hge
    (by simpa only [hgr] using hs)
  refine ⟨r,w,g,hr,hw,hg,hgr,?_,?_,?_⟩
  · exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt r hd
  · rw [hq,hgr]
    exact candidate_crossing_negative r w (ne_of_gt hw) hp
  · filter_upwards [hge] with s hsp
    exact ⟨adjugateVector (g s),source_root_eigenvector s (g s) hsp⟩

end
end ThreeSitePhosphorylation

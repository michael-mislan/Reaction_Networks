import proofs.ThreeSitePhosphorylation.SmoothPaths
import proofs.ThreeSitePhosphorylation.LinearOrbit

namespace ThreeSitePhosphorylation
noncomputable section
open scoped Topology

theorem source_reference_solution (r w T : ℝ) (v : Fin 9 → ℂ)
    (he : (complexSource r).mulVec v=(Complex.I*(w:ℂ)) • v) :
    pathResidual (((0,(r,T)),realPart v),referencePath (realPart v) (imagPart v) w T)=0 := by
  obtain ⟨ha,hb⟩ := source_eigen_real_imag r w v he
  simp only [pathResidual,pathField,zero_smul,add_zero,linearPicard_pathLinear]
  rw [referencePath_integral (jacobianOperator r) _ _ w T ha hb]
  change (referencePath (realPart v) (imagPart v) w T-ContinuousMap.const UnitTime (realPart v))-
    (referencePath (realPart v) (imagPart v) w T-ContinuousMap.const UnitTime (realPart v))=0
  exact sub_self _

/-- Actual source-specific smooth integral paths around a nonzero periodic
linear orbit. Nonzero-amplitude periodicity is not asserted here. -/
theorem source_smooth_critical_paths : ∃ r w : ℝ, ∃ v : Fin 9 → ℂ, ∃ ψ : FlowData → SourcePath,
    0 < r ∧ 0 < w ∧ realPart v ≠ 0 ∧
    (complexSource r).mulVec v=(Complex.I*(w:ℂ)) • v ∧
    ContDiffAt ℝ ⊤ ψ ((0,(r,2*Real.pi/w)),realPart v) ∧
    ψ ((0,(r,2*Real.pi/w)),realPart v)=referencePath (realPart v) (imagPart v) w (2*Real.pi/w) ∧
    referencePath (realPart v) (imagPart v) w (2*Real.pi/w) ⟨0,by norm_num⟩=realPart v ∧
    referencePath (realPart v) (imagPart v) w (2*Real.pi/w) ⟨1,by norm_num⟩=realPart v ∧
    ∀ᶠ p in 𝓝 ((0,(r,2*Real.pi/w)),realPart v), pathResidual (p,ψ p)=0 := by
  obtain ⟨r,w,v,hr,hw,hv,he⟩ := source_imaginary_eigenpair
  have hreal := source_eigen_real_nonzero r w (ne_of_gt hw) v hv he
  obtain ⟨ψ,hψ,hψ0,hψeq⟩ := smooth_full_interval_paths r (2*Real.pi/w) (realPart v)
    (referencePath (realPart v) (imagPart v) w (2*Real.pi/w))
    (source_reference_solution r w (2*Real.pi/w) v he)
  obtain ⟨h0,h1⟩ := referencePath_endpoints (realPart v) (imagPart v) w (ne_of_gt hw)
  exact ⟨r,w,v,ψ,hr,hw,hreal,he,hψ,hψ0,h0,h1,hψeq⟩

end
end ThreeSitePhosphorylation

import proofs.ThreeSitePhosphorylation.SpectrumNecessary
import proofs.ThreeSitePhosphorylation.PolynomialIsolation

namespace ThreeSitePhosphorylation
noncomputable section

/-- Every imaginary source eigenvalue lies at the unique critical frequency.
This asserts spectral exclusion, not algebraic simplicity or Hopf. -/
theorem source_imaginary_spectrum_isolated : ∃ r w : ℝ, ∃ v : Fin 9 → ℂ,
    0 < r ∧ 0 < w ∧ v ≠ 0 ∧
    (complexSource r).mulVec v = (Complex.I*(w:ℂ)) • v ∧
    ∀ a : ℝ, ∀ u : Fin 9 → ℂ, u ≠ 0 →
      (complexSource r).mulVec u = (Complex.I*(a:ℂ)) • u → a^2=w^2 := by
  obtain ⟨r,w,v,hr,hw,hv,he⟩ := source_imaginary_eigenpair
  change (complexSource r).mulVec v = (Complex.I*(w:ℂ)) • v at he
  have hp := source_eigenvalue_root r (Complex.I*(w:ℂ)) v hv he
  have hphi := eliminant_zero_of_root r w (ne_of_gt hw) hp
  refine ⟨r,w,v,hr,hw,hv,he,?_⟩
  intro a u hu hue
  exact candidate_imaginary_frequency_unique r hr (w^2) (sq_pos_of_pos hw) hphi a
    (source_eigenvalue_root r (Complex.I*(a:ℂ)) u hu hue)

end
end ThreeSitePhosphorylation

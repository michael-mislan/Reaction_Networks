import proofs.ThreeSitePhosphorylation.LeftProjection
import proofs.ThreeSitePhosphorylation.LinearOrbit
import proofs.ThreeSitePhosphorylation.ScalarODE

namespace ThreeSitePhosphorylation
noncomputable section
set_option maxHeartbeats 20000

theorem basis_coord_eigen {ι : Type*} (b : Module.Basis ι ℂ (Fin 9 → ℂ))
    (A : Matrix (Fin 9) (Fin 9) ℂ) (z : ι → ℂ)
    (he : ∀ i, A.mulVec (b i)=z i • b i) (i : ι) (v : Fin 9 → ℂ) :
    b.coord i (A.mulVec v)=z i*b.coord i v := by
  have hh : (b.coord i).comp A.mulVecLin = z i • b.coord i := by
    apply b.ext
    intro j
    simp only [LinearMap.comp_apply,Matrix.mulVecLin_apply,he,map_smul,
      LinearMap.smul_apply,smul_eq_mul,Module.Basis.coord_apply,Module.Basis.repr_self]
    by_cases h : j=i <;> simp [h]
  exact LinearMap.congr_fun hh v

theorem sourceLeft_is_coord (r w : ℝ) (hw : 0<w)
    (hp : candidatePolynomial r (Complex.I*(w:ℂ))=0)
    (x : Fin 7 → ℝ) (hx : StrictMono x) (hn : ∀ i, x i<0)
    (b : Module.Basis SpectralIndex ℂ (Fin 9 → ℂ))
    (hb : ∀ i, b i=adjugateVector (spectralValues x w i))
    (he : ∀ i, (complexSource r).mulVec (b i)=spectralValues x w i • b i) :
    sourceLeft r (Complex.I*(w:ℂ))=b.coord (Sum.inr 0) := by
  apply b.ext
  intro i
  by_cases hi : i=Sum.inr 0
  · subst i
    conv_lhs => rw [hb]
    change sourceLeft r (Complex.I*(w:ℂ)) (adjugateVector (Complex.I*(w:ℂ)))=_
    rw [sourceLeft_normalized r _ (candidate_imaginary_root_simple r w (ne_of_gt hw) hp)]
    simp [Module.Basis.coord_apply]
  · have hz : Complex.I*(w:ℂ) ≠ spectralValues x w i := by
      intro hh
      change spectralValues x w (Sum.inr 0)=spectralValues x w i at hh
      have ht := (spectralValues_injective x hx hn w hw) hh
      exact hi ht.symm
    rw [sourceLeft_other_eigen r _ _ hp hz _ (he i)]
    simp [Module.Basis.coord_apply,hi]

theorem real_vector_imaginary_eigen_zero (r w : ℝ) (hw : w ≠ 0) (v : Fin 9 → ℂ)
    (hv : imagPart v=0)
    (he : (complexSource r).mulVec v=(Complex.I*(w:ℂ)) • v) : v=0 := by
  have hh := (source_eigen_real_imag r w v he).2
  rw [hv,map_zero] at hh
  have hr : realPart v=0 := (smul_eq_zero.mp hh.symm).resolve_left hw
  ext i
  exact Complex.ext (congrFun hr i) (congrFun hv i)

end
end ThreeSitePhosphorylation

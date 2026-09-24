import proofs.ThreeSitePhosphorylation.HomogeneousKernel
import proofs.ThreeSitePhosphorylation.ResonantKernel
import proofs.ThreeSitePhosphorylation.ComplexOrbit

namespace ThreeSitePhosphorylation
noncomputable section

theorem source_periodic_variation_kernel (r w : ℝ) (hw : 0<w)
    (hp : candidatePolynomial r (Complex.I*(w:ℂ))=0) (dr dT : ℝ)
    (u : ℝ → (Fin 9 → ℂ)) (hper : u 1=u 0) (hr : imagPart (u 0)=0)
    (hc : sourceLeft r (Complex.I*(w:ℂ)) (u 0)=0)
    (hu : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt u
      (((2*Real.pi/w:ℝ):ℂ) • (complexSource r).mulVec (u t)+
        (dT:ℂ) • (complexSource r).mulVec
          (harmonicVector (adjugateVector (Complex.I*(w:ℂ)))
            (conjugateVector (adjugateVector (Complex.I*(w:ℂ)))) t)+
        (((2*Real.pi/w:ℝ):ℂ)*(dr:ℂ)) • sourceDelta.mulVec
          (harmonicVector (adjugateVector (Complex.I*(w:ℂ)))
            (conjugateVector (adjugateVector (Complex.I*(w:ℂ)))) t)) t) :
    dr=0 ∧ dT=0 ∧ u 0=0 := by
  let z : ℂ := Complex.I*(w:ℂ)
  let v := adjugateVector z
  have hz : z ≠ -Complex.I*(w:ℂ) := by
    intro h
    have hh := congrArg Complex.im h
    simp [z] at hh
    linarith
  have hv := (source_root_eigenvector r z hp).2
  have hm : sourceLeft r z (conjugateVector v)=0 :=
    sourceLeft_other_eigen r z _ hp hz _ (conjugate_eigen r w v hv)
  have hT : 0<2*Real.pi/w := by positivity
  have ht : ((2*Real.pi/w:ℝ):ℂ)*z=turnFrequency := by
    dsimp [z,turnFrequency]
    push_cast
    field_simp
    exact div_self (by exact_mod_cast ne_of_gt hw)
  obtain ⟨hdr,hdt⟩ := resonant_parameter_kernel (complexSource r).mulVecLin
    sourceDelta.mulVecLin (sourceLeft r z) z v (conjugateVector v)
    (sourceLeft_eigen r z hp)
    (sourceLeft_normalized r z (candidate_imaginary_root_simple r w (ne_of_gt hw) hp))
    hm (sourceLeft_crossing_real_negative r w (ne_of_gt hw) hp)
    w (2*Real.pi/w) dr dT hw hT rfl ht u hper hu
  obtain ⟨x,hx,hn,b,hb,he⟩ := source_eigenbasis r w hw hp
  have hcoord : b.coord (Sum.inr 0) (u 0)=0 := by
    rw [← sourceLeft_is_coord r w hw hp x hx hn b hb he]
    exact hc
  have hhom : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivAt u ((2*Real.pi/w) • (complexSource r).mulVec (u t)) t := by
    intro t ht'
    have hh := hu t ht'
    simp only [hdr,hdt,Complex.ofReal_zero,zero_smul,mul_zero,add_zero] at hh
    convert hh using 1
  exact ⟨hdr,hdt,periodic_homogeneous_source_kernel r w (2*Real.pi/w) hw hT x hn b he
    u hhom hper hcoord hr⟩

end
end ThreeSitePhosphorylation

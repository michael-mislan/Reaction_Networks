import proofs.ThreeSitePhosphorylation.SourceVariationalKernel
import proofs.ThreeSitePhosphorylation.VariationalODE

namespace ThreeSitePhosphorylation
noncomputable section

theorem complexify_delta (y : ReducedState) :
    complexify ((jacobianOperator 1-jacobianOperator 0) y)=sourceDelta.mulVec (complexify y) := by
  simp only [ContinuousLinearMap.sub_apply,map_sub,complexify_source,sourceDelta,Matrix.sub_mulVec]

theorem periodic_path_kernel (r w : ℝ) (hw : 0<w)
    (hp : candidatePolynomial r (Complex.I*(w:ℂ))=0)
    (dr dT : ℝ) (dx : ReducedState) (q : SourcePath)
    (he : q=constantPath dx+linearPicard (ContinuousLinearMap.id ℝ ReducedState)
      (variationField r (2*Real.pi/w) dr dT
        (referencePath (realPart (adjugateVector (Complex.I*(w:ℂ))))
          (imagPart (adjugateVector (Complex.I*(w:ℂ)))) w (2*Real.pi/w)) q))
    (hper : q ⟨1,by norm_num⟩=q ⟨0,by norm_num⟩)
    (hn : sourceLeft r (Complex.I*(w:ℂ)) (complexify dx)=0) : dr=0 ∧ dT=0 ∧ dx=0 := by
  let v := adjugateVector (Complex.I*(w:ℂ))
  let u0 := referencePath (realPart v) (imagPart v) w (2*Real.pi/w)
  let f := variationField r (2*Real.pi/w) dr dT u0 q
  let u : ℝ → (Fin 9 → ℂ) := fun t => complexify (integralVariation dx f t)
  have hinit : u 0=complexify dx := by simp [u,integralVariation_initial]
  have hp' : u 1=u 0 := by
    change complexify (integralVariation dx f 1)=complexify (integralVariation dx f 0)
    rw [integralVariation_eq dx f q he ⟨1,by norm_num⟩,
      integralVariation_eq dx f q he ⟨0,by norm_num⟩,hper]
  have hr : imagPart (u 0)=0 := by rw [hinit]; ext i; simp [imagPart]
  have hc : sourceLeft r (Complex.I*(w:ℂ)) (u 0)=0 := by rwa [hinit]
  have hbase (t : UnitTime) : complexify (u0 t)=harmonicVector v (conjugateVector v) t := by
    exact normalized_orbit_harmonics v w (ne_of_gt hw) t
  have hd (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :=
    complexify.hasFDerivAt.comp_hasDerivAt t (variational_ode r (2*Real.pi/w) dr dT dx u0 q he t ht)
  have hu : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt u
      (((2*Real.pi/w:ℝ):ℂ) • (complexSource r).mulVec (u t)+
        (dT:ℂ) • (complexSource r).mulVec (harmonicVector v (conjugateVector v) t)+
        (((2*Real.pi/w:ℝ):ℂ)*(dr:ℂ)) • sourceDelta.mulVec
          (harmonicVector v (conjugateVector v) t)) t := by
    intro t ht
    have hh := hd t ht
    simp only [map_add,map_smul,complexify_source,complexify_delta,hbase] at hh
    convert hh using 1
    ext i
    simp [u,f,smul_smul,mul_assoc]
  obtain ⟨hdr,hdt,hzero⟩ := source_periodic_variation_kernel r w hw hp dr dT u hp' hr hc hu
  refine ⟨hdr,hdt,?_⟩
  rw [hinit] at hzero
  ext i
  have hi := congrFun hzero i
  simp only [complexify_apply,Pi.zero_apply] at hi
  exact Complex.ofReal_injective hi

end
end ThreeSitePhosphorylation

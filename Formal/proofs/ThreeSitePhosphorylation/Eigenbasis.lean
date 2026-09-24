import proofs.ThreeSitePhosphorylation.RealSpectrum
import proofs.ThreeSitePhosphorylation.ParameterDomain
import proofs.ThreeSitePhosphorylation.TransverseBranch

namespace ThreeSitePhosphorylation
noncomputable section
set_option maxHeartbeats 300000

abbrev SpectralIndex := Fin 7 ⊕ Fin 2

def spectralValues (x : Fin 7 → ℝ) (w : ℝ) : SpectralIndex → ℂ :=
  Sum.elim (fun i => (x i:ℂ)) (fun j => Complex.I*((![w,-w] j:ℝ):ℂ))

theorem spectralValues_injective (x : Fin 7 → ℝ) (hx : StrictMono x)
    (hn : ∀ i, x i<0) (w : ℝ) (hw : 0<w) : Function.Injective (spectralValues x w) := by
  intro i j hij
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have he : x i=x j := Complex.ofReal_injective hij
      exact congrArg Sum.inl (hx.injective he)
    | inr j =>
      have he := congrArg Complex.re hij
      fin_cases j <;> simp [spectralValues] at he <;> linarith [hn i]
  | inr i =>
    cases j with
    | inl j =>
      have he := congrArg Complex.re hij
      fin_cases i <;> simp [spectralValues] at he <;> linarith [hn j]
    | inr j =>
      have he := congrArg Complex.im hij
      fin_cases i <;> fin_cases j <;> simp [spectralValues] at he ⊢ <;> linarith

theorem realCandidate_root (r x : ℝ) (hx : realCandidate r x=0) :
    candidatePolynomial r (x:ℂ)=0 := by
  apply Complex.ext
  · exact hx
  · simp [candidatePolynomial,pow_succ,Complex.mul_im,Complex.mul_re]

theorem source_eigenbasis (r w : ℝ) (hw : 0<w)
    (hp : candidatePolynomial r (Complex.I*(w:ℂ))=0) :
    ∃ x : Fin 7 → ℝ, StrictMono x ∧ (∀ i, x i<0) ∧
      ∃ b : Module.Basis SpectralIndex ℂ (Fin 9 → ℂ),
        (∀ i, b i=adjugateVector (spectralValues x w i)) ∧
        ∀ i, (complexSource r).mulVec (b i)=spectralValues x w i • b i := by
  have hr := imaginary_parameter_domain r w (ne_of_gt hw) hp
  obtain ⟨x,hx,hroots⟩ := seven_negative_roots r hr.1.le hr.2.le
  have hn : ∀ i, x i<0 := fun i => (hroots i).1
  have hi := spectralValues_injective x hx hn w hw
  have hroot : ∀ i : SpectralIndex, candidatePolynomial r (spectralValues x w i)=0 := by
    intro i
    cases i with
    | inl i => exact realCandidate_root r (x i) (hroots i).2
    | inr j =>
      obtain ⟨he,ho⟩ := frequency_equations_of_root r w (ne_of_gt hw) hp
      fin_cases j
      · simpa only [spectralValues,Sum.elim_inr,Matrix.cons_val_zero] using hp
      · change candidatePolynomial r (Complex.I*((-w:ℝ):ℂ))=0
        rw [candidate_at_imaginary,neg_sq,he,ho]
        simp
  have hev : ∀ i : SpectralIndex,
      Module.End.HasEigenvector (complexSource r).mulVecLin (spectralValues x w i)
        (adjugateVector (spectralValues x w i)) := by
    intro i
    obtain ⟨hv,he⟩ := source_root_eigenvector r (spectralValues x w i) (hroot i)
    exact ⟨by simpa only [Module.End.mem_eigenspace_iff] using he,hv⟩
  have hlin := Module.End.eigenvectors_linearIndependent' (complexSource r).mulVecLin
    (spectralValues x w) hi (fun i => adjugateVector (spectralValues x w i)) hev
  have hcard : Fintype.card SpectralIndex=Module.finrank ℂ (Fin 9 → ℂ) := by
    simp [SpectralIndex]
  let b := basisOfLinearIndependentOfCardEqFinrank hlin hcard
  have hb : ∀ i, b i=adjugateVector (spectralValues x w i) := by
    intro i
    exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hlin hcard) i
  refine ⟨x,hx,hn,b,hb,?_⟩
  intro i
  rw [hb]
  exact (source_root_eigenvector r (spectralValues x w i) (hroot i)).2

end
end ThreeSitePhosphorylation

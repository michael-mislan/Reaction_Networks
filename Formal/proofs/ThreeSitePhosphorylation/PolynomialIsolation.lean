import proofs.ThreeSitePhosphorylation.Polynomial
import proofs.ThreeSitePhosphorylation.FrequencyUnique

namespace ThreeSitePhosphorylation
noncomputable section
set_option maxHeartbeats 100000

theorem frequency_equations_of_root (r w : ℝ) (hw : w ≠ 0)
    (hp : candidatePolynomial r (Complex.I*(w:ℂ)) = 0) :
    even0 (w^2)+r*even1 (w^2)=0 ∧ odd0 (w^2)+r*odd1 (w^2)=0 := by
  rw [candidate_at_imaginary] at hp
  have he := congrArg Complex.re hp
  have ho := congrArg Complex.im hp
  simp at he ho
  exact ⟨he,ho.resolve_left hw⟩

theorem eliminant_zero_of_root (r w : ℝ) (hw : w ≠ 0)
    (hp : candidatePolynomial r (Complex.I*(w:ℂ)) = 0) :
    frequencyPolynomial (w^2)=0 := by
  obtain ⟨he,ho⟩ := frequency_equations_of_root r w hw hp
  rw [frequency_elimination_identity]
  linear_combination even1 (w^2)*ho-odd1 (w^2)*he

theorem candidate_zero_excluded (r : ℝ) (hr : 0 < r) : candidatePolynomial r 0 ≠ 0 := by
  intro hp
  have hz := congrArg Complex.re hp
  norm_num [candidatePolynomial] at hz
  linarith

theorem candidate_imaginary_frequency_unique (r : ℝ) (hr : 0 < r)
    (t : ℝ) (ht : 0 < t) (hphi : frequencyPolynomial t=0)
    (w : ℝ) (hp : candidatePolynomial r (Complex.I*(w:ℂ)) = 0) : w^2=t := by
  have hw : w ≠ 0 := by
    intro hz
    rw [hz] at hp
    simp only [Complex.ofReal_zero,mul_zero] at hp
    exact candidate_zero_excluded r hr hp
  exact positive_frequency_unique (w^2) t (sq_pos_of_ne_zero hw) ht
    (eliminant_zero_of_root r w hw hp) hphi

end
end ThreeSitePhosphorylation

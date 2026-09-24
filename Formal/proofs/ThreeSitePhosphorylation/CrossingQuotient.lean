import proofs.ThreeSitePhosphorylation.SimpleRoot

namespace ThreeSitePhosphorylation
noncomputable section
set_option maxHeartbeats 200000

def candidateParameter (z : ℂ) : ℂ := candidatePolynomial 1 z-candidatePolynomial 0 z

theorem candidate_affine (r s : ℝ) (z : ℂ) :
    candidatePolynomial s z = candidatePolynomial r z + ((s-r:ℝ):ℂ)*candidateParameter z := by
  unfold candidateParameter candidatePolynomial
  push_cast
  ring

theorem candidate_parameter_at_imaginary (w : ℝ) :
    candidateParameter (Complex.I*(w:ℂ)) =
      (even1 (w^2):ℂ)+Complex.I*(w:ℂ)*(odd1 (w^2):ℂ) := by
  unfold candidateParameter
  rw [candidate_at_imaginary,candidate_at_imaginary]
  push_cast
  ring

theorem complex_crossing_real (w E O dE dO : ℝ) (hw : w ≠ 0)
    (hd : 0 < w^2*dO^2+dE^2) :
    (-((E:ℂ)+Complex.I*(w:ℂ)*(O:ℂ))/
      (((2*w^2*dO:ℝ):ℂ)-Complex.I*((2*w*dE:ℝ):ℂ))).re =
      -(E*dO-O*dE)/(2*(w^2*dO^2+dE^2)) := by
  rw [Complex.div_re]
  simp only [Complex.neg_re,Complex.neg_im,Complex.add_re,Complex.add_im,
    Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,mul_zero,
    one_mul,zero_add,add_zero,sub_zero,zero_sub,Complex.normSq_apply]
  have he : (2*w^2*dO)*(2*w^2*dO)+(-(2*w*dE))*(-(2*w*dE)) =
      4*w^2*(w^2*dO^2+dE^2) := by ring
  rw [he]
  have hw2 : w^2 ≠ 0 := pow_ne_zero _ hw
  have hn : w^2*dO^2+dE^2 ≠ 0 := ne_of_gt hd
  field_simp
  ring

theorem candidate_crossing_negative (r w : ℝ) (hw : w ≠ 0)
    (hp : candidatePolynomial r (Complex.I*(w:ℂ))=0) :
    (-candidateParameter (Complex.I*(w:ℂ))/candidateSlope r (Complex.I*(w:ℂ))).re < 0 := by
  obtain ⟨he,ho⟩ := frequency_equations_of_root r w hw hp
  have ht := sq_pos_of_ne_zero hw
  have htrans := frequency_transverse (w^2) r ht he ho
  rw [candidate_parameter_at_imaginary,candidate_slope_at_imaginary,ho,zero_add,
    complex_crossing_real w _ _ _ _ hw htrans.1,← frequency_orientation (w^2) r he ho]
  exact htrans.2

end
end ThreeSitePhosphorylation

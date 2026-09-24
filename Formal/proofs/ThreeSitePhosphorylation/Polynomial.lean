import proofs.ThreeSitePhosphorylation.FrequencyData

namespace ThreeSitePhosphorylation
noncomputable section
set_option maxHeartbeats 1000000

/-- The candidate reduced polynomial. Its equality with the literal source
Jacobian's characteristic polynomial is a separate obligation. -/
def candidatePolynomial (r : ℝ) (z : ℂ) : ℂ :=
    (((1/1:ℝ)+r*(0/1:ℝ)):ℂ)*z^9 +
    (((21549480866197/53063010000:ℝ)+r*(716/6045:ℝ)):ℂ)*z^8 +
    (((1914250662484005497/49272795000000:ℝ)+r*(244167141079021/5173643475000:ℝ)):ℂ)*z^7 +
    (((3070471513831161895424219/2522151194062500000:ℝ)+r*(1743145840777470340069/403544191050000000:ℝ)):ℂ)*z^6 +
    (((178228249672628679513269034107/15132907164375000000000:ℝ)+r*(41210428898350734288350941/302658143287500000000:ℝ)):ℂ)*z^5 +
    (((3747333761964530151289376279869/151329071643750000000000:ℝ)+r*(19351917652493567002237891771/15132907164375000000000:ℝ)):ℂ)*z^4 +
    (((1095227502621761760478226249101/226993607465625000000000:ℝ)+r*(298391200108946577505242797723/113496803732812500000000:ℝ)):ℂ)*z^3 +
    (((676438287388827146536247537/1269894307500000000000:ℝ)+r*(15669391757369638993598066707/13968837382500000000000:ℝ)):ℂ)*z^2 +
    (((2365405597729059858828139/17908765875000000000:ℝ)+r*(2369048939115567901134889/17908765875000000000:ℝ)):ℂ)*z^1 +
    (((1182316803067886887/3061327500000000:ℝ)+r*(1182316803067886887/3061327500000000:ℝ)):ℂ)*z^0

theorem candidate_at_imaginary (r w : ℝ) :
    candidatePolynomial r (Complex.I*(w:ℂ)) =
      ((even0 (w^2)+r*even1 (w^2):ℝ):ℂ) +
      Complex.I*(w:ℂ)*((odd0 (w^2)+r*odd1 (w^2):ℝ):ℂ) := by
  apply Complex.ext <;>
    simp [candidatePolynomial,even0,odd0,even1,odd1,pow_succ,
      Complex.mul_re,Complex.mul_im] <;> ring

theorem candidate_has_imaginary_pair : ∃ r w : ℝ,
    0 < r ∧ 0 < w ∧ candidatePolynomial r (Complex.I*(w:ℂ)) = 0 := by
  obtain ⟨t,r,ht,hr,_hl,_hu,he,ho⟩ := admissible_frequency_exists
  refine ⟨r,Real.sqrt t,hr,Real.sqrt_pos.2 ht,?_⟩
  rw [candidate_at_imaginary,Real.sq_sqrt ht.le,he,ho]
  simp

end
end ThreeSitePhosphorylation

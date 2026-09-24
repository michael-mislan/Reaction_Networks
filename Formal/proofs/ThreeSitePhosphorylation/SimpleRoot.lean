import proofs.ThreeSitePhosphorylation.Derivatives
import proofs.ThreeSitePhosphorylation.PolynomialIsolation

namespace ThreeSitePhosphorylation
noncomputable section
set_option maxHeartbeats 300000

def candidateSlope (r : ℝ) (z : ℂ) : ℂ :=
    (((1/1:ℝ)+r*(0/1:ℝ)):ℂ)*9*z^8 +
    (((21549480866197/53063010000:ℝ)+r*(716/6045:ℝ)):ℂ)*8*z^7 +
    (((1914250662484005497/49272795000000:ℝ)+r*(244167141079021/5173643475000:ℝ)):ℂ)*7*z^6 +
    (((3070471513831161895424219/2522151194062500000:ℝ)+r*(1743145840777470340069/403544191050000000:ℝ)):ℂ)*6*z^5 +
    (((178228249672628679513269034107/15132907164375000000000:ℝ)+r*(41210428898350734288350941/302658143287500000000:ℝ)):ℂ)*5*z^4 +
    (((3747333761964530151289376279869/151329071643750000000000:ℝ)+r*(19351917652493567002237891771/15132907164375000000000:ℝ)):ℂ)*4*z^3 +
    (((1095227502621761760478226249101/226993607465625000000000:ℝ)+r*(298391200108946577505242797723/113496803732812500000000:ℝ)):ℂ)*3*z^2 +
    (((676438287388827146536247537/1269894307500000000000:ℝ)+r*(15669391757369638993598066707/13968837382500000000000:ℝ)):ℂ)*2*z^1 +
    (((2365405597729059858828139/17908765875000000000:ℝ)+r*(2369048939115567901134889/17908765875000000000:ℝ)):ℂ)*1*z^0

theorem candidate_hasDerivAt (r : ℝ) (z : ℂ) :
    HasDerivAt (candidatePolynomial r) (candidateSlope r z) z := by
  convert (((((((((((hasDerivAt_pow 9 z).const_mul (((1/1:ℝ)+r*(0/1:ℝ)):ℂ)).add ((hasDerivAt_pow 8 z).const_mul (((21549480866197/53063010000:ℝ)+r*(716/6045:ℝ)):ℂ))).add ((hasDerivAt_pow 7 z).const_mul (((1914250662484005497/49272795000000:ℝ)+r*(244167141079021/5173643475000:ℝ)):ℂ))).add ((hasDerivAt_pow 6 z).const_mul (((3070471513831161895424219/2522151194062500000:ℝ)+r*(1743145840777470340069/403544191050000000:ℝ)):ℂ))).add ((hasDerivAt_pow 5 z).const_mul (((178228249672628679513269034107/15132907164375000000000:ℝ)+r*(41210428898350734288350941/302658143287500000000:ℝ)):ℂ))).add ((hasDerivAt_pow 4 z).const_mul (((3747333761964530151289376279869/151329071643750000000000:ℝ)+r*(19351917652493567002237891771/15132907164375000000000:ℝ)):ℂ))).add ((hasDerivAt_pow 3 z).const_mul (((1095227502621761760478226249101/226993607465625000000000:ℝ)+r*(298391200108946577505242797723/113496803732812500000000:ℝ)):ℂ))).add ((hasDerivAt_pow 2 z).const_mul (((676438287388827146536247537/1269894307500000000000:ℝ)+r*(15669391757369638993598066707/13968837382500000000000:ℝ)):ℂ))).add ((hasDerivAt_pow 1 z).const_mul (((2365405597729059858828139/17908765875000000000:ℝ)+r*(2369048939115567901134889/17908765875000000000:ℝ)):ℂ))).add ((hasDerivAt_pow 0 z).const_mul (((1182316803067886887/3061327500000000:ℝ)+r*(1182316803067886887/3061327500000000:ℝ)):ℂ))) using 1
  norm_num [candidatePolynomial,candidateSlope]
  ring

theorem candidate_slope_at_imaginary (r w : ℝ) :
    candidateSlope r (Complex.I*(w:ℂ)) =
      ((odd0 (w^2)+r*odd1 (w^2)+2*w^2*(odd0Slope (w^2)+r*odd1Slope (w^2)):ℝ):ℂ) -
      Complex.I*((2*w*(even0Slope (w^2)+r*even1Slope (w^2)):ℝ):ℂ) := by
  apply Complex.ext <;>
    simp [candidateSlope,odd0,odd1,odd0Slope,odd1Slope,even0Slope,even1Slope,
      pow_succ,Complex.mul_re,Complex.mul_im] <;> ring

theorem candidate_imaginary_root_simple (r w : ℝ) (hw : w ≠ 0)
    (hp : candidatePolynomial r (Complex.I*(w:ℂ))=0) :
    candidateSlope r (Complex.I*(w:ℂ)) ≠ 0 := by
  obtain ⟨he,ho⟩ := frequency_equations_of_root r w hw hp
  have ht := sq_pos_of_ne_zero hw
  have hpos := (frequency_transverse (w^2) r ht he ho).1
  intro hz
  rw [candidate_slope_at_imaginary,ho,zero_add] at hz
  have hr := congrArg Complex.re hz
  have hi := congrArg Complex.im hz
  simp [pow_two,Complex.mul_re,Complex.mul_im,hw] at hr hi
  have hdo : odd0Slope (w^2)+r*odd1Slope (w^2)=0 := by
    simpa only [pow_two] using hr
  have hde : even0Slope (w^2)+r*even1Slope (w^2)=0 := by
    simpa only [pow_two] using hi
  rw [hdo,hde] at hpos
  norm_num at hpos

end
end ThreeSitePhosphorylation

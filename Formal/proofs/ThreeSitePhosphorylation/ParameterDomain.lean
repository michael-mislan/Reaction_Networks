import proofs.ThreeSitePhosphorylation.PolynomialIsolation

namespace ThreeSitePhosphorylation
noncomputable section
set_option maxHeartbeats 300000

theorem frequency_ratio_domain (t r : ℝ)
    (ht : frequencyLower ≤ t ∧ t ≤ frequencyUpper)
    (he : even0 t+r*even1 t=0) : (1/4:ℝ)<r ∧ r<(3/10:ℝ) := by
  have hs := (frequency_even_signs t ht).2
  have hl : (0:ℝ) ≤ frequencyLower := by norm_num [frequencyLower]
  have ht0 : 0 ≤ t := hl.trans ht.1
  have h2 : frequencyLower^2 ≤ t^2 ∧ t^2 ≤ frequencyUpper^2 := by
    constructor <;> gcongr
    · exact ht.1
    · exact ht.2
  have h3 : frequencyLower^3 ≤ t^3 ∧ t^3 ≤ frequencyUpper^3 := by
    constructor <;> gcongr
    · exact ht.1
    · exact ht.2
  have h4 : frequencyLower^4 ≤ t^4 ∧ t^4 ≤ frequencyUpper^4 := by
    constructor <;> gcongr
    · exact ht.1
    · exact ht.2
  norm_num [frequencyLower,frequencyUpper] at ht h2 h3 h4
  have hp : 0 < even0 t+(1/4:ℝ)*even1 t := by
    unfold even0 even1
    linarith only [ht.1,ht.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]
  have hn : even0 t+(3/10:ℝ)*even1 t < 0 := by
    unfold even0 even1
    linarith only [ht.1,ht.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]
  constructor <;> nlinarith

theorem imaginary_parameter_domain (r w : ℝ) (hw : w ≠ 0)
    (hp : candidatePolynomial r (Complex.I*(w:ℂ))=0) : (1/4:ℝ)<r ∧ r<(3/10:ℝ) := by
  obtain ⟨t,hl,hu,ht,hphi⟩ := positive_frequency_exists
  have heq : w^2=t := positive_frequency_unique (w^2) t (sq_pos_of_ne_zero hw) ht
    (eliminant_zero_of_root r w hw hp) hphi
  have he := (frequency_equations_of_root r w hw hp).1
  rw [heq] at he
  exact frequency_ratio_domain t r ⟨hl,hu⟩ he

end
end ThreeSitePhosphorylation

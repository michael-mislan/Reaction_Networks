import proofs.CoreCouplingCAC.Preservation

namespace DisguisedToricAssemblies
open CoreCouplingCAC

noncomputable def admissibleCut (p : Rates) : ℝ :=
  max 0 (p.u*(1-p.d)/(p.v*(1+2*p.d)))

noncomputable def threshold (p : Rates) : ℝ :=
  (p.a+2*p.b)*(p.e-1)/(p.e*(p.a+p.b)^2)-2

theorem cut_nonneg (p : Rates) : 0 ≤ admissibleCut p := le_max_left _ _

theorem cut_linear (p : Rates) (hp : p.Positive) (z : ℝ) (hz : admissibleCut p ≤ z) :
    p.u*(1-p.d) ≤ p.v*(1+2*p.d)*z := by
  have hc : 0 < p.v*(1+2*p.d) := by
    have := hp.2.2.2.1
    have := hp.2.2.2.2.2
    positivity
  have hd : p.u*(1-p.d)/(p.v*(1+2*p.d)) ≤ z := (le_max_right _ _).trans hz
  have hh := (div_le_iff₀ hc).mp hd
  nlinarith

theorem admissible_K_nonneg (p : Rates) (hp : p.Positive) (z : ℝ)
    (hz : admissibleCut p ≤ z) : 0 ≤ reducedK p z := by
  have hz0 := (cut_nonneg p).trans hz
  have hl := cut_linear p hp z hz
  have hd := hp.2.2.2.2.2
  unfold reducedK
  apply div_nonneg _ (by linarith)
  nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hl)]

theorem K_nonneg_iff_cut (p : Rates) (hp : p.Positive) (z : ℝ) (hz : 0 < z) :
    0 ≤ reducedK p z ↔ admissibleCut p ≤ z := by
  constructor
  · intro hk
    have hc : 0 < p.v*(1+2*p.d) := by
      have := hp.2.2.2.1
      have := hp.2.2.2.2.2
      positivity
    have hd : 0 < 2+p.d := by have := hp.2.2.2.2.2; linarith
    have hn := (le_div_iff₀ hd).mp hk
    have hl : p.u*(1-p.d) ≤ z*(p.v*(1+2*p.d)) := by
      by_contra hh
      have hlt := mul_neg_of_pos_of_neg hz (sub_neg.mpr (lt_of_not_ge hh))
      nlinarith
    exact max_le hz.le ((div_le_iff₀ hc).mpr hl)
  · exact admissible_K_nonneg p hp z

theorem admissible_A_nonneg (p : Rates) (hp : p.Positive) (z : ℝ)
    (hz : admissibleCut p ≤ z) : 0 ≤ reducedA p z := by
  have hz0 := (cut_nonneg p).trans hz
  have hb : 0 ≤ reducedB p z := by
    have := hp.1
    have := hp.2.1
    unfold reducedB
    positivity
  exact add_nonneg (mul_nonneg hz0 hb) (admissible_K_nonneg p hp z hz)

theorem admissible_increasing (p : Rates) (hp : p.Positive) (x y : ℝ)
    (hx : admissibleCut p ≤ x) (hxy : x < y) :
    reducedA p x < reducedA p y ∧ residual p x < residual p y := by
  have hx0 := (cut_nonneg p).trans hx
  have hy0 : 0 < y := lt_of_le_of_lt hx0 hxy
  have hdx : 0 < x+2 := by linarith
  have hdy : 0 < y+2 := by linarith
  have hdd : 0 < 2+p.d := by have := hp.2.2.2.2.2; linarith
  have hc : 0 < p.a+2*p.b := by have := hp.1; have := hp.2.1; positivity
  have hC : 0 < p.v*(1+2*p.d) := by
    have := hp.2.2.2.1
    have := hp.2.2.2.2.2
    positivity
  have hB : reducedB p y < reducedB p x := by
    unfold reducedB
    apply (div_lt_div_iff₀ hdy hdx).2
    nlinarith [mul_pos hc (sub_pos.mpr hxy)]
  have hK : reducedK p x < reducedK p y := by
    have hid : reducedK p y-reducedK p x =
        (y-x)*(p.v*(1+2*p.d)*(x+y)-p.u*(1-p.d))/(2+p.d) := by
      unfold reducedK
      field_simp
      ring
    have hl := cut_linear p hp x hx
    have ht : 0 < p.v*(1+2*p.d)*(x+y)-p.u*(1-p.d) := by
      nlinarith [mul_pos hC hy0]
    apply sub_pos.mp
    rw [hid]
    exact div_pos (mul_pos (sub_pos.mpr hxy) ht) hdd
  have hA : reducedA p x < reducedA p y := by
    have hi₁ := port_identity p x (ne_of_gt hdx)
    have hi₂ := port_identity p y (ne_of_gt hdy)
    unfold reducedA
    linarith
  have hAp := admissible_A_nonneg p hp x hx
  have hs : (reducedA p x)^2 < (reducedA p y)^2 := by nlinarith
  have hs' := mul_lt_mul_of_pos_left hs hp.2.2.2.2.1
  have hb' := mul_lt_mul_of_pos_left hB (by have := hp.2.2.2.2.1; linarith : 0 < 1+p.e)
  refine ⟨hA, ?_⟩
  unfold CoreCouplingCAC.residual
  linarith

end DisguisedToricAssemblies

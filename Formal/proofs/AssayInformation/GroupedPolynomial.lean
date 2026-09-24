import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

set_option maxRecDepth 4096
noncomputable section
namespace AssayInformation

def grouped (B D E G x : ℝ) : ℝ := B-D*x^3+x^201*(E-G*x)
def signedPoly (A B D E G x : ℝ) : ℝ := x^396*grouped B D E G x-A

theorem grouped_derivative (B D E G x : ℝ) :
    HasDerivAt (grouped B D E G)
      (-3*D*x^2+201*x^200*(E-G*x)-G*x^201) x := by
  unfold grouped
  convert (((hasDerivAt_const x B).sub (((hasDerivAt_id x).pow 3).const_mul D)).add
    (((hasDerivAt_id x).pow 201).mul ((hasDerivAt_const x E).sub
      ((hasDerivAt_id x).const_mul G)))) using 1
  simp only [Pi.pow_apply,Pi.sub_apply,id_eq]
  ring

theorem grouped_antitone (B D E G l u : ℝ) (hl : 0 ≤ l)
    (hD : 0 ≤ D) (hG : 0 ≤ G) (hE : 0 ≤ E-G*u)
    (hbound : -3*D*l^2+201*u^200*(E-G*l)-G*l^201 ≤ 0) :
    AntitoneOn (grouped B D E G) (Set.Icc l u) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc l u)
  · unfold grouped; fun_prop
  · intro x _
    exact (grouped_derivative B D E G x).hasDerivWithinAt
  · intro x hx
    have hx' : x ∈ Set.Icc l u := interior_subset hx
    have hx0 := hl.trans hx'.1
    have h2 := pow_le_pow_left₀ hl hx'.1 2
    have h201 := pow_le_pow_left₀ hl hx'.1 201
    have h200 := pow_le_pow_left₀ hx0 hx'.2 200
    have he0 : 0 ≤ E-G*x := by nlinarith [mul_le_mul_of_nonneg_left hx'.2 hG]
    have he1 : E-G*x ≤ E-G*l := by nlinarith [mul_le_mul_of_nonneg_left hx'.1 hG]
    have hp := mul_le_mul h200 he1 he0 (by positivity : 0 ≤ u^200)
    nlinarith [mul_le_mul_of_nonneg_left h2 hD,
      mul_le_mul_of_nonneg_left h201 hG]

theorem signedPoly_positive_cell (A B D E G l u : ℝ)
    (hl : 0 ≤ l) (hD : 0 ≤ D) (hG : 0 ≤ G) (hE : 0 ≤ E-G*u)
    (hd : -3*D*l^2+201*u^200*(E-G*l)-G*l^201 ≤ 0)
    (hH : 0 ≤ grouped B D E G u)
    (hv : 0 < l^396*grouped B D E G u-A)
    (x : ℝ) (hx : x ∈ Set.Icc l u) : 0 < signedPoly A B D E G x := by
  have hh := grouped_antitone B D E G l u hl hD hG hE hd hx
    (show u ∈ Set.Icc l u from ⟨hx.1.trans hx.2,le_rfl⟩) hx.2
  have hp := pow_le_pow_left₀ hl hx.1 396
  have hm := mul_le_mul hp hh hH (by positivity : 0 ≤ x^396)
  unfold signedPoly
  linarith

theorem signedPoly_derivative (A B D E G x : ℝ) :
    HasDerivAt (signedPoly A B D E G)
      (x^395*((396*B-399*D*x^3)+x^201*(597*E-598*G*x))) x := by
  unfold signedPoly
  convert ((((hasDerivAt_id x).pow 396).mul (grouped_derivative B D E G x)).sub
    (hasDerivAt_const x A)) using 1
  simp only [grouped,Pi.pow_apply,id_eq]
  ring

theorem signedPoly_negative_right (A B D E G a : ℝ) (ha : 0 ≤ a)
    (hD : 0 ≤ D) (hG : 0 ≤ G)
    (h1 : 0 ≤ 396*B-399*D*a^3) (h2 : 0 ≤ 597*E-598*G*a)
    (hv : signedPoly A B D E G a < 0)
    (x : ℝ) (hx : x ∈ Set.Icc 0 a) : signedPoly A B D E G x < 0 := by
  have mono : MonotoneOn (signedPoly A B D E G) (Set.Icc 0 a) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 a)
    · unfold signedPoly grouped; fun_prop
    · intro y _
      exact (signedPoly_derivative A B D E G y).hasDerivWithinAt
    · intro y hy
      have hy' : y ∈ Set.Icc 0 a := interior_subset hy
      have hy0 : 0 ≤ y := hy'.1
      have hp := pow_le_pow_left₀ hy'.1 hy'.2 3
      have hg1 : 0 ≤ 396*B-399*D*y^3 := by
        nlinarith [mul_le_mul_of_nonneg_left hp hD]
      have hg2 : 0 ≤ 597*E-598*G*y := by
        nlinarith [mul_le_mul_of_nonneg_left hy'.2 hG]
      positivity
  exact (mono hx ⟨ha,le_rfl⟩ hx.2).trans_lt hv

end AssayInformation

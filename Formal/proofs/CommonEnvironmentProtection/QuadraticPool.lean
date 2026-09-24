import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace CommonEnvironmentProtection.QuadraticPool
noncomputable section

def root (a b d : ℝ) : ℝ := (-b + Real.sqrt (b^2+4*a*d))/(2*a)

theorem root_pos (a b d : ℝ) (ha : 0 < a) (hd : 0 < d) : 0 < root a b d := by
  have hdisc : 0 ≤ b^2+4*a*d := by nlinarith [sq_nonneg b, mul_pos ha hd]
  have hs := Real.sq_sqrt hdisc
  have hn := Real.sqrt_nonneg (b^2+4*a*d)
  have hb : b < Real.sqrt (b^2+4*a*d) := by
    nlinarith [mul_pos ha hd]
  exact div_pos (by linarith) (by positivity)

theorem root_balance (a b d : ℝ) (ha : 0 < a) (hd : 0 < d) :
    a*(root a b d)^2+b*root a b d-d=0 := by
  have hdisc : 0 ≤ b^2+4*a*d := by nlinarith [sq_nonneg b, mul_pos ha hd]
  have hs := Real.sq_sqrt hdisc
  unfold root
  field_simp
  ring_nf at hs ⊢
  nlinarith

theorem factor_positive (a b d y z : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hy : 0 ≤ y) (hz : 0 < z) (hbal : a*z^2+b*z-d=0) :
    0 < a*(y+z)+b := by
  have hm : 0 ≤ a*y*z := mul_nonneg (mul_nonneg ha.le hy) hz.le
  nlinarith

theorem polynomial_le_iff (a b d y : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hy : 0 ≤ y) : a*y^2+b*y-d ≤ 0 ↔ y ≤ root a b d := by
  have hz := root_pos a b d ha hd
  have hb := root_balance a b d ha hd
  have hp := factor_positive a b d y (root a b d) ha hd hy hz hb
  have he : a*y^2+b*y-d = (y-root a b d)*(a*(y+root a b d)+b) := by
    nlinarith
  rw [he]
  constructor
  · intro h
    by_contra! hh
    have := mul_pos (sub_pos.mpr hh) hp
    linarith
  · intro h
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) hp.le

theorem positive_root_unique (a b d y : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hy : 0 < y) (hbal : a*y^2+b*y-d=0) : y=root a b d := by
  have hz := root_pos a b d ha hd
  have hb := root_balance a b d ha hd
  have hp := factor_positive a b d y (root a b d) ha hd hy.le hz hb
  have he : (y-root a b d)*(a*(y+root a b d)+b)=0 := by nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right (ne_of_gt hp))

def response (a b c d x : ℝ) : ℝ := root a (b+c/x) d

theorem response_strictMono (a b c d : ℝ) (ha : 0 < a) (hc : 0 < c) (hd : 0 < d) :
    StrictMonoOn (response a b c d) (Set.Ioi 0) := by
  intro x hx z hz hxz
  have hr : c/z < c/x := by
    rw [div_lt_div_iff₀ hz hx]
    nlinarith [mul_pos hc (sub_pos.mpr hxz)]
  have hy := root_pos a (b+c/x) d ha hd
  have hbal := root_balance a (b+c/x) d ha hd
  have hneg : a*(root a (b+c/x) d)^2+(b+c/z)*root a (b+c/x) d-d < 0 := by
    nlinarith [mul_pos (sub_pos.mpr hr) hy]
  have hle := (polynomial_le_iff a (b+c/z) d (root a (b+c/x) d) ha hd hy.le).mp hneg.le
  have hne : root a (b+c/x) d ≠ root a (b+c/z) d := by
    intro he
    rw [he, root_balance a (b+c/z) d ha hd] at hneg
    exact (lt_irrefl 0) hneg
  exact lt_of_le_of_ne hle hne

theorem response_continuous (a b c d L U : ℝ) (hL : 0 < L) :
    ContinuousOn (response a b c d) (Set.Icc L U) := by
  have hx : ∀ x ∈ Set.Icc L U, x ≠ 0 := by
    intro x hx
    linarith [hx.1]
  have hlin : ContinuousOn (fun x : ℝ => b+c/x) (Set.Icc L U) :=
    continuousOn_const.add (continuousOn_const.div continuousOn_id hx)
  exact (hlin.neg.add ((hlin.pow 2).add continuousOn_const).sqrt).div_const (2*a)

theorem response_threshold_iff (a b c d x y : ℝ)
    (ha : 0 < a) (hd : 0 < d) (hx : 0 < x) (hy : 0 ≤ y)
    (hmargin : 0 < d-a*y^2-b*y) :
    y ≤ response a b c d x ↔ c*y/(d-a*y^2-b*y) ≤ x := by
  rw [response, ← polynomial_le_iff a (b+c/x) d y ha hd hy,
    div_le_iff₀ hmargin]
  have he : a*y^2+(b+c/x)*y-d = (c*y)/x-(d-a*y^2-b*y) := by ring
  rw [he]
  constructor
  · intro h
    have hv : (c*y)/x ≤ d-a*y^2-b*y := by linarith
    have hv' := (div_le_iff₀ hx).mp hv
    nlinarith
  · intro h
    have hv : (c*y)/x ≤ d-a*y^2-b*y :=
      (div_le_iff₀ hx).mpr (by nlinarith)
    linarith

def rate (p u v y : ℝ) : ℝ := p*y/(u+v*y)

theorem rate_strictMono (p u v : ℝ) (hp : 0 < p) (hu : 0 < u) (hv : 0 ≤ v) :
    StrictMonoOn (rate p u v) (Set.Ici 0) := by
  intro y hy z hz hyz
  have hdy : 0 < u+v*y := by nlinarith [mul_nonneg hv hy]
  have hdz : 0 < u+v*z := by nlinarith [mul_nonneg hv hz]
  unfold rate
  rw [div_lt_div_iff₀ hdy hdz]
  nlinarith [mul_pos (mul_pos hp hu) (sub_pos.mpr hyz)]

theorem rate_service_iff (p u v q y : ℝ) (hu : 0 < u) (hv : 0 ≤ v)
    (hy : 0 ≤ y) (hcap : 0 < p-q*v) :
    q ≤ rate p u v y ↔ q*u/(p-q*v) ≤ y := by
  have hden : 0 < u+v*y := by nlinarith [mul_nonneg hv hy]
  unfold rate
  rw [le_div_iff₀ hden, div_le_iff₀ hcap]
  constructor <;> intro h <;> nlinarith

end
end CommonEnvironmentProtection.QuadraticPool

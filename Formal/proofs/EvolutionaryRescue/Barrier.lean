import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace EvolutionaryRescue

theorem barrier_identity (d b mu a r : ℝ) :
    d*a+b*((1-mu)*(1-a)^2+mu*r*(1-a)-(1-a)) =
      d*a-b*(1-a)*a-b*mu*(1-a)*(1-a-r) := by ring

/-- The actual source inequality for the time-dependent feedback barrier. -/
theorem finite_course_barrier (d dmax b mu a r lam alpha : ℝ)
    (ha : 0≤a) (ha' : a≤(1-r)/2) (hr0 : 0≤r)
    (hb : 0≤b) (hd : d≤dmax) (hl : 0≤lam) (hmu : lam≤b*mu)
    (halpha : dmax*alpha≤lam*(1-r)/4) :
    d*a-b*(1-a)*a-b*mu*(1-a)*(1-a-r) ≤ dmax*(a-alpha) := by
  have hq : 0≤1-a := by linarith
  have hqhalf : (1:ℝ)/2≤1-a := by linarith
  have hgap : (1-r)/2≤1-a-r := by linarith
  have hgap0 : 0≤1-a-r := by linarith
  have hprod : (1-r)/4≤(1-a)*(1-a-r) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hqhalf) hgap0]
  have hp0 : 0≤(1-a)*(1-a-r) := mul_nonneg hq hgap0
  have hrate := mul_le_mul_of_nonneg_right hmu hp0
  have hforce := mul_le_mul_of_nonneg_left hprod hl
  have hdeath := mul_le_mul_of_nonneg_right hd ha
  have hbirth : 0≤b*(1-a)*a := mul_nonneg (mul_nonneg hb hq) ha
  nlinarith

theorem barrier_constants :
    (421/1000:ℚ)*(1/2105)=(1/1000)*(1-1/5)/4 ∧
    (1/2105:ℚ)≤(1-1/5)/2 := by norm_num

end EvolutionaryRescue

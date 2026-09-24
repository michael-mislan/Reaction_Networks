import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace EvolutionaryRescue

theorem scalar_envelope (d dmax b mu mumin q r : ℝ)
    (hd : d≤dmax) (hb : 0≤b) (hm : mumin≤mu)
    (hq : 0≤q) (hqr : r≤q) (hq1 : q≤1) :
    d*(1-q)+b*((1-mu)*q^2+mu*r*q-q) ≤
      dmax*(1-q)+b*((1-mumin)*q^2+mumin*r*q-q) := by
  have hdeath := mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr hq1)
  have hmutation := mul_nonneg (mul_nonneg (mul_nonneg hb (sub_nonneg.mpr hm)) hq)
    (sub_nonneg.mpr hqr)
  nlinarith

theorem scalar_survival_polynomial (a : ℝ) :
    -((421/1000)*(1-(1-a))+(1/10)*
      ((1-1/100)*(1-a)^2+(1/100)*(1/5)*(1-a)-(1-a))) =
    1/1250-(807/2500)*a-(99/1000)*a^2 := by ring

theorem boundary_curvature_arithmetic :
    (6912:ℚ)*(120561/10^6-120545/10^6)=110592/10^6 ∧
    (20:ℚ)*9*((1/5)*6^2+2*6)=3456 := by norm_num

end EvolutionaryRescue

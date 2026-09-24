import proofs.FiniteCopy.ActivitySource

namespace FiniteCopy
open CoreCouplingCAC Set

theorem activity_H_formula (x : Point) (q : ℝ) :
    (∑ r, densityRates (1/100000) q x r*markH r) =
      16*x 2-2*x 3+2*(x 2)^2-2*q*x 2 := by
  norm_num [densityRates,markH,Fin.sum_univ_succ]
  ring

theorem markH_square (r : Fin 13) : (markH r)^2 ≤ 4 := by
  fin_cases r <;> norm_num [markH]

theorem H_current_near_stationary (z H x h q : ℝ)
    (hz0 : 0 ≤ z) (hz3 : z ≤ 3) (hH : 8 ≤ H)
    (hstat : 16*z+2*z^2-(2+1/10000)*H = 0)
    (hclose : |x-z| ≤ 1/1000000) (hcloseH : |h-H| ≤ 1/1000000)
    (hx0 : 0 ≤ x) (hq : q ≤ 1/1000000) :
    1/2000 ≤ 16*x-2*h+2*x^2-2*q*x := by
  have hz := abs_le.mp hclose
  have hh := abs_le.mp hcloseH
  have hx4 : x ≤ 4 := by linarith [hz.2]
  have hp := mul_nonneg (by linarith [hz.1] : 0 ≤ x-z+1/1000000) (add_nonneg hx0 hz0)
  have hs : z^2-7/1000000 ≤ x^2 := by nlinarith only [hp,hx4,hz3]
  have hqp := mul_nonneg (sub_nonneg.mpr hq) hx0
  have hqx : q*x ≤ 4/1000000 := by nlinarith only [hqp,hx4]
  nlinarith only [hstat,hH,hz.1,hh.2,hs,hqx]

theorem low_activity_H (z : ℝ)
    (hz : z ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z)) (x : Point) (q : ℝ)
    (hq : q ≤ 1/1000000) (hx0 : 0 ≤ x 2)
    (hy : ∀ i, |x i-pointOfState (lift sourceRates z) i| ≤ 1/1000000) :
    1/2000 ≤ ∑ r, densityRates (1/100000) q x r*markH r := by
  rw [activity_H_formula]
  have hb := low_source_box z hz
  have hstat := hs.2.2.2
  change 16*z+2*z^2-(2+1/10000)*reducedH sourceRates z = 0 at hstat
  exact H_current_near_stationary z (reducedH sourceRates z) (x 2) (x 3) q
    (by linarith [hz.1]) (by linarith [hz.2]) hb.2.2.1 hstat (hy 2) (hy 3) hx0 hq

theorem high_activity_H (z : ℝ)
    (hz : z ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z)) (x : Point) (q : ℝ)
    (hq : q ≤ 1/1000000) (hx0 : 0 ≤ x 2)
    (hy : ∀ i, |x i-pointOfState (lift sourceRates z) i| ≤ 1/1000000) :
    1/2000 ≤ ∑ r, densityRates (1/100000) q x r*markH r := by
  rw [activity_H_formula]
  have hb := high_source_box z hz
  have hstat := hs.2.2.2
  change 16*z+2*z^2-(2+1/10000)*reducedH sourceRates z = 0 at hstat
  exact H_current_near_stationary z (reducedH sourceRates z) (x 2) (x 3) q
    (by linarith [hz.1]) (by linarith [hz.2]) (by linarith [hb.2.2.1]) hstat (hy 2) (hy 3) hx0 hq

end FiniteCopy

import Mathlib

namespace PhenotypeIdentification

theorem offspring_difference (k00 k01 k10 k11 e x y : ℝ) :
    ((k00+e)*x*x+(k01-e)*x*y+(k10-e)*y*x+(k11+e)*y*y) -
    (k00*x*x+k01*x*y+k10*y*x+k11*y*y) = e*(x-y)^2 := by ring

theorem offspring_difference_nonnegative (e x y : ℝ) (he : 0 ≤ e) :
    0 ≤ e*(x-y)^2 := mul_nonneg he (sq_nonneg _)

theorem marginal_preservation (k00 k01 k10 k11 e : ℝ) :
    (k00+e)+(k01-e)=k00+k01 ∧ (k10-e)+(k11+e)=k10+k11 := by
  constructor <;> ring

end PhenotypeIdentification

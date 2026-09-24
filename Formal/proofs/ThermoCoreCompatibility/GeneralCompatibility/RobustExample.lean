import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ThermoCoreCompatibility.GeneralCompatibility

def sourceResidual (a b x y : ℚ) : ℚ := 2 * b * (y-x^2) - a * (x-y)
def targetResidual (a b x y : ℚ) : ℚ := a * (x-y) - b * (y-x^2)

theorem residual_sum (a b x y : ℚ) :
    sourceResidual a b x y + targetResidual a b x y = b * (y-x^2) := by
  unfold sourceResidual targetResidual
  ring

theorem triangle_nominal :
    sourceResidual 2 1 (1/10) (13/200) = 1/25 ∧
    targetResidual 2 1 (1/10) (13/200) = 3/200 ∧
    sourceResidual 2 1 (13/200) (43/1000) = 671/20000 ∧
    targetResidual 2 1 (13/200) (43/1000) = 209/40000 ∧
    sourceResidual 1 1 (1/10) (43/1000) = 9/1000 ∧
    targetResidual 1 1 (1/10) (43/1000) = 3/125 := by
  norm_num [sourceResidual, targetResidual]

theorem triangle_box_corners_positive :
    0 < sourceResidual (2*(1+1/20)) (1-1/20) (1/10+1/10000) (13/200-1/10000) ∧
    0 < targetResidual (2*(1-1/20)) (1+1/20) (1/10-1/10000) (13/200+1/10000) ∧
    0 < sourceResidual (2*(1+1/20)) (1-1/20) (13/200+1/10000) (43/1000-1/10000) ∧
    0 < targetResidual (2*(1-1/20)) (1+1/20) (13/200-1/10000) (43/1000+1/10000) ∧
    0 < sourceResidual (1+1/20) (1-1/20) (1/10+1/10000) (43/1000-1/10000) ∧
    0 < targetResidual (1-1/20) (1+1/20) (1/10-1/10000) (43/1000+1/10000) := by
  norm_num [sourceResidual, targetResidual]

end ThermoCoreCompatibility.GeneralCompatibility

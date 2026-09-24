import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

namespace EvolutionaryRescue

/-- Literal one-mutant-daughter offspring expansion at molecular terminal one. -/
theorem offspring_expansion (eps k y lh dhh : ℝ) :
    (1-eps*k)*(1-2*eps*lh+eps^2*dhh)+eps*k*y*(1-eps*lh) =
    1+eps*(-2*lh-k*(1-y))+eps^2*(dhh+k*(2-y)*lh)-eps^3*k*dhh := by ring

/-- The equal-marginal mutation terms cancel in the dependence forcing. -/
theorem covariance_forcing (b mu y marginal joint independent : ℝ) :
    b*((1-mu)*independent+mu*y*marginal)-
      b*((1-mu)*joint+mu*y*marginal)=b*(1-mu)*(independent-joint) := by ring

/-- Quadratic polarization in the independent marginal, used by the exact response. -/
theorem independent_response (u v : ℝ) : u^2-v^2=(u+v)*(u-v) := by ring

end EvolutionaryRescue

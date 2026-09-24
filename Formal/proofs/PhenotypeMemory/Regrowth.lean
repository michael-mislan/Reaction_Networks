import Mathlib

namespace PhenotypeMemory

/-- Exact source-stopped linear-system outputs; their probability identification
and the 27-state residual replay are conventional, explicitly outside this module. -/
def lowErasureHit : ℚ :=
  116150936073671693412424967282960570423142300 /
  136977305603200010736009305215557430759831961
def lowErasureTime : ℚ :=
  16829971848592738145544998742629113702018502500 /
  958841139222400075152065136508902015318823727
def highErasureHit : ℚ :=
  569574178531798404102472899849703283441991381 /
  2017088486530386011582065903745112214002690841

theorem exact_regrowth_arithmetic :
    672/1000 < lowErasureHit-lowErasureTime/100 ∧
    highErasureHit < 283/1000 ∧
    389/1000 < lowErasureHit-lowErasureTime/100-highErasureHit := by
  norm_num [lowErasureHit, lowErasureTime, highErasureHit]

theorem short_horizon_comparison_arithmetic :
    (1:ℚ)*(1/10)*(3-1)*(1/10) = 1/50 ∧
    97/100-1/50 > (9/10:ℚ) := by norm_num

end PhenotypeMemory

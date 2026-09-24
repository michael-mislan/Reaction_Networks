import proofs.OptimalAffinity.Source

namespace OptimalAffinity

def YSteady (N : Network) (x y : ℝ) : Prop :=
  (netY N 0 : ℝ) * netFlux N 0 x y +
    (netY N 1 : ℝ) * netFlux N 1 x y = 0

def productionCurrent (N : Network) (x y : ℝ) : ℝ := netFlux N 0 x y

theorem oa2x2_oneWayFluxes (x y : ℝ) :
    forwardFlux oa2x2 0 x y = 3 * x ∧
    reverseFlux oa2x2 0 x y = 2 * y ∧
    forwardFlux oa2x2 1 x y = 7 * y ^ 2 ∧
    reverseFlux oa2x2 1 x y = 6 * x ^ 2 * y := by
  norm_num [forwardFlux, reverseFlux, oa2x2]

theorem oa2x2_netFluxes (x y : ℝ) :
    netFlux oa2x2 0 x y = 3 * x - 2 * y ∧
    netFlux oa2x2 1 x y = 7 * y ^ 2 - 6 * x ^ 2 * y := by
  norm_num [netFlux, forwardFlux, reverseFlux, oa2x2]

theorem oa2x2_ySteady_iff (x y : ℝ) :
    YSteady oa2x2 x y ↔ 3 * x - 2 * y = 7 * y ^ 2 - 6 * x ^ 2 * y := by
  simp only [YSteady]
  rw [oa2x2_netFluxes x y |>.1, oa2x2_netFluxes x y |>.2]
  norm_num [netY, oa2x2]
  constructor <;> intro h <;> linarith

theorem oa2x2_tightCoupling {x y : ℝ} (hsteady : YSteady oa2x2 x y) :
    netFlux oa2x2 0 x y = netFlux oa2x2 1 x y := by
  rw [oa2x2_netFluxes x y |>.1, oa2x2_netFluxes x y |>.2]
  exact (oa2x2_ySteady_iff x y).mp hsteady

theorem oa2x2_current_formula (x y : ℝ) :
    productionCurrent oa2x2 x y = 3 * x - 2 * y := by
  exact oa2x2_netFluxes x y |>.1

theorem oa2x2_one_one_steady : YSteady oa2x2 1 1 := by
  rw [oa2x2_ySteady_iff]
  norm_num

theorem oa2x2_one_one_current : productionCurrent oa2x2 1 1 = 1 := by
  rw [oa2x2_current_formula]
  norm_num

end OptimalAffinity

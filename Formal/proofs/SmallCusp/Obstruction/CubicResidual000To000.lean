import proofs.SmallCusp.Obstruction.CubicDegeneracy
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def cubicResidualNetwork0 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .xx), (.x, .zero), (.y, .x), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork0_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork0.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [cubicResidualNetwork0, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
      at heq0 heq1 hdet hrg hlg hfold hc0 hc1 ⊢
  case false.false =>
    linear_combination
      ((2 : ℝ) * (v 4 * h 1)) * hdet +
      (-(v 4)) * hfold +
      (-(v 2 * v 4)) * hc0
  case false.true =>
    ring
  case true.false =>
    linear_combination
      ((-2 : ℝ) * (v 4 * h 1)) * hdet +
      (v 4) * hfold +
      (-(v 2 * v 4)) * hc1
  case true.true =>
    ring

theorem cubicResidualNetwork0_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork0.toNetwork := by
  intro v hv heq
  by_contra hJ
  simp only [not_or, not_not] at hJ
  have heq0 := heq 0
  have heq1 := heq 1
  have hv0 := hv 0
  have hv1 := hv 1
  have hv2 := hv 2
  have hv3 := hv 3
  have hv4 := hv 4
  simp [cubicResidualNetwork0, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork0_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork0.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork0_jacobianNonzero
    cubicResidualNetwork0_fourCharts

end SmallCusp

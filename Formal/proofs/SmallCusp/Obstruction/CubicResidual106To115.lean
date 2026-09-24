import proofs.SmallCusp.Obstruction.CubicDegeneracy
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

def cubicResidualNetwork106 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xy), (.xx, .zero), (.xy, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork106_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork106.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork106, CodedBimolNetwork.toNetwork,
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
      at heq0 heq1 hdet hfold hc0 hc1
  case false.false =>
    have g1 : v 4 + -(v 3) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork106, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (-4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (4 : ℝ) * (v 2 * (v 3) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + (16 : ℝ) * ((v 2) ^ 2 * v 4 * h 0) + (-16 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + (4 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (-4 : ℝ) * (v 1 * v 2 * v 3 * h 1) + (4 : ℝ) * (v 1 * v 2 * v 3 * h 0) + -(v 0 * (v 4) ^ 2 * h 1) + v 0 * (v 4) ^ 2 * h 0 + v 0 * (v 3) ^ 2 * h 1 + -(v 0 * (v 3) ^ 2 * h 0) + (8 : ℝ) * (v 0 * v 2 * v 4 * h 0) + (-8 : ℝ) * (v 0 * v 2 * v 3 * h 0) + v 0 * v 1 * v 4 * h 1 + -(v 0 * v 1 * v 3 * h 1) + (v 0) ^ 2 * v 4 * h 0 + -((v 0) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 2 * v 4 * h 1) + (8 : ℝ) * (v 2 * v 4 * h 0) + (-4 : ℝ) * (v 2 * v 3 * h 1) + (8 : ℝ) * (v 2 * v 3 * h 0) + (16 : ℝ) * ((v 2) ^ 2 * h 0) + (4 : ℝ) * (v 1 * v 2 * h 1) + (-4 : ℝ) * (v 1 * v 2 * h 0) + -(v 0 * v 4 * h 1) + v 0 * v 4 * h 0 + -(v 0 * v 3 * h 1) + v 0 * v 3 * h 0 + (8 : ℝ) * (v 0 * v 2 * h 0) + v 0 * v 1 * h 1 + (v 0) ^ 2 * h 0) * g1
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork106, CodedBimolNetwork.toNetwork,
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
      at hg0 hg1
    have g1 : v 4 + -(v 3) = 0 := by
      nlinarith [hg1]
    have g3 : v 4 + -(v 3) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork106, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + -(v 1 * (v 3) ^ 2 * h 1) + v 1 * (v 3) ^ 2 * h 0 + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (8 : ℝ) * (v 1 * v 2 * v 3 * h 0) + -((v 1) ^ 2 * v 4 * h 1) + (v 1) ^ 2 * v 3 * h 1 + -(v 0 * v 1 * v 4 * h 0) + v 0 * v 1 * v 3 * h 0 = 0 := by
      linear_combination
        ((4 : ℝ) * (v 2 * v 4 * h 0) + (4 : ℝ) * (v 2 * v 3 * h 0) + -(v 1 * v 3 * h 0) + (-8 : ℝ) * (v 1 * v 2 * h 0)) * g1 +
      (v 1 * v 4 * h 1 + -(v 1 * v 4 * h 0) + v 1 * v 3 * h 1 + -((v 1) ^ 2 * h 1) + -(v 0 * v 1 * h 0)) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork106, CodedBimolNetwork.toNetwork,
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
      at hg0 hg1
    have g3 : v 4 + -(v 3) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork106, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-8 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (16 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (4 : ℝ) * (v 2 * (v 3) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + v 0 * (v 4) ^ 2 * h 1 + -(v 0 * (v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (2 : ℝ) * (v 0 * v 3 * v 4 * h 0) + v 0 * (v 3) ^ 2 * h 1 + -(v 0 * (v 3) ^ 2 * h 0) = 0 := by
      linear_combination
        ((4 : ℝ) * (v 2 * v 4 * h 1) + (-8 : ℝ) * (v 2 * v 4 * h 0) + (-4 : ℝ) * (v 2 * v 3 * h 1) + (8 : ℝ) * (v 2 * v 3 * h 0) + v 0 * v 4 * h 1 + -(v 0 * v 4 * h 0) + -(v 0 * v 3 * h 1) + v 0 * v 3 * h 0) * g3
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork106, CodedBimolNetwork.toNetwork,
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
      at hg0 hg1 hg2
    have g2 : v 4 + -(v 3) = 0 := by
      nlinarith [hg2]
    have g4 : v 4 + -(v 3) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork106, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (-4 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (-4 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + (2 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (-2 : ℝ) * (v 1 * v 3 * v 4 * h 0) + -(v 1 * (v 3) ^ 2 * h 1) + v 1 * (v 3) ^ 2 * h 0 = 0 := by
      linear_combination
        (-(v 1 * v 4 * h 1) + v 1 * v 3 * h 1 + -(v 1 * v 3 * h 0)) * g2 +
      ((-4 : ℝ) * (v 2 * v 4 * h 0) + (4 : ℝ) * (v 2 * v 3 * h 0) + v 1 * v 4 * h 0) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork106_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork106.toNetwork := by
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
  simp [cubicResidualNetwork106, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork106_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork106.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork106_jacobianNonzero
    cubicResidualNetwork106_fourCharts

def cubicResidualNetwork107 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xy), (.xx, .zero), (.xy, .x), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork107_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork107.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork107, CodedBimolNetwork.toNetwork,
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
      at heq0 heq1 hdet hfold hc0 hc1
  case false.false =>
    have g1 : v 4 + -(v 3) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork107, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (-4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (4 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (-8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (16 : ℝ) * ((v 2) ^ 2 * v 4 * h 0) + (-16 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + (4 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (-4 : ℝ) * (v 1 * v 2 * v 3 * h 1) + (4 : ℝ) * (v 1 * v 2 * v 3 * h 0) + -(v 0 * (v 4) ^ 2 * h 1) + v 0 * (v 4) ^ 2 * h 0 + v 0 * v 3 * v 4 * h 1 + -(v 0 * v 3 * v 4 * h 0) + (8 : ℝ) * (v 0 * v 2 * v 4 * h 0) + (-8 : ℝ) * (v 0 * v 2 * v 3 * h 0) + v 0 * v 1 * v 4 * h 1 + -(v 0 * v 1 * v 3 * h 1) + (v 0) ^ 2 * v 4 * h 0 + -((v 0) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 2 * v 4 * h 1) + (8 : ℝ) * (v 2 * v 4 * h 0) + (16 : ℝ) * ((v 2) ^ 2 * h 0) + (4 : ℝ) * (v 1 * v 2 * h 1) + (-4 : ℝ) * (v 1 * v 2 * h 0) + -(v 0 * v 4 * h 1) + v 0 * v 4 * h 0 + (8 : ℝ) * (v 0 * v 2 * h 0) + v 0 * v 1 * h 1 + (v 0) ^ 2 * h 0) * g1
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork107, CodedBimolNetwork.toNetwork,
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
      at hg0 hg1
    have g1 : v 4 + -(v 3) = 0 := by
      nlinarith [hg1]
    have g3 : v 4 + -(v 3) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork107, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 2 * v 3 * v 4 * h 0) + v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + -(v 1 * v 3 * v 4 * h 1) + v 1 * v 3 * v 4 * h 0 + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (8 : ℝ) * (v 1 * v 2 * v 3 * h 0) + -((v 1) ^ 2 * v 4 * h 1) + (v 1) ^ 2 * v 3 * h 1 + -(v 0 * v 1 * v 4 * h 0) + v 0 * v 1 * v 3 * h 0 = 0 := by
      linear_combination
        ((-8 : ℝ) * (v 1 * v 2 * h 0) + -((v 1) ^ 2 * h 1) + -(v 0 * v 1 * h 0)) * g1 +
      ((4 : ℝ) * (v 2 * v 4 * h 0) + v 1 * v 4 * h 1 + -(v 1 * v 4 * h 0)) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork107, CodedBimolNetwork.toNetwork,
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
      at hg0 hg1
    have g1 : -(v 4) + v 1 = 0 := by
      nlinarith [hg1]
    have g3 : v 4 + -(v 3) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork107, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-8 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (16 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (4 : ℝ) * (v 2 * (v 3) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + v 0 * (v 4) ^ 2 * h 1 + -(v 0 * (v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (2 : ℝ) * (v 0 * v 3 * v 4 * h 0) + v 0 * (v 3) ^ 2 * h 1 + -(v 0 * (v 3) ^ 2 * h 0) = 0 := by
      linear_combination
        (-(v 0 * v 4 * h 1) + v 0 * v 3 * h 1) * g1 +
      ((4 : ℝ) * (v 2 * v 4 * h 1) + (-8 : ℝ) * (v 2 * v 4 * h 0) + (-4 : ℝ) * (v 2 * v 3 * h 1) + (8 : ℝ) * (v 2 * v 3 * h 0) + -(v 0 * v 4 * h 0) + -(v 0 * v 3 * h 1) + v 0 * v 3 * h 0 + v 0 * v 1 * h 1) * g3
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork107, CodedBimolNetwork.toNetwork,
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
      at hg0 hg1 hg2
    have g1 : -(v 4) + v 1 = 0 := by
      nlinarith [hg1]
    have g2 : v 4 + -(v 3) = 0 := by
      nlinarith [hg2]
    have g4 : v 4 + -(v 3) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork107, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (-4 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (-4 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + (2 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (-2 : ℝ) * (v 1 * v 3 * v 4 * h 0) + -(v 1 * (v 3) ^ 2 * h 1) + v 1 * (v 3) ^ 2 * h 0 = 0 := by
      linear_combination
        ((v 4) ^ 2 * h 0 + v 3 * v 4 * h 1 + -((v 3) ^ 2 * h 1) + -((v 3) ^ 2 * h 0) + v 1 * v 4 * h 1 + -(v 1 * v 3 * h 1)) * g1 +
      ((v 4) ^ 2 * h 0 + (-2 : ℝ) * (v 1 * v 3 * h 0) + -((v 1) ^ 2 * h 1)) * g2 +
      (v 3 * v 4 * h 1 + v 3 * v 4 * h 0 + (-4 : ℝ) * (v 2 * v 4 * h 0) + (4 : ℝ) * (v 2 * v 3 * h 0)) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork107_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork107.toNetwork := by
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
  simp [cubicResidualNetwork107, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork107_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork107.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork107_jacobianNonzero
    cubicResidualNetwork107_fourCharts

def cubicResidualNetwork108 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xy), (.xx, .zero), (.xy, .xx), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork108_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork108.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork108, CodedBimolNetwork.toNetwork,
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
      at heq0 heq1 hdet hfold hc0 hc1
  case false.false =>
    have g1 : v 4 + -(v 3) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork108, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (-4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (8 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (-16 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (-4 : ℝ) * (v 2 * (v 3) ^ 2 * h 1) + (8 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + (16 : ℝ) * ((v 2) ^ 2 * v 4 * h 0) + (-16 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + (4 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (-4 : ℝ) * (v 1 * v 2 * v 3 * h 1) + (4 : ℝ) * (v 1 * v 2 * v 3 * h 0) + -(v 0 * (v 4) ^ 2 * h 1) + v 0 * (v 4) ^ 2 * h 0 + (2 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (-2 : ℝ) * (v 0 * v 3 * v 4 * h 0) + -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 + (8 : ℝ) * (v 0 * v 2 * v 4 * h 0) + (-8 : ℝ) * (v 0 * v 2 * v 3 * h 0) + v 0 * v 1 * v 4 * h 1 + -(v 0 * v 1 * v 3 * h 1) + (v 0) ^ 2 * v 4 * h 0 + -((v 0) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 2 * v 4 * h 1) + (8 : ℝ) * (v 2 * v 4 * h 0) + (4 : ℝ) * (v 2 * v 3 * h 1) + (-8 : ℝ) * (v 2 * v 3 * h 0) + (16 : ℝ) * ((v 2) ^ 2 * h 0) + (4 : ℝ) * (v 1 * v 2 * h 1) + (-4 : ℝ) * (v 1 * v 2 * h 0) + -(v 0 * v 4 * h 1) + v 0 * v 4 * h 0 + v 0 * v 3 * h 1 + -(v 0 * v 3 * h 0) + (8 : ℝ) * (v 0 * v 2 * h 0) + v 0 * v 1 * h 1 + (v 0) ^ 2 * h 0) * g1
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork108, CodedBimolNetwork.toNetwork,
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
      at hg0 hg1
    have g1 : v 4 + -(v 3) = 0 := by
      nlinarith [hg1]
    have g3 : v 4 + -(v 3) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork108, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (4 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 3 * v 4 * h 0) + v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (8 : ℝ) * (v 1 * v 2 * v 3 * h 0) + -((v 1) ^ 2 * v 4 * h 1) + (v 1) ^ 2 * v 3 * h 1 + -(v 0 * v 1 * v 4 * h 0) + v 0 * v 1 * v 3 * h 0 = 0 := by
      linear_combination
        ((4 : ℝ) * (v 2 * v 4 * h 0) + v 1 * v 4 * h 1 + (-8 : ℝ) * (v 1 * v 2 * h 0) + -((v 1) ^ 2 * h 1) + -(v 0 * v 1 * h 0)) * g1 +
      ((-4 : ℝ) * (v 2 * v 3 * h 0) + -(v 1 * v 4 * h 0) + -(v 1 * v 3 * h 1) + v 1 * v 3 * h 0) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork108, CodedBimolNetwork.toNetwork,
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
      at hg0 hg1
    have g3 : v 4 + -(v 3) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork108, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-8 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (16 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (4 : ℝ) * (v 2 * (v 3) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + v 0 * (v 4) ^ 2 * h 1 + -(v 0 * (v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (2 : ℝ) * (v 0 * v 3 * v 4 * h 0) + v 0 * (v 3) ^ 2 * h 1 + -(v 0 * (v 3) ^ 2 * h 0) = 0 := by
      linear_combination
        ((4 : ℝ) * (v 2 * v 4 * h 1) + (-8 : ℝ) * (v 2 * v 4 * h 0) + (-4 : ℝ) * (v 2 * v 3 * h 1) + (8 : ℝ) * (v 2 * v 3 * h 0) + v 0 * v 4 * h 1 + -(v 0 * v 4 * h 0) + -(v 0 * v 3 * h 1) + v 0 * v 3 * h 0) * g3
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork108, CodedBimolNetwork.toNetwork,
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
      at hg0 hg1 hg2
    have g2 : v 4 + -(v 3) = 0 := by
      nlinarith [hg2]
    have g4 : v 4 + -(v 3) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork108, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (-4 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (-4 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + (2 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (-2 : ℝ) * (v 1 * v 3 * v 4 * h 0) + -(v 1 * (v 3) ^ 2 * h 1) + v 1 * (v 3) ^ 2 * h 0 = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 2 * v 4 * h 0) + (4 : ℝ) * (v 2 * v 3 * h 0) + -(v 1 * v 4 * h 1) + v 1 * v 4 * h 0 + v 1 * v 3 * h 1) * g2 +
      (-(v 1 * v 3 * h 0)) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork108_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork108.toNetwork := by
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
  simp [cubicResidualNetwork108, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork108_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork108.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork108_jacobianNonzero
    cubicResidualNetwork108_fourCharts

def cubicResidualNetwork109 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xy), (.xx, .xy), (.xx, .yy), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork109_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork109.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork109, CodedBimolNetwork.toNetwork,
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
      at heq0 heq1 hdet hfold hc0 hc1
  case false.false =>
    have g0 : v 4 + (-2 : ℝ) * (v 3) + -(v 2) + v 1 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g1 : -(v 4) + (2 : ℝ) * (v 3) + v 2 = 0 := by
      nlinarith [heq1]
    have g2 : v 1 * v 4 + (-4 : ℝ) * (v 1 * v 3) + (-2 : ℝ) * (v 1 * v 2) + v 0 * v 4 = 0 := by
      nlinarith [hdet]
    have g3 : (2 : ℝ) * (v 0 * (v 4) ^ 3) + (-4 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (-2 : ℝ) * (v 0 * v 2 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * v 1 * (v 4) ^ 2) + (4 : ℝ) * (v 0 * (v 1) ^ 2 * v 3) + (2 : ℝ) * (v 0 * (v 1) ^ 2 * v 2) + (-2 : ℝ) * ((v 0) ^ 2 * (v 4) ^ 2) + (-2 : ℝ) * ((v 0) ^ 2 * v 1 * v 4) = 0 := by
      nlinarith [hfold]
    have g4 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + (-4 : ℝ) * (v 3 * h 0) + (4 : ℝ) * (v 3 * (v 4) ^ 2) + (-2 : ℝ) * (v 2 * h 0) + (2 : ℝ) * (v 2 * (v 4) ^ 2) + v 1 * h 1 + (-2 : ℝ) * (v 1 * (v 4) ^ 2) + (-4 : ℝ) * ((v 1) ^ 2 * v 3) + (-2 : ℝ) * ((v 1) ^ 2 * v 2) + -(v 0 * h 0) + (2 : ℝ) * (v 0 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * v 1 * v 4) = 0 := by
      nlinarith [hc0]
    have g5 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (4 : ℝ) * (v 3 * h 0) + (-4 : ℝ) * (v 3 * (v 4) ^ 2) + (2 : ℝ) * (v 2 * h 0) + (-2 : ℝ) * (v 2 * (v 4) ^ 2) + (2 : ℝ) * (v 1 * (v 4) ^ 2) + (4 : ℝ) * ((v 1) ^ 2 * v 3) + (2 : ℝ) * ((v 1) ^ 2 * v 2) + (-2 : ℝ) * (v 0 * (v 4) ^ 2) + (-2 : ℝ) * (v 0 * v 1 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork109, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -(v 0 * (v 4) ^ 2 * h 1) + v 0 * (v 4) ^ 2 * h 0 + -(v 0 * v 1 * v 4 * h 1) + (4 : ℝ) * (v 0 * v 1 * v 3 * h 0) + (2 : ℝ) * (v 0 * v 1 * v 2 * h 0) + -((v 0) ^ 2 * v 4 * h 0) = 0 := by
      linear_combination
        ((2 : ℝ) * (v 3 * v 4 * h 1) + v 0 * v 4 * h 0) * g0 +
      ((2 : ℝ) * (v 3 * v 4 * h 1) + v 1 * v 4 * h 1 + v 1 * v 4 * h 0 + (-4 : ℝ) * (v 1 * v 3 * h 0) + (-2 : ℝ) * (v 1 * v 2 * h 1) + (-2 : ℝ) * (v 1 * v 2 * h 0) + -((v 1) ^ 2 * h 1) + v 0 * v 4 * h 1 + v 0 * v 1 * h 0) * g1 +
      ((2 : ℝ) * (v 3 * h 0) + -(v 2 * h 1) + v 2 * h 0 + -(v 1 * h 1) + (2 : ℝ) * ((v 4) ^ 3) + (-4 : ℝ) * (v 3 * (v 4) ^ 2) + (-2 : ℝ) * (v 2 * (v 4) ^ 2) + (2 : ℝ) * (v 1 * (v 4) ^ 2) + (4 : ℝ) * ((v 1) ^ 2 * v 3) + (2 : ℝ) * ((v 1) ^ 2 * v 2) + (-2 : ℝ) * (v 0 * (v 4) ^ 2) + (-2 : ℝ) * (v 0 * v 1 * v 4)) * g2 +
      (-(v 4)) * g3 +
      ((-2 : ℝ) * (v 1 * v 3) + -(v 1 * v 2)) * g4 +
      (-(v 1 * v 4) + (2 : ℝ) * (v 1 * v 3) + v 1 * v 2) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork109, CodedBimolNetwork.toNetwork,
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
      at hg0 hg1
    have g1 : -(v 4) + (4 : ℝ) * (v 3) + (2 : ℝ) * (v 2) = 0 := by
      nlinarith [hg1]
    have g3 : -(v 4) + (2 : ℝ) * (v 3) + v 2 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork109, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + (v 1) ^ 2 * v 4 * h 1 + (-4 : ℝ) * ((v 1) ^ 2 * v 3 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * v 2 * h 0) + v 0 * v 1 * v 4 * h 0 = 0 := by
      linear_combination
        (v 1 * v 4 * h 1 + -(v 1 * v 4 * h 0) + (v 1) ^ 2 * h 1 + (-2 : ℝ) * ((v 1) ^ 2 * h 0) + v 0 * v 1 * h 0) * g1 +
      ((-2 : ℝ) * (v 1 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 4 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * h 1) + (2 : ℝ) * ((v 1) ^ 2 * h 0) + (-2 : ℝ) * (v 0 * v 1 * h 0)) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork109, CodedBimolNetwork.toNetwork,
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
      at hg0 hg1
    have g1 : v 4 + v 1 = 0 := by
      nlinarith [hg1]
    have g3 : -(v 4) + (2 : ℝ) * (v 3) + v 2 = 0 := by
      nlinarith [heq1]
    have g5 : (2 : ℝ) * (v 0 * (v 4) ^ 3) + (-4 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (-2 : ℝ) * (v 0 * v 2 * (v 4) ^ 2) = 0 := by
      nlinarith [hfold]
    have g7 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (4 : ℝ) * (v 3 * h 0) + (-4 : ℝ) * (v 3 * (v 4) ^ 2) + (2 : ℝ) * (v 2 * h 0) + (-2 : ℝ) * (v 2 * (v 4) ^ 2) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork109, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 0 * (v 4) ^ 2 * h 1 + -(v 0 * (v 4) ^ 2 * h 0) = 0 := by
      linear_combination
        (v 0 * v 4 * h 1 + -(v 0 * v 4 * h 0)) * g1 +
      ((-2 : ℝ) * (v 0 * v 1 * h 0)) * g3 +
      (-(v 1)) * g5 +
      (v 0 * v 1) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork109, CodedBimolNetwork.toNetwork,
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
      at hg0 hg1 hg2
    have g1 : v 4 + v 1 = 0 := by
      nlinarith [hg1]
    have g2 : -(v 4) + (4 : ℝ) * (v 3) + (2 : ℝ) * (v 2) = 0 := by
      nlinarith [hg2]
    have g4 : -(v 4) + (2 : ℝ) * (v 3) + v 2 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork109, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 = 0 := by
      linear_combination
        ((v 4) ^ 2 * h 0 + -(v 1 * v 4 * h 1)) * g1 +
      (-((v 4) ^ 2 * h 0) + (v 1) ^ 2 * h 1) * g2 +
      ((2 : ℝ) * ((v 4) ^ 2 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * h 1)) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork109_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork109.toNetwork := by
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
  simp [cubicResidualNetwork109, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork109_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork109.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork109_jacobianNonzero
    cubicResidualNetwork109_fourCharts

def cubicResidualNetwork110 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xy), (.xx, .xy), (.xx, .yy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork110_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork110.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork110, CodedBimolNetwork.toNetwork,
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
      at heq0 heq1 hdet hfold hc0 hc1
  case false.false =>
    have g1 : (-2 : ℝ) * (v 4) + (2 : ℝ) * (v 3) + v 2 = 0 := by
      nlinarith [heq1]
    have g2 : (-4 : ℝ) * (v 1 * v 3) + (-2 : ℝ) * (v 1 * v 2) + (4 : ℝ) * (v 0 * v 4) = 0 := by
      nlinarith [hdet]
    have g3 : (64 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (-64 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (32 : ℝ) * (v 0 * v 2 * (v 4) ^ 2) + (-64 : ℝ) * (v 0 * v 2 * v 3 * v 4) + (-16 : ℝ) * (v 0 * (v 2) ^ 2 * v 4) + (32 : ℝ) * (v 0 * v 1 * v 3 * v 4) + (16 : ℝ) * (v 0 * v 1 * v 2 * v 4) + (4 : ℝ) * (v 0 * (v 1) ^ 2 * v 3) + (2 : ℝ) * (v 0 * (v 1) ^ 2 * v 2) + (-32 : ℝ) * ((v 0) ^ 2 * v 3 * v 4) + (-16 : ℝ) * ((v 0) ^ 2 * v 2 * v 4) + (-4 : ℝ) * ((v 0) ^ 3 * v 4) = 0 := by
      nlinarith [hfold]
    have g5 : (-4 : ℝ) * (v 4 * h 1) + (4 : ℝ) * (v 3 * h 0) + (64 : ℝ) * (v 3 * (v 4) ^ 2) + (-64 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * (v 2 * h 0) + (32 : ℝ) * (v 2 * (v 4) ^ 2) + (-64 : ℝ) * (v 2 * v 3 * v 4) + (-16 : ℝ) * ((v 2) ^ 2 * v 4) + (32 : ℝ) * (v 1 * v 3 * v 4) + (16 : ℝ) * (v 1 * v 2 * v 4) + (4 : ℝ) * ((v 1) ^ 2 * v 3) + (2 : ℝ) * ((v 1) ^ 2 * v 2) + (-32 : ℝ) * (v 0 * v 3 * v 4) + (-16 : ℝ) * (v 0 * v 2 * v 4) + (-4 : ℝ) * ((v 0) ^ 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork110, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (-16 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (16 : ℝ) * (v 0 * v 3 * v 4 * h 0) + (-8 : ℝ) * (v 0 * v 2 * v 4 * h 1) + (8 : ℝ) * (v 0 * v 2 * v 4 * h 0) + (4 : ℝ) * (v 0 * v 1 * v 3 * h 0) + (2 : ℝ) * (v 0 * v 1 * v 2 * h 0) + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) = 0 := by
      linear_combination
        ((-8 : ℝ) * (v 0 * v 3 * h 0) + (-4 : ℝ) * (v 0 * v 2 * h 0) + (-2 : ℝ) * ((v 0) ^ 2 * h 0)) * g1 +
      (-(v 0 * h 0)) * g2 +
      ((-4 : ℝ) * (v 3) + (-2 : ℝ) * (v 2) + -(v 0)) * g3 +
      ((4 : ℝ) * (v 0 * v 3) + (2 : ℝ) * (v 0 * v 2) + (v 0) ^ 2) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork110, CodedBimolNetwork.toNetwork,
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
      at hg0 hg1
    have g1 : (4 : ℝ) * (v 3) + (2 : ℝ) * (v 2) = 0 := by
      nlinarith [hg1]
    have g4 : (-4 : ℝ) * (v 1 * v 3) + (-2 : ℝ) * (v 1 * v 2) + (4 : ℝ) * (v 0 * v 4) = 0 := by
      nlinarith [hdet]
    simp [-mul_eq_zero, cubicResidualNetwork110, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (16 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (-16 : ℝ) * (v 1 * v 3 * v 4 * h 0) + (8 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (-4 : ℝ) * ((v 1) ^ 2 * v 3 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * v 2 * h 0) + (4 : ℝ) * (v 0 * v 1 * v 4 * h 1) = 0 := by
      linear_combination
        ((4 : ℝ) * (v 1 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 4 * h 0) + (v 1) ^ 2 * h 1 + -((v 1) ^ 2 * h 0)) * g1 +
      (v 1 * h 1) * g4
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork110, CodedBimolNetwork.toNetwork,
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
      at hg0 hg1
    have g0 : (-4 : ℝ) * (v 3) + (-2 : ℝ) * (v 2) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : (4 : ℝ) * (v 4) + v 1 = 0 := by
      nlinarith [hg1]
    have g2 : (2 : ℝ) * (v 4) + (-2 : ℝ) * (v 3) + -(v 2) + v 1 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g4 : (-4 : ℝ) * (v 1 * v 3) + (-2 : ℝ) * (v 1 * v 2) + (4 : ℝ) * (v 0 * v 4) = 0 := by
      nlinarith [hdet]
    have g5 : (64 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (-64 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (32 : ℝ) * (v 0 * v 2 * (v 4) ^ 2) + (-64 : ℝ) * (v 0 * v 2 * v 3 * v 4) + (-16 : ℝ) * (v 0 * (v 2) ^ 2 * v 4) = 0 := by
      nlinarith [hfold]
    have g7 : (-4 : ℝ) * (v 4 * h 1) + (4 : ℝ) * (v 3 * h 0) + (64 : ℝ) * (v 3 * (v 4) ^ 2) + (-64 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * (v 2 * h 0) + (32 : ℝ) * (v 2 * (v 4) ^ 2) + (-64 : ℝ) * (v 2 * v 3 * v 4) + (-16 : ℝ) * ((v 2) ^ 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork110, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (16 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (-16 : ℝ) * (v 0 * v 3 * v 4 * h 0) + (8 : ℝ) * (v 0 * v 2 * v 4 * h 1) + (-8 : ℝ) * (v 0 * v 2 * v 4 * h 0) = 0 := by
      linear_combination
        (-(v 0 * v 1 * h 0) + (2 : ℝ) * ((v 0) ^ 2 * h 0)) * g0 +
      ((4 : ℝ) * (v 0 * v 3 * h 1) + (-4 : ℝ) * (v 0 * v 3 * h 0) + (2 : ℝ) * (v 0 * v 2 * h 1) + (-2 : ℝ) * (v 0 * v 2 * h 0) + (v 0) ^ 2 * h 0) * g1 +
      ((-2 : ℝ) * ((v 0) ^ 2 * h 0)) * g2 +
      (v 0 * h 1) * g4 +
      (-(v 0)) * g5 +
      ((v 0) ^ 2) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork110, CodedBimolNetwork.toNetwork,
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
      at hg0 hg1 hg2
    have g1 : (4 : ℝ) * (v 4) + v 1 = 0 := by
      nlinarith [hg1]
    have g2 : (4 : ℝ) * (v 3) + (2 : ℝ) * (v 2) = 0 := by
      nlinarith [hg2]
    simp [-mul_eq_zero, cubicResidualNetwork110, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (-16 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (16 : ℝ) * (v 1 * v 3 * v 4 * h 0) + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (8 : ℝ) * (v 1 * v 2 * v 4 * h 0) = 0 := by
      linear_combination
        ((16 : ℝ) * (v 3 * v 4 * h 0) + (8 : ℝ) * (v 2 * v 4 * h 0) + (-4 : ℝ) * (v 1 * v 3 * h 1) + (-2 : ℝ) * (v 1 * v 2 * h 1)) * g1 +
      ((-16 : ℝ) * ((v 4) ^ 2 * h 0) + (v 1) ^ 2 * h 1) * g2
    nlinarith [hcertificate]

theorem cubicResidualNetwork110_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork110.toNetwork := by
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
  simp [cubicResidualNetwork110, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork110_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork110.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork110_jacobianNonzero
    cubicResidualNetwork110_fourCharts

def cubicResidualNetwork111 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xx, .xy), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork111_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork111.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork111, CodedBimolNetwork.toNetwork,
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
      at heq0 heq1 hdet hfold hc0 hc1
  case false.false =>
    have g0 : v 4 + -(v 3) + v 1 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g1 : -(v 4) + v 3 + v 2 + -(v 1) = 0 := by
      nlinarith [heq1]
    have g2 : v 2 * v 4 + (-2 : ℝ) * (v 2 * v 3) + v 0 * v 4 + -(v 0 * v 2) + v 0 * v 1 = 0 := by
      nlinarith [hdet]
    have g3 : (2 : ℝ) * (v 0 * (v 4) ^ 3) + (-2 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * v 1 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * (v 1) ^ 2 * v 3) + (-2 : ℝ) * ((v 0) ^ 2 * (v 4) ^ 2) + (-2 : ℝ) * ((v 0) ^ 2 * v 1 * v 4) = 0 := by
      nlinarith [hfold]
    have g4 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + (-2 : ℝ) * (v 3 * h 0) + (2 : ℝ) * (v 3 * (v 4) ^ 2) + v 1 * h 1 + (-2 : ℝ) * (v 1 * (v 4) ^ 2) + (-2 : ℝ) * ((v 1) ^ 2 * v 3) + -(v 0 * h 0) + (2 : ℝ) * (v 0 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * v 1 * v 4) = 0 := by
      nlinarith [hc0]
    have g5 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (2 : ℝ) * (v 3 * h 0) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + v 2 * h 1 + -(v 1 * h 1) + (2 : ℝ) * (v 1 * (v 4) ^ 2) + (2 : ℝ) * ((v 1) ^ 2 * v 3) + (-2 : ℝ) * (v 0 * (v 4) ^ 2) + (-2 : ℝ) * (v 0 * v 1 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork111, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -(v 0 * (v 4) ^ 2 * h 1) + v 0 * (v 4) ^ 2 * h 0 + -(v 0 * v 1 * v 4 * h 1) + (2 : ℝ) * (v 0 * v 1 * v 3 * h 0) + -((v 0) ^ 2 * v 4 * h 0) = 0 := by
      linear_combination
        ((-2 : ℝ) * ((v 4) ^ 2 * h 0) + ((5 : ℝ) / 2) * (v 3 * v 4 * h 1) + ((-1 : ℝ) / 2) * ((v 3) ^ 2 * h 1) + (4 : ℝ) * (v 2 * v 4 * h 0) + v 2 * v 3 * h 1 + ((3 : ℝ) / 2) * ((v 2) ^ 2 * h 1) + (-5 : ℝ) * (v 1 * v 4 * h 0) + ((1 : ℝ) / 2) * (v 1 * v 3 * h 1) + -(v 1 * v 3 * h 0) + ((-3 : ℝ) / 2) * (v 1 * v 2 * h 1) + (3 : ℝ) * (v 1 * v 2 * h 0) + (-3 : ℝ) * ((v 1) ^ 2 * h 0) + ((1 : ℝ) / 2) * (v 0 * v 3 * h 1) + v 0 * v 2 * h 0 + -(v 0 * v 1 * h 0)) * g0 +
      ((-2 : ℝ) * ((v 4) ^ 2 * h 0) + ((5 : ℝ) / 2) * (v 3 * v 4 * h 1) + ((-1 : ℝ) / 2) * ((v 3) ^ 2 * h 1) + ((3 : ℝ) / 2) * (v 2 * v 3 * h 1) + (-5 : ℝ) * (v 1 * v 4 * h 0) + ((1 : ℝ) / 2) * (v 1 * v 3 * h 1) + -(v 1 * v 3 * h 0) + ((-3 : ℝ) / 2) * (v 1 * v 2 * h 1) + (-3 : ℝ) * ((v 1) ^ 2 * h 0) + (2 : ℝ) * (v 0 * v 4 * h 1) + (2 : ℝ) * (v 0 * v 2 * h 1) + ((1 : ℝ) / 2) * ((v 0) ^ 2 * h 1)) * g1 +
      (v 4 * h 1 + (-2 : ℝ) * (v 4 * h 0) + (-2 : ℝ) * (v 1 * h 0) + ((1 : ℝ) / 2) * (v 0 * h 1) + -(v 0 * h 0)) * g2 +
      (((1 : ℝ) / 2) * (v 2)) * g3 +
      (-((v 4) ^ 2) + ((-3 : ℝ) / 2) * (v 2 * v 4)) * g4 +
      (-((v 4) ^ 2) + ((-3 : ℝ) / 2) * (v 2 * v 4) + ((-1 : ℝ) / 2) * (v 0 * v 2)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork111, CodedBimolNetwork.toNetwork,
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
      at hg0 hg1
    have g0 : v 4 + (-2 : ℝ) * (v 3) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : -(v 4) + (2 : ℝ) * (v 3) = 0 := by
      nlinarith [hg1]
    have g2 : v 4 + -(v 3) + v 1 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : -(v 4) + v 3 + v 2 + -(v 1) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork111, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 2 * (v 4) ^ 2 * h 1 + -(v 2 * (v 4) ^ 2 * h 0) + v 1 * v 2 * v 4 * h 1 + (-2 : ℝ) * (v 1 * v 2 * v 3 * h 0) + v 0 * v 2 * v 4 * h 0 = 0 := by
      linear_combination
        (v 2 * v 4 * h 0 + (-4 : ℝ) * (v 2 * v 3 * h 1) + (2 : ℝ) * (v 1 * v 2 * h 1) + (-2 : ℝ) * (v 1 * v 2 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * h 1) + (2 : ℝ) * ((v 1) ^ 2 * h 0)) * g0 +
      (-(v 2 * v 4 * h 1) + (-2 : ℝ) * (v 2 * v 3 * h 1) + -(v 1 * v 2 * h 1) + (-2 : ℝ) * (v 1 * v 2 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * h 1) + (2 : ℝ) * ((v 1) ^ 2 * h 0)) * g1 +
      ((-2 : ℝ) * (v 2 * v 4 * h 0) + (4 : ℝ) * (v 2 * v 3 * h 1) + (-2 : ℝ) * (v 1 * v 2 * h 1) + (2 : ℝ) * (v 1 * v 2 * h 0) + (2 : ℝ) * ((v 1) ^ 2 * h 1) + (-2 : ℝ) * ((v 1) ^ 2 * h 0)) * g2 +
      ((2 : ℝ) * ((v 1) ^ 2 * h 1) + (-2 : ℝ) * ((v 1) ^ 2 * h 0)) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork111, CodedBimolNetwork.toNetwork,
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
      at hg0 hg1
    have g0 : v 4 + (-2 : ℝ) * (v 3) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : v 4 + v 1 = 0 := by
      nlinarith [hg1]
    have g2 : v 4 + -(v 3) + v 1 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : -(v 4) + v 3 + v 2 + -(v 1) = 0 := by
      nlinarith [heq1]
    have g6 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + (-2 : ℝ) * (v 3 * h 0) + (2 : ℝ) * (v 3 * (v 4) ^ 2) + (2 : ℝ) * (v 2 * (v 4) ^ 2) + (-2 : ℝ) * ((v 2) ^ 2 * v 3) + v 1 * h 1 + (-2 : ℝ) * (v 1 * (v 4) ^ 2) + (4 : ℝ) * (v 1 * v 2 * v 3) + (-2 : ℝ) * ((v 1) ^ 2 * v 3) + -(v 0 * h 0) = 0 := by
      nlinarith [hc0]
    have g7 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (2 : ℝ) * (v 3 * h 0) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + v 2 * h 1 + (-2 : ℝ) * (v 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 2) ^ 2 * v 3) + -(v 1 * h 1) + (2 : ℝ) * (v 1 * (v 4) ^ 2) + (-4 : ℝ) * (v 1 * v 2 * v 3) + (2 : ℝ) * ((v 1) ^ 2 * v 3) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork111, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 0 * (v 4) ^ 2 * h 1 + -(v 0 * (v 4) ^ 2 * h 0) + -(v 0 * v 2 * v 4 * h 1) + (2 : ℝ) * (v 0 * v 2 * v 3 * h 0) + v 0 * v 1 * v 4 * h 1 + (-2 : ℝ) * (v 0 * v 1 * v 3 * h 0) = 0 := by
      linear_combination
        (((-1 : ℝ) / 2) * (v 3 * v 4 * h 1) + -((v 2) ^ 2 * h 1) + ((-1 : ℝ) / 2) * (v 0 * v 4 * h 1) + -(v 0 * v 4 * h 0) + -((v 0) ^ 2 * h 0)) * g0 +
      (((1 : ℝ) / 2) * ((v 4) ^ 2 * h 1) + -((v 3) ^ 2 * h 1) + v 2 * v 4 * h 1 + -(v 2 * v 3 * h 1) + (-2 : ℝ) * ((v 2) ^ 2 * h 1) + v 1 * v 3 * h 1 + ((1 : ℝ) / 2) * (v 0 * v 4 * h 1) + (-2 : ℝ) * (v 0 * v 3 * h 1) + -(v 0 * v 3 * h 0) + -(v 0 * v 2 * h 1) + v 0 * v 1 * h 1 + (v 0) ^ 2 * h 1 + -((v 0) ^ 2 * h 0)) * g1 +
      (((-1 : ℝ) / 2) * ((v 4) ^ 2 * h 1) + -((v 3) ^ 2 * h 1) + (2 : ℝ) * ((v 2) ^ 2 * h 1) + ((1 : ℝ) / 2) * (v 0 * v 4 * h 1) + v 0 * v 3 * h 1 + v 0 * v 3 * h 0 + v 0 * v 2 * h 1 + (v 0) ^ 2 * h 0) * g2 +
      (-((v 3) ^ 2 * h 1) + v 2 * v 4 * h 1 + v 1 * v 3 * h 1 + (2 : ℝ) * (v 0 * v 3 * h 0) + v 0 * v 2 * h 1 + v 0 * v 1 * h 1 + (v 0) ^ 2 * h 1) * g3 +
      ((v 3) ^ 2) * g6 +
      ((v 3) ^ 2) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork111, CodedBimolNetwork.toNetwork,
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
      at hg0 hg1 hg2
    have g0 : v 4 + (-2 : ℝ) * (v 3) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : v 4 + v 1 = 0 := by
      nlinarith [hg1]
    have g2 : -(v 4) + (2 : ℝ) * (v 3) = 0 := by
      nlinarith [hg2]
    have g3 : v 4 + -(v 3) + v 1 + -(v 0) = 0 := by
      nlinarith [heq0]
    simp [-mul_eq_zero, cubicResidualNetwork111, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -(v 2 * (v 4) ^ 2 * h 1) + v 2 * (v 4) ^ 2 * h 0 + (v 2) ^ 2 * v 4 * h 1 + (-2 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + -(v 1 * v 2 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((2 : ℝ) * ((v 2) ^ 2 * h 1) + (-2 : ℝ) * ((v 2) ^ 2 * h 0)) * g0 +
      (-(v 2 * v 4 * h 1) + v 2 * v 4 * h 0 + (2 : ℝ) * ((v 2) ^ 2 * h 1) + (-2 : ℝ) * ((v 2) ^ 2 * h 0)) * g1 +
      ((v 2) ^ 2 * h 1 + (-2 : ℝ) * ((v 2) ^ 2 * h 0) + v 1 * v 2 * h 0) * g2 +
      ((-2 : ℝ) * ((v 2) ^ 2 * h 1) + (2 : ℝ) * ((v 2) ^ 2 * h 0)) * g3
    nlinarith [hcertificate]

theorem cubicResidualNetwork111_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork111.toNetwork := by
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
  simp [cubicResidualNetwork111, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork111_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork111.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork111_jacobianNonzero
    cubicResidualNetwork111_fourCharts

def cubicResidualNetwork112 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xx, .xy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork112_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork112.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork112, CodedBimolNetwork.toNetwork,
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
      at heq0 heq1 hdet hfold hc0 hc1
  case false.false =>
    have g0 : (2 : ℝ) * (v 4) + -(v 3) + v 1 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g1 : (-2 : ℝ) * (v 4) + v 3 + v 2 + -(v 1) = 0 := by
      nlinarith [heq1]
    have g2 : (-2 : ℝ) * (v 2 * v 3) + (4 : ℝ) * (v 0 * v 4) + -(v 0 * v 2) + v 0 * v 1 = 0 := by
      nlinarith [hdet]
    have g3 : (32 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (-16 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (16 : ℝ) * (v 0 * v 1 * v 3 * v 4) + (2 : ℝ) * (v 0 * (v 1) ^ 2 * v 3) + (-16 : ℝ) * ((v 0) ^ 2 * v 3 * v 4) + (-4 : ℝ) * ((v 0) ^ 3 * v 4) = 0 := by
      nlinarith [hfold]
    have g4 : (4 : ℝ) * (v 4 * h 1) + (-2 : ℝ) * (v 3 * h 0) + (-32 : ℝ) * (v 3 * (v 4) ^ 2) + (16 : ℝ) * ((v 3) ^ 2 * v 4) + v 1 * h 1 + (-16 : ℝ) * (v 1 * v 3 * v 4) + (-2 : ℝ) * ((v 1) ^ 2 * v 3) + -(v 0 * h 0) + (16 : ℝ) * (v 0 * v 3 * v 4) + (4 : ℝ) * ((v 0) ^ 2 * v 4) = 0 := by
      nlinarith [hc0]
    have g5 : (-4 : ℝ) * (v 4 * h 1) + (2 : ℝ) * (v 3 * h 0) + (32 : ℝ) * (v 3 * (v 4) ^ 2) + (-16 : ℝ) * ((v 3) ^ 2 * v 4) + v 2 * h 1 + -(v 1 * h 1) + (16 : ℝ) * (v 1 * v 3 * v 4) + (2 : ℝ) * ((v 1) ^ 2 * v 3) + (-16 : ℝ) * (v 0 * v 3 * v 4) + (-4 : ℝ) * ((v 0) ^ 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork112, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (-8 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (8 : ℝ) * (v 0 * v 3 * v 4 * h 0) + (2 : ℝ) * (v 0 * v 1 * v 3 * h 0) + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) = 0 := by
      linear_combination
        ((-8 : ℝ) * (v 3 * v 4 * h 1) + (4 : ℝ) * ((v 3) ^ 2 * h 0) + (4 : ℝ) * (v 2 * v 4 * h 1) + (4 : ℝ) * (v 2 * v 3 * h 1) + (4 : ℝ) * (v 2 * v 3 * h 0) + (-4 : ℝ) * (v 1 * v 3 * h 1) + (4 : ℝ) * (v 0 * v 4 * h 1) + (-16 : ℝ) * (v 0 * v 4 * h 0) + (4 : ℝ) * (v 0 * v 2 * h 0) + (-4 : ℝ) * (v 0 * v 1 * h 0)) * g0 +
      ((-8 : ℝ) * (v 3 * v 4 * h 1) + (4 : ℝ) * ((v 3) ^ 2 * h 0) + (4 : ℝ) * (v 2 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 3 * h 1) + (4 : ℝ) * (v 0 * v 4 * h 1) + (-8 : ℝ) * (v 0 * v 4 * h 0) + (-2 : ℝ) * (v 0 * v 1 * h 0)) * g1 +
      ((4 : ℝ) * (v 4 * h 0) + (-2 : ℝ) * (v 3 * h 1) + (2 : ℝ) * (v 1 * h 0) + (-4 : ℝ) * (v 0 * h 0)) * g2 +
      ((-2 : ℝ) * (v 3)) * g3 +
      ((-4 : ℝ) * (v 2 * v 4)) * g4 +
      ((-4 : ℝ) * (v 2 * v 4) + (2 : ℝ) * (v 0 * v 3)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork112, CodedBimolNetwork.toNetwork,
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
      at hg0 hg1
    have g0 : (-2 : ℝ) * (v 3) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : (2 : ℝ) * (v 3) = 0 := by
      nlinarith [hg1]
    simp [-mul_eq_zero, cubicResidualNetwork112, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (8 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (-8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (-2 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (4 : ℝ) * (v 0 * v 2 * v 4 * h 1) = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 2 * v 4 * h 1)) * g0 +
      ((-4 : ℝ) * (v 2 * v 4 * h 0) + -(v 1 * v 2 * h 0)) * g1
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork112, CodedBimolNetwork.toNetwork,
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
      at hg0 hg1
    have g0 : (-2 : ℝ) * (v 3) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : (4 : ℝ) * (v 4) + v 1 = 0 := by
      nlinarith [hg1]
    have g2 : (2 : ℝ) * (v 4) + -(v 3) + v 1 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : (-2 : ℝ) * (v 4) + v 3 + v 2 + -(v 1) = 0 := by
      nlinarith [heq1]
    have g6 : (4 : ℝ) * (v 4 * h 1) + (-2 : ℝ) * (v 3 * h 0) + (-32 : ℝ) * (v 3 * (v 4) ^ 2) + (16 : ℝ) * ((v 3) ^ 2 * v 4) + (16 : ℝ) * (v 2 * v 3 * v 4) + (-2 : ℝ) * ((v 2) ^ 2 * v 3) + v 1 * h 1 + (-16 : ℝ) * (v 1 * v 3 * v 4) + (4 : ℝ) * (v 1 * v 2 * v 3) + (-2 : ℝ) * ((v 1) ^ 2 * v 3) + -(v 0 * h 0) = 0 := by
      nlinarith [hc0]
    have g7 : (-4 : ℝ) * (v 4 * h 1) + (2 : ℝ) * (v 3 * h 0) + (32 : ℝ) * (v 3 * (v 4) ^ 2) + (-16 : ℝ) * ((v 3) ^ 2 * v 4) + v 2 * h 1 + (-16 : ℝ) * (v 2 * v 3 * v 4) + (2 : ℝ) * ((v 2) ^ 2 * v 3) + -(v 1 * h 1) + (16 : ℝ) * (v 1 * v 3 * v 4) + (-4 : ℝ) * (v 1 * v 2 * v 3) + (2 : ℝ) * ((v 1) ^ 2 * v 3) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork112, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (8 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (-8 : ℝ) * (v 0 * v 3 * v 4 * h 0) + (2 : ℝ) * (v 0 * v 2 * v 3 * h 0) + (-2 : ℝ) * (v 0 * v 1 * v 3 * h 0) = 0 := by
      linear_combination
        ((-4 : ℝ) * ((v 3) ^ 2 * h 1) + (-4 : ℝ) * ((v 3) ^ 2 * h 0) + (-4 : ℝ) * (v 2 * v 4 * h 1) + (-2 : ℝ) * (v 2 * v 3 * h 1) + (-2 : ℝ) * (v 2 * v 3 * h 0) + (2 : ℝ) * (v 1 * v 3 * h 1) + (2 : ℝ) * (v 1 * v 3 * h 0) + (-2 : ℝ) * (v 1 * v 2 * h 1) + (-4 : ℝ) * (v 0 * v 4 * h 1) + (4 : ℝ) * (v 0 * v 4 * h 0) + (2 : ℝ) * (v 0 * v 2 * h 1) + -(v 0 * v 1 * h 1) + v 0 * v 1 * h 0) * g0 +
      ((-4 : ℝ) * ((v 3) ^ 2 * h 1) + (-4 : ℝ) * ((v 3) ^ 2 * h 0) + (-2 : ℝ) * (v 2 * v 3 * h 1) + -((v 0) ^ 2 * h 1) + (v 0) ^ 2 * h 0) * g1 +
      ((4 : ℝ) * ((v 3) ^ 2 * h 1) + (4 : ℝ) * ((v 3) ^ 2 * h 0) + (-2 : ℝ) * (v 0 * v 2 * h 1)) * g2 +
      ((-4 : ℝ) * ((v 3) ^ 2 * h 1) + (-4 : ℝ) * ((v 3) ^ 2 * h 0)) * g3 +
      ((-2 : ℝ) * (v 1 * v 3)) * g6 +
      ((-2 : ℝ) * (v 1 * v 3)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork112, CodedBimolNetwork.toNetwork,
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
      at hg0 hg1 hg2
    have g2 : (2 : ℝ) * (v 3) = 0 := by
      nlinarith [hg2]
    simp [-mul_eq_zero, cubicResidualNetwork112, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (-8 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (-2 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + (2 : ℝ) * (v 1 * v 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 2 * v 4 * h 1) + (4 : ℝ) * (v 2 * v 4 * h 0) + -((v 2) ^ 2 * h 0) + v 1 * v 2 * h 0) * g2
    nlinarith [hcertificate]

theorem cubicResidualNetwork112_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork112.toNetwork := by
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
  simp [cubicResidualNetwork112, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork112_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork112.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork112_jacobianNonzero
    cubicResidualNetwork112_fourCharts

def cubicResidualNetwork113 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xx, .xy), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork113_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork113.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork113, CodedBimolNetwork.toNetwork,
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
      at heq0 heq1 hdet hfold hc0 hc1
  case false.false =>
    have g0 : v 4 + -(v 3) + (2 : ℝ) * (v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g1 : -(v 4) + v 3 + v 2 + -(v 1) = 0 := by
      nlinarith [heq1]
    have g2 : v 2 * v 4 + (-2 : ℝ) * (v 2 * v 3) + v 1 * v 4 + (-2 : ℝ) * (v 1 * v 3) + v 0 * v 4 + -(v 0 * v 2) + v 0 * v 1 = 0 := by
      nlinarith [hdet]
    have g4 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + (-2 : ℝ) * (v 3 * h 0) + (2 : ℝ) * (v 3 * (v 4) ^ 2) + (2 : ℝ) * (v 1 * h 1) + (-4 : ℝ) * (v 1 * (v 4) ^ 2) + (-8 : ℝ) * ((v 1) ^ 2 * v 3) + -(v 0 * h 0) + (2 : ℝ) * (v 0 * (v 4) ^ 2) + (4 : ℝ) * (v 0 * v 1 * v 4) = 0 := by
      nlinarith [hc0]
    have g5 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (2 : ℝ) * (v 3 * h 0) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + v 2 * h 1 + -(v 1 * h 1) + (4 : ℝ) * (v 1 * (v 4) ^ 2) + (8 : ℝ) * ((v 1) ^ 2 * v 3) + (-2 : ℝ) * (v 0 * (v 4) ^ 2) + (-4 : ℝ) * (v 0 * v 1 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork113, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -(v 0 * (v 4) ^ 2 * h 1) + v 0 * (v 4) ^ 2 * h 0 + (-2 : ℝ) * (v 0 * v 1 * v 4 * h 1) + (4 : ℝ) * (v 0 * v 1 * v 3 * h 0) + -((v 0) ^ 2 * v 4 * h 0) = 0 := by
      linear_combination
        (-((v 4) ^ 2 * h 1) + (4 : ℝ) * (v 3 * v 4 * h 1) + (-3 : ℝ) * ((v 3) ^ 2 * h 0) + (2 : ℝ) * (v 2 * v 4 * h 1) + (-2 : ℝ) * (v 2 * v 3 * h 1) + (2 : ℝ) * (v 2 * v 3 * h 0) + (v 2) ^ 2 * h 0 + (-4 : ℝ) * (v 1 * v 3 * h 0) + -((v 1) ^ 2 * h 0) + v 0 * v 4 * h 0) * g0 +
      (-((v 4) ^ 2 * h 1) + (4 : ℝ) * (v 3 * v 4 * h 1) + (-3 : ℝ) * ((v 3) ^ 2 * h 0) + (2 : ℝ) * (v 2 * v 4 * h 1) + (-2 : ℝ) * (v 2 * v 3 * h 1) + -(v 2 * v 3 * h 0) + (-7 : ℝ) * (v 1 * v 3 * h 0) + (-2 : ℝ) * (v 1 * v 2 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * h 0) + (4 : ℝ) * (v 0 * v 4 * h 1) + v 0 * v 4 * h 0 + (-3 : ℝ) * (v 0 * v 3 * h 0) + (-2 : ℝ) * (v 0 * v 2 * h 1)) * g1 +
      ((2 : ℝ) * (v 4 * h 1) + (-3 : ℝ) * (v 3 * h 0) + (-2 : ℝ) * (v 2 * h 1) + -(v 2 * h 0) + -(v 1 * h 0)) * g2 +
      (-((v 4) ^ 2) + (-2 : ℝ) * (v 2 * v 3)) * g4 +
      (-((v 4) ^ 2) + (-2 : ℝ) * (v 2 * v 3)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork113, CodedBimolNetwork.toNetwork,
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
      at hg0 hg1
    have g0 : v 4 + (-2 : ℝ) * (v 3) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : -(v 4) + (2 : ℝ) * (v 3) = 0 := by
      nlinarith [hg1]
    have g2 : v 4 + -(v 3) + (2 : ℝ) * (v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : -(v 4) + v 3 + v 2 + -(v 1) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork113, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 2 * (v 4) ^ 2 * h 1 + -(v 2 * (v 4) ^ 2 * h 0) + v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + (2 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (2 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (-4 : ℝ) * ((v 1) ^ 2 * v 3 * h 0) + v 0 * v 2 * v 4 * h 0 + v 0 * v 1 * v 4 * h 0 = 0 := by
      linear_combination
        (-(v 2 * v 4 * h 0) + (-4 : ℝ) * (v 2 * v 3 * h 1) + (4 : ℝ) * ((v 2) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 3 * h 0) + (-4 : ℝ) * (v 1 * v 2 * h 0)) * g0 +
      (-(v 2 * v 4 * h 1) + (-2 : ℝ) * (v 2 * v 4 * h 0) + (-2 : ℝ) * (v 2 * v 3 * h 1) + (2 : ℝ) * ((v 2) ^ 2 * h 0) + -(v 1 * v 4 * h 1) + -(v 1 * v 4 * h 0) + (2 : ℝ) * (v 1 * v 3 * h 1) + (-2 : ℝ) * (v 1 * v 3 * h 0) + (-2 : ℝ) * (v 1 * v 2 * h 1) + (-8 : ℝ) * (v 1 * v 2 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * h 1) + (-2 : ℝ) * ((v 1) ^ 2 * h 0) + -(v 0 * v 1 * h 0)) * g1 +
      ((4 : ℝ) * (v 2 * v 3 * h 1) + (-4 : ℝ) * ((v 2) ^ 2 * h 0) + (4 : ℝ) * (v 1 * v 2 * h 0)) * g2 +
      ((2 : ℝ) * (v 2 * v 4 * h 0) + (2 : ℝ) * (v 1 * v 4 * h 0) + (-4 : ℝ) * (v 1 * v 3 * h 1) + (8 : ℝ) * (v 1 * v 2 * h 0)) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork113, CodedBimolNetwork.toNetwork,
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
      at hg0 hg1
    have g0 : v 4 + (-2 : ℝ) * (v 3) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : v 4 + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [hg1]
    have g2 : v 4 + -(v 3) + (2 : ℝ) * (v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : -(v 4) + v 3 + v 2 + -(v 1) = 0 := by
      nlinarith [heq1]
    have g6 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + (-2 : ℝ) * (v 3 * h 0) + (2 : ℝ) * (v 3 * (v 4) ^ 2) + (2 : ℝ) * (v 2 * (v 4) ^ 2) + (-2 : ℝ) * ((v 2) ^ 2 * v 3) + (2 : ℝ) * (v 1 * h 1) + (-2 : ℝ) * (v 1 * (v 4) ^ 2) + (4 : ℝ) * (v 1 * v 2 * v 3) + (-2 : ℝ) * ((v 1) ^ 2 * v 3) + -(v 0 * h 0) = 0 := by
      nlinarith [hc0]
    have g7 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (2 : ℝ) * (v 3 * h 0) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + v 2 * h 1 + (-2 : ℝ) * (v 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 2) ^ 2 * v 3) + -(v 1 * h 1) + (2 : ℝ) * (v 1 * (v 4) ^ 2) + (-4 : ℝ) * (v 1 * v 2 * v 3) + (2 : ℝ) * ((v 1) ^ 2 * v 3) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork113, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 0 * (v 4) ^ 2 * h 1 + -(v 0 * (v 4) ^ 2 * h 0) + -(v 0 * v 2 * v 4 * h 1) + (2 : ℝ) * (v 0 * v 2 * v 3 * h 0) + v 0 * v 1 * v 4 * h 1 + (-2 : ℝ) * (v 0 * v 1 * v 3 * h 0) = 0 := by
      linear_combination
        ((-2 : ℝ) * (v 2 * v 3 * h 0) + (-4 : ℝ) * ((v 2) ^ 2 * h 1) + (-4 : ℝ) * (v 1 * v 2 * h 1) + v 0 * v 4 * h 1 + -(v 0 * v 4 * h 0)) * g0 +
      ((-2 : ℝ) * (v 2 * v 3 * h 0) + (-4 : ℝ) * ((v 2) ^ 2 * h 1) + (4 : ℝ) * ((v 2) ^ 2 * h 0) + (-4 : ℝ) * (v 1 * v 2 * h 1) + (2 : ℝ) * (v 0 * v 4 * h 1) + -(v 0 * v 4 * h 0) + -(v 0 * v 3 * h 0) + (-2 : ℝ) * (v 0 * v 2 * h 1)) * g1 +
      ((4 : ℝ) * ((v 2) ^ 2 * h 1) + (-4 : ℝ) * ((v 2) ^ 2 * h 0) + -(v 0 * v 4 * h 1) + v 0 * v 4 * h 0) * g2 +
      ((-4 : ℝ) * (v 2 * v 3 * h 0) + (-4 : ℝ) * ((v 2) ^ 2 * h 1) + (-8 : ℝ) * (v 1 * v 2 * h 1) + v 0 * v 4 * h 1) * g3 +
      ((4 : ℝ) * ((v 2) ^ 2)) * g6 +
      ((4 : ℝ) * ((v 2) ^ 2)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork113, CodedBimolNetwork.toNetwork,
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
      at hg0 hg1 hg2
    have g0 : v 4 + (-2 : ℝ) * (v 3) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : v 4 + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [hg1]
    have g2 : -(v 4) + (2 : ℝ) * (v 3) = 0 := by
      nlinarith [hg2]
    have g3 : v 4 + -(v 3) + (2 : ℝ) * (v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g4 : -(v 4) + v 3 + v 2 + -(v 1) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork113, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -(v 2 * (v 4) ^ 2 * h 1) + v 2 * (v 4) ^ 2 * h 0 + (v 2) ^ 2 * v 4 * h 1 + (-2 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + -((v 1) ^ 2 * v 4 * h 1) + (2 : ℝ) * ((v 1) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        (v 3 * v 4 * h 1 + (2 : ℝ) * ((v 2) ^ 2 * h 1) + (-2 : ℝ) * ((v 2) ^ 2 * h 0) + (2 : ℝ) * (v 1 * v 3 * h 0)) * g0 +
      (((-1 : ℝ) / 2) * (v 3 * v 4 * h 0) + (v 3) ^ 2 * h 1 + (v 3) ^ 2 * h 0 + -(v 2 * v 4 * h 1) + v 2 * v 4 * h 0 + (2 : ℝ) * ((v 2) ^ 2 * h 1) + (-2 : ℝ) * ((v 2) ^ 2 * h 0) + -(v 1 * v 4 * h 0) + v 1 * v 3 * h 1 + (3 : ℝ) * (v 1 * v 3 * h 0)) * g1 +
      (((-1 : ℝ) / 2) * (v 3 * v 4 * h 0) + (v 2) ^ 2 * h 1 + (-2 : ℝ) * ((v 2) ^ 2 * h 0) + -(v 1 * v 4 * h 1) + -(v 1 * v 3 * h 1) + -((v 1) ^ 2 * h 1)) * g2 +
      (-(v 3 * v 4 * h 1) + (-2 : ℝ) * ((v 2) ^ 2 * h 1) + (2 : ℝ) * ((v 2) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 3 * h 0)) * g3 +
      ((2 : ℝ) * (v 1 * v 4 * h 1) + (-2 : ℝ) * (v 1 * v 4 * h 0)) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork113_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork113.toNetwork := by
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
  simp [cubicResidualNetwork113, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork113_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork113.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork113_jacobianNonzero
    cubicResidualNetwork113_fourCharts

def cubicResidualNetwork114 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xx, .xy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork114_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork114.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork114, CodedBimolNetwork.toNetwork,
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
      at heq0 heq1 hdet hfold hc0 hc1
  case false.false =>
    have g0 : (2 : ℝ) * (v 4) + -(v 3) + (2 : ℝ) * (v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g1 : (-2 : ℝ) * (v 4) + v 3 + v 2 + -(v 1) = 0 := by
      nlinarith [heq1]
    have g2 : (-2 : ℝ) * (v 2 * v 3) + (-2 : ℝ) * (v 1 * v 3) + (4 : ℝ) * (v 0 * v 4) + -(v 0 * v 2) + v 0 * v 1 = 0 := by
      nlinarith [hdet]
    have g3 : (32 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (-16 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (32 : ℝ) * (v 0 * v 1 * v 3 * v 4) + (8 : ℝ) * (v 0 * (v 1) ^ 2 * v 3) + (-16 : ℝ) * ((v 0) ^ 2 * v 3 * v 4) + (-4 : ℝ) * ((v 0) ^ 3 * v 4) = 0 := by
      nlinarith [hfold]
    have g5 : (-4 : ℝ) * (v 4 * h 1) + (2 : ℝ) * (v 3 * h 0) + (32 : ℝ) * (v 3 * (v 4) ^ 2) + (-16 : ℝ) * ((v 3) ^ 2 * v 4) + v 2 * h 1 + -(v 1 * h 1) + (32 : ℝ) * (v 1 * v 3 * v 4) + (8 : ℝ) * ((v 1) ^ 2 * v 3) + (-16 : ℝ) * (v 0 * v 3 * v 4) + (-4 : ℝ) * ((v 0) ^ 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork114, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (-8 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (8 : ℝ) * (v 0 * v 3 * v 4 * h 0) + (4 : ℝ) * (v 0 * v 1 * v 3 * h 0) + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) = 0 := by
      linear_combination
        ((24 : ℝ) * ((v 4) ^ 2 * h 1) + (-32 : ℝ) * ((v 4) ^ 2 * h 0) + (-8 : ℝ) * (v 3 * v 4 * h 1) + (6 : ℝ) * ((v 3) ^ 2 * h 1) + (-20 : ℝ) * (v 2 * v 4 * h 1) + (16 : ℝ) * (v 2 * v 4 * h 0) + (6 : ℝ) * (v 2 * v 3 * h 1) + (8 : ℝ) * (v 2 * v 3 * h 0) + (4 : ℝ) * ((v 2) ^ 2 * h 1) + (-32 : ℝ) * (v 1 * v 4 * h 0) + (2 : ℝ) * (v 1 * v 2 * h 1) + (8 : ℝ) * (v 1 * v 2 * h 0) + (-6 : ℝ) * ((v 1) ^ 2 * h 1) + (-8 : ℝ) * ((v 1) ^ 2 * h 0) + (4 : ℝ) * (v 0 * v 4 * h 1)) * g0 +
      ((24 : ℝ) * ((v 4) ^ 2 * h 1) + (-32 : ℝ) * ((v 4) ^ 2 * h 0) + (-8 : ℝ) * (v 3 * v 4 * h 1) + (6 : ℝ) * ((v 3) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * v 4 * h 1) + (8 : ℝ) * (v 2 * v 3 * h 0) + (12 : ℝ) * (v 1 * v 4 * h 1) + (-48 : ℝ) * (v 1 * v 4 * h 0) + (-6 : ℝ) * (v 1 * v 3 * h 1) + (-8 : ℝ) * (v 1 * v 2 * h 1) + (-12 : ℝ) * ((v 1) ^ 2 * h 1) + (-16 : ℝ) * ((v 1) ^ 2 * h 0) + (6 : ℝ) * (v 0 * v 3 * h 1) + (4 : ℝ) * (v 0 * v 2 * h 0) + (6 : ℝ) * (v 0 * v 1 * h 1) + (4 : ℝ) * (v 0 * v 1 * h 0)) * g1 +
      ((8 : ℝ) * (v 4 * h 1) + (-8 : ℝ) * (v 4 * h 0) + (-2 : ℝ) * (v 2 * h 1) + (4 : ℝ) * (v 2 * h 0) + (-4 : ℝ) * (v 1 * h 0)) * g2 +
      ((-4 : ℝ) * (v 4) + (-2 : ℝ) * (v 2)) * g3 +
      ((4 : ℝ) * (v 0 * v 4) + (2 : ℝ) * (v 0 * v 2)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork114, CodedBimolNetwork.toNetwork,
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
      at hg0 hg1
    have g0 : (-2 : ℝ) * (v 3) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : (2 : ℝ) * (v 3) = 0 := by
      nlinarith [hg1]
    simp [-mul_eq_zero, cubicResidualNetwork114, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (8 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (-8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (8 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 3 * v 4 * h 0) + (-4 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (-4 : ℝ) * ((v 1) ^ 2 * v 3 * h 0) + (4 : ℝ) * (v 0 * v 2 * v 4 * h 1) + (4 : ℝ) * (v 0 * v 1 * v 4 * h 1) = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 2 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 4 * h 1)) * g0 +
      ((-4 : ℝ) * (v 2 * v 4 * h 0) + (-4 : ℝ) * (v 1 * v 4 * h 0) + (-2 : ℝ) * (v 1 * v 2 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * h 0)) * g1
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork114, CodedBimolNetwork.toNetwork,
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
      at hg0 hg1
    have g0 : (-2 : ℝ) * (v 3) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : (4 : ℝ) * (v 4) + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [hg1]
    have g2 : (2 : ℝ) * (v 4) + -(v 3) + (2 : ℝ) * (v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : (-2 : ℝ) * (v 4) + v 3 + v 2 + -(v 1) = 0 := by
      nlinarith [heq1]
    have g5 : (32 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (-16 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (-16 : ℝ) * (v 0 * v 2 * v 3 * v 4) + (2 : ℝ) * (v 0 * (v 2) ^ 2 * v 3) + (16 : ℝ) * (v 0 * v 1 * v 3 * v 4) + (-4 : ℝ) * (v 0 * v 1 * v 2 * v 3) + (2 : ℝ) * (v 0 * (v 1) ^ 2 * v 3) = 0 := by
      nlinarith [hfold]
    have g7 : (-4 : ℝ) * (v 4 * h 1) + (2 : ℝ) * (v 3 * h 0) + (32 : ℝ) * (v 3 * (v 4) ^ 2) + (-16 : ℝ) * ((v 3) ^ 2 * v 4) + v 2 * h 1 + (-16 : ℝ) * (v 2 * v 3 * v 4) + (2 : ℝ) * ((v 2) ^ 2 * v 3) + -(v 1 * h 1) + (16 : ℝ) * (v 1 * v 3 * v 4) + (-4 : ℝ) * (v 1 * v 2 * v 3) + (2 : ℝ) * ((v 1) ^ 2 * v 3) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork114, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (8 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (-8 : ℝ) * (v 0 * v 3 * v 4 * h 0) + (2 : ℝ) * (v 0 * v 2 * v 3 * h 0) + (-2 : ℝ) * (v 0 * v 1 * v 3 * h 0) = 0 := by
      linear_combination
        ((4 : ℝ) * (v 3 * v 4 * h 0) + (4 : ℝ) * ((v 3) ^ 2 * h 0) + (2 : ℝ) * (v 2 * v 3 * h 1) + (2 : ℝ) * (v 2 * v 3 * h 0) + (2 : ℝ) * (v 1 * v 3 * h 1) + (-4 : ℝ) * (v 0 * v 4 * h 1) + (2 : ℝ) * (v 0 * v 4 * h 0) + (-2 : ℝ) * (v 0 * v 3 * h 1) + -(v 0 * v 2 * h 1) + (-2 : ℝ) * (v 0 * v 2 * h 0) + -(v 0 * v 1 * h 1) + v 0 * v 1 * h 0) * g0 +
      ((6 : ℝ) * ((v 3) ^ 2 * h 0) + -((v 0) ^ 2 * h 1) + ((-1 : ℝ) / 2) * ((v 0) ^ 2 * h 0)) * g1 +
      ((4 : ℝ) * ((v 3) ^ 2 * h 1) + (-4 : ℝ) * ((v 3) ^ 2 * h 0)) * g2 +
      ((4 : ℝ) * ((v 3) ^ 2 * h 1) + (4 : ℝ) * ((v 3) ^ 2 * h 0) + (-2 : ℝ) * ((v 0) ^ 2 * h 1) + (-2 : ℝ) * ((v 0) ^ 2 * h 0)) * g3 +
      (-(v 0)) * g5 +
      ((v 0) ^ 2) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork114, CodedBimolNetwork.toNetwork,
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
      at hg0 hg1 hg2
    have g2 : (2 : ℝ) * (v 3) = 0 := by
      nlinarith [hg2]
    simp [-mul_eq_zero, cubicResidualNetwork114, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (-8 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (-2 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + (-8 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (8 : ℝ) * (v 1 * v 3 * v 4 * h 0) + (2 : ℝ) * ((v 1) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 2 * v 4 * h 1) + (4 : ℝ) * (v 2 * v 4 * h 0) + -((v 2) ^ 2 * h 0) + (-4 : ℝ) * (v 1 * v 4 * h 1) + (4 : ℝ) * (v 1 * v 4 * h 0) + (v 1) ^ 2 * h 0) * g2
    nlinarith [hcertificate]

theorem cubicResidualNetwork114_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork114.toNetwork := by
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
  simp [cubicResidualNetwork114, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork114_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork114.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork114_jacobianNonzero
    cubicResidualNetwork114_fourCharts

def cubicResidualNetwork115 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xy), (.xx, .xy), (.xy, .xx), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork115_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork115.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork115, CodedBimolNetwork.toNetwork,
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
      at heq0 heq1 hdet hfold hc0 hc1
  case false.false =>
    have g0 : -(v 4) + v 3 + -(v 2) + v 1 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g1 : v 4 + -(v 3) + v 2 = 0 := by
      nlinarith [heq1]
    have g3 : (-2 : ℝ) * (v 0 * (v 4) ^ 3) + (6 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (-6 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (2 : ℝ) * (v 0 * (v 3) ^ 3) + (-2 : ℝ) * (v 0 * v 2 * (v 4) ^ 2) + (4 : ℝ) * (v 0 * v 2 * v 3 * v 4) + (-2 : ℝ) * (v 0 * v 2 * (v 3) ^ 2) + (2 : ℝ) * (v 0 * v 1 * (v 4) ^ 2) + (-4 : ℝ) * (v 0 * v 1 * v 3 * v 4) + (2 : ℝ) * (v 0 * v 1 * (v 3) ^ 2) + (2 : ℝ) * (v 0 * (v 1) ^ 2 * v 2) + (-2 : ℝ) * ((v 0) ^ 2 * (v 4) ^ 2) + (4 : ℝ) * ((v 0) ^ 2 * v 3 * v 4) + (-2 : ℝ) * ((v 0) ^ 2 * (v 3) ^ 2) + (2 : ℝ) * ((v 0) ^ 2 * v 1 * v 4) + (-2 : ℝ) * ((v 0) ^ 2 * v 1 * v 3) = 0 := by
      nlinarith [hfold]
    have g4 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + v 3 * h 1 + v 3 * h 0 + (-6 : ℝ) * (v 3 * (v 4) ^ 2) + (6 : ℝ) * ((v 3) ^ 2 * v 4) + (-2 : ℝ) * ((v 3) ^ 3) + (-2 : ℝ) * (v 2 * h 0) + (2 : ℝ) * (v 2 * (v 4) ^ 2) + (-4 : ℝ) * (v 2 * v 3 * v 4) + (2 : ℝ) * (v 2 * (v 3) ^ 2) + v 1 * h 1 + (-2 : ℝ) * (v 1 * (v 4) ^ 2) + (4 : ℝ) * (v 1 * v 3 * v 4) + (-2 : ℝ) * (v 1 * (v 3) ^ 2) + (-2 : ℝ) * ((v 1) ^ 2 * v 2) + -(v 0 * h 0) + (2 : ℝ) * (v 0 * (v 4) ^ 2) + (-4 : ℝ) * (v 0 * v 3 * v 4) + (2 : ℝ) * (v 0 * (v 3) ^ 2) + (-2 : ℝ) * (v 0 * v 1 * v 4) + (2 : ℝ) * (v 0 * v 1 * v 3) = 0 := by
      nlinarith [hc0]
    simp [-mul_eq_zero, cubicResidualNetwork115, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -(v 0 * (v 4) ^ 2 * h 1) + v 0 * (v 4) ^ 2 * h 0 + (2 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (-2 : ℝ) * (v 0 * v 3 * v 4 * h 0) + -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 + v 0 * v 1 * v 4 * h 1 + -(v 0 * v 1 * v 3 * h 1) + (2 : ℝ) * (v 0 * v 1 * v 2 * h 0) + (v 0) ^ 2 * v 4 * h 0 + -((v 0) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((-2 : ℝ) * (v 0 * v 4 * h 0) + (2 : ℝ) * (v 0 * v 3 * h 0)) * g0 +
      ((2 : ℝ) * (v 0 * v 1 * h 0)) * g1 +
      (v 4 + -(v 3)) * g3 +
      (v 0 * v 4 + -(v 0 * v 3)) * g4
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork115, CodedBimolNetwork.toNetwork,
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
      at hg0 hg1
    have g1 : v 4 + -(v 3) + (2 : ℝ) * (v 2) = 0 := by
      nlinarith [hg1]
    have g3 : v 4 + -(v 3) + v 2 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork115, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 3 * v 4 * h 0) + v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + -((v 1) ^ 2 * v 4 * h 1) + (v 1) ^ 2 * v 3 * h 1 + (-2 : ℝ) * ((v 1) ^ 2 * v 2 * h 0) + -(v 0 * v 1 * v 4 * h 0) + v 0 * v 1 * v 3 * h 0 = 0 := by
      linear_combination
        (-(v 1 * v 4 * h 1) + v 1 * v 4 * h 0 + v 1 * v 3 * h 1 + -(v 1 * v 3 * h 0) + (v 1) ^ 2 * h 1 + (-2 : ℝ) * ((v 1) ^ 2 * h 0) + v 0 * v 1 * h 0) * g1 +
      ((2 : ℝ) * (v 1 * v 4 * h 1) + (-2 : ℝ) * (v 1 * v 4 * h 0) + (-2 : ℝ) * (v 1 * v 3 * h 1) + (2 : ℝ) * (v 1 * v 3 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * h 1) + (2 : ℝ) * ((v 1) ^ 2 * h 0) + (-2 : ℝ) * (v 0 * v 1 * h 0)) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork115, CodedBimolNetwork.toNetwork,
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
      at hg0 hg1
    have g3 : v 4 + -(v 3) + v 2 = 0 := by
      nlinarith [heq1]
    have g5 : (-2 : ℝ) * (v 0 * (v 4) ^ 3) + (6 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (-6 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (2 : ℝ) * (v 0 * (v 3) ^ 3) + (-2 : ℝ) * (v 0 * v 2 * (v 4) ^ 2) + (4 : ℝ) * (v 0 * v 2 * v 3 * v 4) + (-2 : ℝ) * (v 0 * v 2 * (v 3) ^ 2) = 0 := by
      nlinarith [hfold]
    have g7 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + -(v 3 * h 1) + -(v 3 * h 0) + (6 : ℝ) * (v 3 * (v 4) ^ 2) + (-6 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + (2 : ℝ) * (v 2 * h 0) + (-2 : ℝ) * (v 2 * (v 4) ^ 2) + (4 : ℝ) * (v 2 * v 3 * v 4) + (-2 : ℝ) * (v 2 * (v 3) ^ 2) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork115, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 0 * (v 4) ^ 2 * h 1 + -(v 0 * (v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (2 : ℝ) * (v 0 * v 3 * v 4 * h 0) + v 0 * (v 3) ^ 2 * h 1 + -(v 0 * (v 3) ^ 2 * h 0) = 0 := by
      linear_combination
        (v 0 * v 4 * h 1 + -(v 0 * v 4 * h 0) + -(v 0 * v 3 * h 1) + v 0 * v 3 * h 0 + (2 : ℝ) * (v 0 * v 2 * h 0)) * g3 +
      (v 2) * g5 +
      (-(v 0 * v 2)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork115, CodedBimolNetwork.toNetwork,
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
      at hg0 hg1 hg2
    have g1 : -(v 4) + v 3 + v 1 = 0 := by
      nlinarith [hg1]
    have g2 : v 4 + -(v 3) + (2 : ℝ) * (v 2) = 0 := by
      nlinarith [hg2]
    have g4 : v 4 + -(v 3) + v 2 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork115, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + (2 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (-2 : ℝ) * (v 1 * v 3 * v 4 * h 0) + -(v 1 * (v 3) ^ 2 * h 1) + v 1 * (v 3) ^ 2 * h 0 = 0 := by
      linear_combination
        ((v 4) ^ 2 * h 0 + -((v 3) ^ 2 * h 0)) * g1 +
      (-((v 4) ^ 2 * h 0) + (v 3) ^ 2 * h 0 + v 1 * v 4 * h 1 + -(v 1 * v 3 * h 1) + (2 : ℝ) * (v 1 * v 3 * h 0)) * g2 +
      ((2 : ℝ) * ((v 4) ^ 2 * h 0) + (-2 : ℝ) * ((v 3) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 3 * h 1) + (-4 : ℝ) * (v 1 * v 3 * h 0)) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork115_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork115.toNetwork := by
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
  simp [cubicResidualNetwork115, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork115_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork115.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork115_jacobianNonzero
    cubicResidualNetwork115_fourCharts

end SmallCusp

import proofs.SmallCusp.Obstruction.CubicDegeneracy
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

def cubicResidualNetwork86 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xx, .xy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork86_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork86.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork86, CodedBimolNetwork.toNetwork,
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
    have g0 : (2 : ℝ) * (v 4) + -(v 3) + (2 : ℝ) * (v 2) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g1 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) + v 1 = 0 := by
      nlinarith [heq1]
    have g2 : (-2 : ℝ) * (v 2 * v 3) + (-4 : ℝ) * (v 1 * v 4) + (-2 : ℝ) * (v 1 * v 2) + (4 : ℝ) * (v 0 * v 4) + v 0 * v 2 = 0 := by
      nlinarith [hdet]
    have g3 : (-32 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (16 : ℝ) * (v 1 * (v 3) ^ 2 * v 4) + (-32 : ℝ) * (v 1 * v 2 * v 3 * v 4) + (-8 : ℝ) * (v 1 * (v 2) ^ 2 * v 3) + (32 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (-16 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (32 : ℝ) * (v 0 * v 2 * v 3 * v 4) + (8 : ℝ) * (v 0 * (v 2) ^ 2 * v 3) + (16 : ℝ) * (v 0 * v 1 * v 3 * v 4) + (-16 : ℝ) * ((v 0) ^ 2 * v 3 * v 4) + (4 : ℝ) * ((v 0) ^ 2 * v 1 * v 4) + (-4 : ℝ) * ((v 0) ^ 3 * v 4) = 0 := by
      nlinarith [hfold]
    have g4 : (4 : ℝ) * (v 4 * h 1) + (-2 : ℝ) * (v 3 * h 0) + (-32 : ℝ) * (v 3 * (v 4) ^ 2) + (16 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * (v 2 * h 1) + (-32 : ℝ) * (v 2 * v 3 * v 4) + (-8 : ℝ) * ((v 2) ^ 2 * v 3) + -(v 0 * h 0) + (16 : ℝ) * (v 0 * v 3 * v 4) + (4 : ℝ) * ((v 0) ^ 2 * v 4) = 0 := by
      nlinarith [hc0]
    have g5 : (-4 : ℝ) * (v 4 * h 1) + (2 : ℝ) * (v 3 * h 0) + (32 : ℝ) * (v 3 * (v 4) ^ 2) + (-16 : ℝ) * ((v 3) ^ 2 * v 4) + -(v 2 * h 1) + (32 : ℝ) * (v 2 * v 3 * v 4) + (8 : ℝ) * ((v 2) ^ 2 * v 3) + v 1 * h 0 + (-16 : ℝ) * (v 0 * v 3 * v 4) + (-4 : ℝ) * ((v 0) ^ 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork86, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (8 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 3 * v 4 * h 0) + (-4 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (-8 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (8 : ℝ) * (v 0 * v 3 * v 4 * h 0) + (4 : ℝ) * (v 0 * v 2 * v 3 * h 0) + (4 : ℝ) * (v 0 * v 1 * v 4 * h 1) + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) = 0 := by
      linear_combination
        ((16 : ℝ) * ((v 4) ^ 2 * h 1) + (-16 : ℝ) * ((v 4) ^ 2 * h 0) + (16 : ℝ) * (v 2 * v 4 * h 1) + (-8 : ℝ) * (v 2 * v 4 * h 0) + (-12 : ℝ) * (v 2 * v 3 * h 0) + (-12 : ℝ) * (v 1 * v 4 * h 1) + (4 : ℝ) * (v 1 * v 4 * h 0) + (-6 : ℝ) * (v 1 * v 2 * h 0) + (4 : ℝ) * (v 0 * v 3 * h 1) + (-3 : ℝ) * (v 0 * v 2 * h 1) + (4 : ℝ) * (v 0 * v 1 * h 1)) * g0 +
      ((16 : ℝ) * ((v 4) ^ 2 * h 1) + (-16 : ℝ) * ((v 4) ^ 2 * h 0) + (24 : ℝ) * (v 2 * v 4 * h 1) + (-16 : ℝ) * (v 2 * v 4 * h 0) + (-24 : ℝ) * (v 2 * v 3 * h 0) + (-4 : ℝ) * (v 1 * v 4 * h 1) + (-20 : ℝ) * (v 1 * v 4 * h 0) + (-2 : ℝ) * (v 1 * v 2 * h 1) + (-12 : ℝ) * (v 1 * v 2 * h 0) + (-8 : ℝ) * (v 0 * v 4 * h 1) + (24 : ℝ) * (v 0 * v 4 * h 0) + (4 : ℝ) * (v 0 * v 3 * h 1) + (-5 : ℝ) * (v 0 * v 2 * h 1) + (4 : ℝ) * ((v 0) ^ 2 * h 1)) * g1 +
      ((8 : ℝ) * (v 4 * h 0) + (-4 : ℝ) * (v 3 * h 0) + -(v 1 * h 1) + (-5 : ℝ) * (v 1 * h 0) + v 0 * h 1 + (32 : ℝ) * (v 3 * (v 4) ^ 2) + (-16 : ℝ) * ((v 3) ^ 2 * v 4) + (32 : ℝ) * (v 2 * v 3 * v 4) + (8 : ℝ) * ((v 2) ^ 2 * v 3) + (-16 : ℝ) * (v 0 * v 3 * v 4) + (-4 : ℝ) * ((v 0) ^ 2 * v 4)) * g2 +
      ((-4 : ℝ) * (v 4)) * g3 +
      ((-8 : ℝ) * (v 2 * v 4) + (2 : ℝ) * (v 2 * v 3)) * g4 +
      ((-8 : ℝ) * (v 2 * v 4) + (4 : ℝ) * (v 2 * v 3) + (2 : ℝ) * (v 1 * v 2) + -(v 0 * v 2)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork86, CodedBimolNetwork.toNetwork,
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
    have g1 : (2 : ℝ) * (v 3) + v 1 = 0 := by
      nlinarith [hg1]
    have g2 : (2 : ℝ) * (v 4) + -(v 3) + (2 : ℝ) * (v 2) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) + v 1 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork86, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (8 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (-8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (-4 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + (4 : ℝ) * (v 0 * v 2 * v 4 * h 1) = 0 := by
      linear_combination
        ((-4 : ℝ) * ((v 3) ^ 2 * h 0) + (-4 : ℝ) * (v 2 * v 4 * h 1) + (4 : ℝ) * (v 2 * v 4 * h 0) + (2 : ℝ) * (v 2 * v 3 * h 0) + (2 : ℝ) * ((v 2) ^ 2 * h 0) + (2 : ℝ) * (v 0 * v 3 * h 0) + v 0 * v 1 * h 0) * g0 +
      ((-4 : ℝ) * ((v 3) ^ 2 * h 0) + (2 : ℝ) * (v 2 * v 3 * h 0) + (2 : ℝ) * (v 1 * v 3 * h 0) + -(v 1 * v 2 * h 0) + -((v 1) ^ 2 * h 0) + (2 : ℝ) * (v 0 * v 2 * h 0) + v 0 * v 1 * h 0 + (v 0) ^ 2 * h 0) * g1 +
      ((v 1) ^ 2 * h 0) * g2 +
      ((v 1) ^ 2 * h 0 + (-2 : ℝ) * (v 0 * v 2 * h 0)) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork86, CodedBimolNetwork.toNetwork,
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
    have g1 : (4 : ℝ) * (v 4) + (2 : ℝ) * (v 2) = 0 := by
      nlinarith [hg1]
    have g2 : (2 : ℝ) * (v 4) + -(v 3) + (2 : ℝ) * (v 2) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) + v 1 = 0 := by
      nlinarith [heq1]
    have g6 : (4 : ℝ) * (v 4 * h 1) + (-2 : ℝ) * (v 3 * h 0) + (-32 : ℝ) * (v 3 * (v 4) ^ 2) + (16 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * (v 2 * h 1) + (-16 : ℝ) * (v 2 * v 3 * v 4) + (-2 : ℝ) * ((v 2) ^ 2 * v 3) + (16 : ℝ) * (v 1 * v 3 * v 4) + (4 : ℝ) * ((v 1) ^ 2 * v 4) + -(v 0 * h 0) = 0 := by
      nlinarith [hc0]
    have g7 : (-4 : ℝ) * (v 4 * h 1) + (2 : ℝ) * (v 3 * h 0) + (32 : ℝ) * (v 3 * (v 4) ^ 2) + (-16 : ℝ) * ((v 3) ^ 2 * v 4) + -(v 2 * h 1) + (16 : ℝ) * (v 2 * v 3 * v 4) + (2 : ℝ) * ((v 2) ^ 2 * v 3) + v 1 * h 0 + (-16 : ℝ) * (v 1 * v 3 * v 4) + (-4 : ℝ) * ((v 1) ^ 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork86, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (-8 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (8 : ℝ) * (v 1 * v 3 * v 4 * h 0) + (2 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (-4 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (8 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (-8 : ℝ) * (v 0 * v 3 * v 4 * h 0) + (-2 : ℝ) * (v 0 * v 2 * v 3 * h 0) + (4 : ℝ) * (v 0 * v 1 * v 4 * h 1) = 0 := by
      linear_combination
        ((-8 : ℝ) * ((v 3) ^ 2 * h 1) + (4 : ℝ) * ((v 3) ^ 2 * h 0) + (4 : ℝ) * (v 2 * v 3 * h 1) + (-2 : ℝ) * (v 2 * v 3 * h 0) + (-9 : ℝ) * (v 1 * v 3 * h 1) + (3 : ℝ) * (v 1 * v 3 * h 0) + (2 : ℝ) * (v 1 * v 2 * h 1) + v 1 * v 2 * h 0 + -((v 1) ^ 2 * h 1) + (4 : ℝ) * (v 0 * v 4 * h 0) + (2 : ℝ) * (v 0 * v 2 * h 0) + -(v 0 * v 1 * h 0)) * g0 +
      ((-8 : ℝ) * ((v 3) ^ 2 * h 1) + (4 : ℝ) * ((v 3) ^ 2 * h 0) + (-7 : ℝ) * (v 1 * v 3 * h 1) + (3 : ℝ) * (v 1 * v 3 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * h 1) + (2 : ℝ) * (v 0 * v 3 * h 1) + ((3 : ℝ) / 2) * (v 0 * v 1 * h 1) + ((-1 : ℝ) / 2) * (v 0 * v 1 * h 0) + (v 0) ^ 2 * h 0) * g1 +
      ((8 : ℝ) * ((v 3) ^ 2 * h 1) + (-4 : ℝ) * ((v 3) ^ 2 * h 0) + (10 : ℝ) * (v 1 * v 3 * h 1) + (2 : ℝ) * ((v 1) ^ 2 * h 1) + v 0 * v 1 * h 0) * g2 +
      ((-8 : ℝ) * ((v 3) ^ 2 * h 1) + (4 : ℝ) * ((v 3) ^ 2 * h 0) + (2 : ℝ) * (v 1 * v 3 * h 0) + v 0 * v 1 * h 1) * g3 +
      ((-2 : ℝ) * (v 1 * v 3)) * g6 +
      ((-2 : ℝ) * (v 1 * v 3)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork86, CodedBimolNetwork.toNetwork,
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
    have g0 : (-2 : ℝ) * (v 3) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : (4 : ℝ) * (v 4) + (2 : ℝ) * (v 2) = 0 := by
      nlinarith [hg1]
    have g2 : (2 : ℝ) * (v 3) + v 1 = 0 := by
      nlinarith [hg2]
    have g3 : (2 : ℝ) * (v 4) + -(v 3) + (2 : ℝ) * (v 2) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g4 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) + v 1 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork86, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (-8 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (2 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + (-4 : ℝ) * (v 1 * v 2 * v 4 * h 1) = 0 := by
      linear_combination
        ((4 : ℝ) * ((v 4) ^ 2 * h 0) + -((v 2) ^ 2 * h 0)) * g0 +
      ((-4 : ℝ) * (v 3 * v 4 * h 1) + (-2 : ℝ) * (v 1 * v 4 * h 1) + ((1 : ℝ) / 2) * (v 1 * v 3 * h 0) + -(v 1 * v 2 * h 0) + v 0 * v 4 * h 0 + ((1 : ℝ) / 2) * (v 0 * v 2 * h 0)) * g1 +
      ((8 : ℝ) * ((v 4) ^ 2 * h 1) + (2 : ℝ) * (v 3 * v 4 * h 0) + (2 : ℝ) * (v 2 * v 4 * h 0) + -(v 0 * v 2 * h 0)) * g2 +
      (v 1 * v 2 * h 0) * g3 +
      ((-4 : ℝ) * (v 3 * v 4 * h 0) + (2 : ℝ) * (v 0 * v 2 * h 0)) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork86_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork86.toNetwork := by
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
  simp [cubicResidualNetwork86, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork86_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork86.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork86_jacobianNonzero
    cubicResidualNetwork86_fourCharts

def cubicResidualNetwork87 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.xx, .xy), (.xy, .xx), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork87_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork87.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork87, CodedBimolNetwork.toNetwork,
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
    have g0 : (2 : ℝ) * (v 4) + v 3 + -(v 2) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g1 : (-2 : ℝ) * (v 4) + -(v 3) + v 2 + v 1 = 0 := by
      nlinarith [heq1]
    have g2 : (-4 : ℝ) * (v 1 * v 4) + -(v 1 * v 3) + (4 : ℝ) * (v 0 * v 4) + v 0 * v 3 = 0 := by
      nlinarith [hdet]
    simp [-mul_eq_zero, cubicResidualNetwork87, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + (8 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 + (-8 : ℝ) * (v 0 * v 2 * v 4 * h 1) + (8 : ℝ) * (v 0 * v 2 * v 4 * h 0) + (4 : ℝ) * (v 0 * v 1 * v 4 * h 1) + v 0 * v 1 * v 3 * h 0 + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) + -((v 0) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((-4 : ℝ) * ((v 4) ^ 2 * h 0) + (-6 : ℝ) * (v 2 * v 4 * h 0) + -(v 2 * v 3 * h 0) + (-4 : ℝ) * (v 1 * v 4 * h 1) + v 1 * v 3 * h 1 + ((-3 : ℝ) / 2) * (v 1 * v 3 * h 0) + (4 : ℝ) * (v 0 * v 4 * h 1) + v 0 * v 3 * h 0) * g0 +
      ((-4 : ℝ) * ((v 4) ^ 2 * h 0) + (-6 : ℝ) * (v 2 * v 4 * h 0) + -(v 2 * v 3 * h 0) + (-2 : ℝ) * (v 1 * v 4 * h 0) + ((-1 : ℝ) / 2) * (v 1 * v 3 * h 0) + (2 : ℝ) * (v 0 * v 4 * h 0) + v 0 * v 3 * h 1) * g1 +
      ((-2 : ℝ) * (v 4 * h 1) + -(v 2 * h 1) + ((-1 : ℝ) / 2) * (v 1 * h 0)) * g2
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork87, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork87, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two] <;> ring
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork87, CodedBimolNetwork.toNetwork,
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
    have g0 : v 3 + (-2 : ℝ) * (v 2) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : (4 : ℝ) * (v 4) + v 3 = 0 := by
      nlinarith [hg1]
    have g2 : (2 : ℝ) * (v 4) + v 3 + -(v 2) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : (-2 : ℝ) * (v 4) + -(v 3) + v 2 + v 1 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork87, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -(v 1 * (v 3) ^ 2 * h 1) + v 1 * (v 3) ^ 2 * h 0 + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (-4 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + -((v 1) ^ 2 * v 3 * h 0) + v 0 * (v 3) ^ 2 * h 1 + -(v 0 * (v 3) ^ 2 * h 0) + (8 : ℝ) * (v 0 * v 2 * v 4 * h 1) + (-8 : ℝ) * (v 0 * v 2 * v 4 * h 0) + (4 : ℝ) * (v 0 * v 1 * v 4 * h 1) + v 0 * v 1 * v 3 * h 0 = 0 := by
      linear_combination
        ((-8 : ℝ) * (v 1 * v 4 * h 0) + -(v 1 * v 3 * h 1) + (2 : ℝ) * (v 1 * v 2 * h 1) + (2 : ℝ) * ((v 1) ^ 2 * h 1) + (8 : ℝ) * (v 0 * v 4 * h 0)) * g0 +
      ((-4 : ℝ) * (v 1 * v 4 * h 0) + v 1 * v 3 * h 0 + -((v 1) ^ 2 * h 0) + (4 : ℝ) * (v 0 * v 4 * h 1) + (4 : ℝ) * (v 0 * v 4 * h 0) + v 0 * v 3 * h 1 + -(v 0 * v 3 * h 0) + -(v 0 * v 1 * h 1) + v 0 * v 1 * h 0) * g1 +
      ((12 : ℝ) * (v 1 * v 4 * h 0) + (-2 : ℝ) * (v 1 * v 2 * h 1) + (-2 : ℝ) * ((v 1) ^ 2 * h 1) + (-8 : ℝ) * (v 0 * v 4 * h 0)) * g2 +
      ((4 : ℝ) * (v 1 * v 4 * h 0) + (2 : ℝ) * (v 1 * v 2 * h 1) + (8 : ℝ) * (v 0 * v 4 * h 1)) * g3
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork87, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork87, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two] <;> ring

theorem cubicResidualNetwork87_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork87.toNetwork := by
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
  simp [cubicResidualNetwork87, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork87_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork87.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork87_jacobianNonzero
    cubicResidualNetwork87_fourCharts

def cubicResidualNetwork88 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.xx, .xy), (.xy, .yy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork88_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork88.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork88, CodedBimolNetwork.toNetwork,
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
    have g0 : (2 : ℝ) * (v 4) + -(v 3) + -(v 2) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g1 : (-2 : ℝ) * (v 4) + v 3 + v 2 + v 1 = 0 := by
      nlinarith [heq1]
    have g2 : (-4 : ℝ) * (v 1 * v 4) + v 1 * v 3 + (4 : ℝ) * (v 0 * v 4) + -(v 0 * v 3) = 0 := by
      nlinarith [hdet]
    simp [-mul_eq_zero, cubicResidualNetwork88, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + (8 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 + (-8 : ℝ) * (v 0 * v 2 * v 4 * h 1) + (8 : ℝ) * (v 0 * v 2 * v 4 * h 0) + (4 : ℝ) * (v 0 * v 1 * v 4 * h 1) + -(v 0 * v 1 * v 3 * h 0) + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) + (v 0) ^ 2 * v 3 * h 0 = 0 := by
      linear_combination
        ((16 : ℝ) * ((v 4) ^ 2 * h 1) + -((v 3) ^ 2 * h 0) + (8 : ℝ) * (v 2 * v 4 * h 1) + (-8 : ℝ) * (v 2 * v 4 * h 0) + v 0 * v 3 * h 1 + -(v 0 * v 3 * h 0)) * g0 +
      ((16 : ℝ) * ((v 4) ^ 2 * h 1) + -((v 3) ^ 2 * h 0) + (8 : ℝ) * (v 2 * v 4 * h 1) + (-8 : ℝ) * (v 2 * v 4 * h 0) + v 0 * v 3 * h 1 + -(v 0 * v 3 * h 0)) * g1 +
      ((4 : ℝ) * (v 4 * h 1) + v 3 * h 1 + -(v 0 * h 1)) * g2
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork88, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork88, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two] <;> ring
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork88, CodedBimolNetwork.toNetwork,
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
    have g0 : -(v 3) + (-2 : ℝ) * (v 2) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : (4 : ℝ) * (v 4) + -(v 3) = 0 := by
      nlinarith [hg1]
    have g2 : (2 : ℝ) * (v 4) + -(v 3) + -(v 2) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : (-2 : ℝ) * (v 4) + v 3 + v 2 + v 1 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork88, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -(v 1 * (v 3) ^ 2 * h 1) + v 1 * (v 3) ^ 2 * h 0 + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (-4 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (v 1) ^ 2 * v 3 * h 0 + v 0 * (v 3) ^ 2 * h 1 + -(v 0 * (v 3) ^ 2 * h 0) + (8 : ℝ) * (v 0 * v 2 * v 4 * h 1) + (-8 : ℝ) * (v 0 * v 2 * v 4 * h 0) + (4 : ℝ) * (v 0 * v 1 * v 4 * h 1) + -(v 0 * v 1 * v 3 * h 0) = 0 := by
      linear_combination
        ((-8 : ℝ) * (v 1 * v 4 * h 0) + v 1 * v 3 * h 1 + (2 : ℝ) * (v 1 * v 2 * h 1) + (2 : ℝ) * ((v 1) ^ 2 * h 1) + (8 : ℝ) * (v 0 * v 4 * h 0)) * g0 +
      ((-4 : ℝ) * (v 1 * v 4 * h 0) + -(v 1 * v 3 * h 0) + -((v 1) ^ 2 * h 0) + (4 : ℝ) * (v 0 * v 4 * h 0) + v 0 * v 3 * h 1 + v 0 * v 3 * h 0 + (2 : ℝ) * (v 0 * v 2 * h 1) + v 0 * v 1 * h 1 + v 0 * v 1 * h 0) * g1 +
      ((12 : ℝ) * (v 1 * v 4 * h 0) + (-2 : ℝ) * (v 1 * v 2 * h 1) + (-2 : ℝ) * ((v 1) ^ 2 * h 1) + (-8 : ℝ) * (v 0 * v 4 * h 0)) * g2 +
      ((4 : ℝ) * (v 1 * v 4 * h 0) + (2 : ℝ) * (v 1 * v 2 * h 1) + (2 : ℝ) * (v 0 * v 3 * h 1)) * g3
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork88, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork88, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two] <;> ring

theorem cubicResidualNetwork88_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork88.toNetwork := by
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
  simp [cubicResidualNetwork88, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork88_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork88.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork88_jacobianNonzero
    cubicResidualNetwork88_fourCharts

def cubicResidualNetwork89 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xy, .xx), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork89_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork89.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork89, CodedBimolNetwork.toNetwork,
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
    have g0 : (2 : ℝ) * (v 4) + v 3 + v 2 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g1 : (-2 : ℝ) * (v 4) + -(v 3) + -(v 2) + v 1 = 0 := by
      nlinarith [heq1]
    have g2 : (-4 : ℝ) * (v 1 * v 4) + -(v 1 * v 3) + -(v 1 * v 2) + (4 : ℝ) * (v 0 * v 4) + v 0 * v 3 + v 0 * v 2 = 0 := by
      nlinarith [hdet]
    simp [-mul_eq_zero, cubicResidualNetwork89, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + v 1 * v 2 * v 3 * h 1 + -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 + -(v 0 * v 2 * v 3 * h 1) + (4 : ℝ) * (v 0 * v 1 * v 4 * h 1) + v 0 * v 1 * v 3 * h 0 + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) + -((v 0) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((-8 : ℝ) * ((v 4) ^ 2 * h 1) + (-8 : ℝ) * (v 3 * v 4 * h 1) + (2 : ℝ) * (v 3 * v 4 * h 0) + v 2 * v 3 * h 0 + -(v 1 * v 3 * h 0) + (2 : ℝ) * (v 1 * v 2 * h 1) + (-2 : ℝ) * ((v 1) ^ 2 * h 1) + (4 : ℝ) * (v 0 * v 4 * h 1) + v 0 * v 3 * h 0) * g0 +
      ((-8 : ℝ) * ((v 4) ^ 2 * h 1) + (-8 : ℝ) * (v 3 * v 4 * h 1) + (2 : ℝ) * (v 3 * v 4 * h 0) + v 2 * v 3 * h 0 + (4 : ℝ) * (v 1 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 3 * h 1) + (2 : ℝ) * (v 1 * v 2 * h 1) + (-2 : ℝ) * (v 0 * v 3 * h 1) + (-2 : ℝ) * (v 0 * v 1 * h 1)) * g1 +
      ((-4 : ℝ) * (v 4 * h 1) + (-3 : ℝ) * (v 3 * h 1)) * g2
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork89, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork89, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two] <;> ring
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork89, CodedBimolNetwork.toNetwork,
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
    have g0 : v 3 + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : (4 : ℝ) * (v 4) + v 3 + v 2 = 0 := by
      nlinarith [hg1]
    have g2 : (2 : ℝ) * (v 4) + v 3 + v 2 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : (-2 : ℝ) * (v 4) + -(v 3) + -(v 2) + v 1 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork89, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -(v 1 * (v 3) ^ 2 * h 1) + v 1 * (v 3) ^ 2 * h 0 + -(v 1 * v 2 * v 3 * h 1) + (-4 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + -((v 1) ^ 2 * v 3 * h 0) + v 0 * (v 3) ^ 2 * h 1 + -(v 0 * (v 3) ^ 2 * h 0) + v 0 * v 2 * v 3 * h 1 + (4 : ℝ) * (v 0 * v 1 * v 4 * h 1) + v 0 * v 1 * v 3 * h 0 = 0 := by
      linear_combination
        ((-2 : ℝ) * (v 3 * v 4 * h 0) + -((v 3) ^ 2 * h 0) + -(v 2 * v 3 * h 0) + (2 : ℝ) * (v 1 * v 4 * h 0) + v 1 * v 3 * h 1 + (2 : ℝ) * (v 1 * v 3 * h 0) + v 1 * v 2 * h 1 + v 1 * v 2 * h 0 + (-2 : ℝ) * ((v 1) ^ 2 * h 1) + -((v 1) ^ 2 * h 0) + (-2 : ℝ) * (v 0 * v 4 * h 0) + -(v 0 * v 3 * h 0) + -(v 0 * v 2 * h 0) + v 0 * v 1 * h 0) * g0 +
      ((-4 : ℝ) * (v 1 * v 4 * h 1) + (-2 : ℝ) * (v 1 * v 2 * h 1) + (-2 : ℝ) * ((v 1) ^ 2 * h 1) + -(v 0 * v 3 * h 1) + (3 : ℝ) * (v 0 * v 1 * h 1)) * g1 +
      ((v 3) ^ 2 * h 0 + (8 : ℝ) * (v 1 * v 4 * h 1) + -(v 1 * v 3 * h 0) + (2 : ℝ) * (v 1 * v 2 * h 1) + (2 : ℝ) * ((v 1) ^ 2 * h 1)) * g2 +
      ((2 : ℝ) * (v 1 * v 3 * h 1) + (-2 : ℝ) * (v 0 * v 3 * h 1) + -(v 0 * v 1 * h 0) + (v 0) ^ 2 * h 0) * g3
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork89, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork89, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two] <;> ring

theorem cubicResidualNetwork89_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork89.toNetwork := by
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
  simp [cubicResidualNetwork89, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork89_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork89.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork89_jacobianNonzero
    cubicResidualNetwork89_fourCharts

def cubicResidualNetwork90 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xy, .yy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork90_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork90.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork90, CodedBimolNetwork.toNetwork,
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
    have g0 : (2 : ℝ) * (v 4) + -(v 3) + v 2 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g1 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) + v 1 = 0 := by
      nlinarith [heq1]
    have g2 : (-4 : ℝ) * (v 1 * v 4) + v 1 * v 3 + -(v 1 * v 2) + (4 : ℝ) * (v 0 * v 4) + -(v 0 * v 3) + v 0 * v 2 = 0 := by
      nlinarith [hdet]
    simp [-mul_eq_zero, cubicResidualNetwork90, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + -(v 1 * v 2 * v 3 * h 1) + -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 + v 0 * v 2 * v 3 * h 1 + (4 : ℝ) * (v 0 * v 1 * v 4 * h 1) + -(v 0 * v 1 * v 3 * h 0) + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) + (v 0) ^ 2 * v 3 * h 0 = 0 := by
      linear_combination
        ((-4 : ℝ) * ((v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 2 * v 4 * h 0) + -((v 2) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 3 * h 1) + (2 : ℝ) * (v 1 * v 3 * h 0) + (v 1) ^ 2 * h 0 + (-4 : ℝ) * (v 0 * v 4 * h 0) + (2 : ℝ) * (v 0 * v 3 * h 1) + (-2 : ℝ) * (v 0 * v 2 * h 1) + -(v 0 * v 2 * h 0) + (2 : ℝ) * (v 0 * v 1 * h 1)) * g0 +
      ((-4 : ℝ) * ((v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 2 * v 4 * h 0) + -((v 2) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 4 * h 0) + v 1 * v 3 * h 0 + -(v 1 * v 2 * h 0) + (-2 : ℝ) * (v 0 * v 4 * h 0) + v 0 * v 3 * h 0 + (-2 : ℝ) * (v 0 * v 2 * h 1) + v 0 * v 1 * h 0 + (2 : ℝ) * ((v 0) ^ 2 * h 1)) * g1 +
      (-(v 3 * h 1) + -(v 0 * h 0)) * g2
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork90, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork90, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two] <;> ring
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork90, CodedBimolNetwork.toNetwork,
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
    have g0 : -(v 3) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : (4 : ℝ) * (v 4) + -(v 3) + v 2 = 0 := by
      nlinarith [hg1]
    have g2 : (2 : ℝ) * (v 4) + -(v 3) + v 2 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) + v 1 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork90, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -(v 1 * (v 3) ^ 2 * h 1) + v 1 * (v 3) ^ 2 * h 0 + v 1 * v 2 * v 3 * h 1 + (-4 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (v 1) ^ 2 * v 3 * h 0 + v 0 * (v 3) ^ 2 * h 1 + -(v 0 * (v 3) ^ 2 * h 0) + -(v 0 * v 2 * v 3 * h 1) + (4 : ℝ) * (v 0 * v 1 * v 4 * h 1) + -(v 0 * v 1 * v 3 * h 0) = 0 := by
      linear_combination
        ((2 : ℝ) * (v 3 * v 4 * h 0) + -((v 3) ^ 2 * h 0) + v 2 * v 3 * h 0 + (-4 : ℝ) * (v 1 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 4 * h 0) + (-2 : ℝ) * (v 1 * v 3 * h 0) + v 1 * v 2 * h 0 + (-2 : ℝ) * ((v 1) ^ 2 * h 1) + -((v 1) ^ 2 * h 0) + (-2 : ℝ) * (v 0 * v 4 * h 0) + v 0 * v 3 * h 0 + -(v 0 * v 2 * h 0) + v 0 * v 1 * h 0) * g0 +
      ((-3 : ℝ) * (v 1 * v 3 * h 1) + (-2 : ℝ) * ((v 1) ^ 2 * h 1) + v 0 * v 3 * h 1) * g1 +
      ((v 3) ^ 2 * h 0 + (2 : ℝ) * (v 1 * v 3 * h 1) + v 1 * v 3 * h 0 + (2 : ℝ) * ((v 1) ^ 2 * h 1)) * g2 +
      ((-2 : ℝ) * (v 1 * v 3 * h 1) + (2 : ℝ) * (v 0 * v 3 * h 1) + -(v 0 * v 1 * h 0) + (v 0) ^ 2 * h 0) * g3
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork90, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork90, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two] <;> ring

theorem cubicResidualNetwork90_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork90.toNetwork := by
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
  simp [cubicResidualNetwork90, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork90_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork90.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork90_jacobianNonzero
    cubicResidualNetwork90_fourCharts

def cubicResidualNetwork91 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xy, .yy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork91_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork91.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork91, CodedBimolNetwork.toNetwork,
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
    have g0 : (2 : ℝ) * (v 4) + -(v 3) + (2 : ℝ) * (v 2) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g1 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) + v 1 = 0 := by
      nlinarith [heq1]
    have g2 : -(v 2 * v 3) + (-4 : ℝ) * (v 1 * v 4) + v 1 * v 3 + (-2 : ℝ) * (v 1 * v 2) + (4 : ℝ) * (v 0 * v 4) + -(v 0 * v 3) + v 0 * v 2 = 0 := by
      nlinarith [hdet]
    have g3 : (-4 : ℝ) * (v 1 * (v 3) ^ 2 * v 4) + (2 : ℝ) * (v 1 * (v 3) ^ 3) + (-4 : ℝ) * (v 1 * v 2 * (v 3) ^ 2) + (4 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (-2 : ℝ) * (v 0 * (v 3) ^ 3) + (4 : ℝ) * (v 0 * v 2 * (v 3) ^ 2) + (2 : ℝ) * (v 0 * v 1 * (v 3) ^ 2) + (-4 : ℝ) * (v 0 * v 1 * v 2 * v 3) + (-2 : ℝ) * ((v 0) ^ 2 * (v 3) ^ 2) + (4 : ℝ) * ((v 0) ^ 2 * v 2 * v 3) + (4 : ℝ) * ((v 0) ^ 2 * v 1 * v 4) + (-4 : ℝ) * ((v 0) ^ 3 * v 4) = 0 := by
      nlinarith [hfold]
    have g4 : (4 : ℝ) * (v 4 * h 1) + -(v 3 * h 1) + -(v 3 * h 0) + (-4 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + (2 : ℝ) * (v 2 * h 1) + (-4 : ℝ) * (v 2 * (v 3) ^ 2) + -(v 0 * h 0) + (2 : ℝ) * (v 0 * (v 3) ^ 2) + (-4 : ℝ) * (v 0 * v 2 * v 3) + (4 : ℝ) * ((v 0) ^ 2 * v 4) = 0 := by
      nlinarith [hc0]
    have g5 : (-4 : ℝ) * (v 4 * h 1) + v 3 * h 1 + v 3 * h 0 + (4 : ℝ) * ((v 3) ^ 2 * v 4) + (-2 : ℝ) * ((v 3) ^ 3) + -(v 2 * h 1) + (4 : ℝ) * (v 2 * (v 3) ^ 2) + v 1 * h 0 + (-2 : ℝ) * (v 0 * (v 3) ^ 2) + (4 : ℝ) * (v 0 * v 2 * v 3) + (-4 : ℝ) * ((v 0) ^ 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork91, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 2 * v 3 * h 1) + -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 + (2 : ℝ) * (v 0 * v 2 * v 3 * h 1) + (4 : ℝ) * (v 0 * v 1 * v 4 * h 1) + -(v 0 * v 1 * v 3 * h 0) + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) + (v 0) ^ 2 * v 3 * h 0 = 0 := by
      linear_combination
        ((8 : ℝ) * ((v 4) ^ 2 * h 1) + (-4 : ℝ) * (v 3 * v 4 * h 0) + (2 : ℝ) * (v 2 * v 4 * h 1) + -(v 2 * v 3 * h 0) + -((v 2) ^ 2 * h 1) + (-4 : ℝ) * (v 1 * v 4 * h 1) + -(v 1 * v 2 * h 1) + (4 : ℝ) * (v 0 * v 4 * h 1) + (-4 : ℝ) * (v 0 * v 4 * h 0) + -(v 0 * v 2 * h 0)) * g0 +
      ((8 : ℝ) * ((v 4) ^ 2 * h 1) + (-4 : ℝ) * (v 3 * v 4 * h 0) + (6 : ℝ) * (v 2 * v 4 * h 1) + (-3 : ℝ) * (v 2 * v 3 * h 0) + (-4 : ℝ) * (v 0 * v 4 * h 0) + -(v 0 * v 2 * h 1) + (-3 : ℝ) * (v 0 * v 2 * h 0)) * g1 +
      (v 3 * h 1 + -(v 3 * h 0) + -(v 2 * h 1) + v 2 * h 0 + -(v 0 * h 0) + (4 : ℝ) * ((v 3) ^ 2 * v 4) + (-2 : ℝ) * ((v 3) ^ 3) + (4 : ℝ) * (v 2 * (v 3) ^ 2) + (-2 : ℝ) * (v 0 * (v 3) ^ 2) + (4 : ℝ) * (v 0 * v 2 * v 3) + (-4 : ℝ) * ((v 0) ^ 2 * v 4)) * g2 +
      ((-4 : ℝ) * (v 4) + v 3 + (-2 : ℝ) * (v 2)) * g3 +
      ((4 : ℝ) * (v 2 * v 4) + -(v 2 * v 3) + (2 : ℝ) * ((v 2) ^ 2)) * g4 +
      ((4 : ℝ) * (v 2 * v 4) + (2 : ℝ) * ((v 2) ^ 2) + v 0 * v 2) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork91, CodedBimolNetwork.toNetwork,
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
    have g0 : -(v 3) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : v 3 + v 1 = 0 := by
      nlinarith [hg1]
    have g2 : (2 : ℝ) * (v 4) + -(v 3) + (2 : ℝ) * (v 2) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) + v 1 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork91, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 2 * (v 3) ^ 2 * h 1 + -(v 2 * (v 3) ^ 2 * h 0) + (-2 : ℝ) * ((v 2) ^ 2 * v 3 * h 1) + (4 : ℝ) * (v 0 * v 2 * v 4 * h 1) + -(v 0 * v 2 * v 3 * h 0) = 0 := by
      linear_combination
        (-((v 3) ^ 2 * h 1) + -(v 2 * v 3 * h 1) + (2 : ℝ) * ((v 2) ^ 2 * h 1) + -(v 1 * v 2 * h 1) + -(v 1 * v 2 * h 0)) * g0 +
      (-((v 3) ^ 2 * h 1) + -(v 2 * v 3 * h 0) + v 1 * v 3 * h 1 + -(v 1 * v 2 * h 1) + -((v 1) ^ 2 * h 1) + -(v 0 * v 3 * h 1) + v 0 * v 2 * h 1 + -(v 0 * v 2 * h 0) + v 0 * v 1 * h 1) * g1 +
      ((v 1) ^ 2 * h 1) * g2 +
      ((v 1) ^ 2 * h 1 + (-2 : ℝ) * (v 0 * v 2 * h 1)) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork91, CodedBimolNetwork.toNetwork,
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
    have g0 : -(v 3) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : (4 : ℝ) * (v 4) + -(v 3) + (2 : ℝ) * (v 2) = 0 := by
      nlinarith [hg1]
    have g2 : (2 : ℝ) * (v 4) + -(v 3) + (2 : ℝ) * (v 2) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) + v 1 = 0 := by
      nlinarith [heq1]
    have g5 : (-4 : ℝ) * (v 1 * (v 3) ^ 2 * v 4) + (2 : ℝ) * (v 1 * (v 3) ^ 3) + (-2 : ℝ) * (v 1 * v 2 * (v 3) ^ 2) + (2 : ℝ) * ((v 1) ^ 2 * (v 3) ^ 2) + (-2 : ℝ) * ((v 1) ^ 2 * v 2 * v 3) + (4 : ℝ) * ((v 1) ^ 3 * v 4) + (4 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (-2 : ℝ) * (v 0 * (v 3) ^ 3) + (2 : ℝ) * (v 0 * v 2 * (v 3) ^ 2) + (-2 : ℝ) * (v 0 * v 1 * (v 3) ^ 2) + (2 : ℝ) * (v 0 * v 1 * v 2 * v 3) + (-4 : ℝ) * (v 0 * (v 1) ^ 2 * v 4) = 0 := by
      nlinarith [hfold]
    have g7 : (-4 : ℝ) * (v 4 * h 1) + v 3 * h 1 + v 3 * h 0 + (4 : ℝ) * ((v 3) ^ 2 * v 4) + (-2 : ℝ) * ((v 3) ^ 3) + -(v 2 * h 1) + (2 : ℝ) * (v 2 * (v 3) ^ 2) + v 1 * h 0 + (-2 : ℝ) * (v 1 * (v 3) ^ 2) + (2 : ℝ) * (v 1 * v 2 * v 3) + (-4 : ℝ) * ((v 1) ^ 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork91, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -(v 1 * (v 3) ^ 2 * h 1) + v 1 * (v 3) ^ 2 * h 0 + v 1 * v 2 * v 3 * h 1 + (-4 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (v 1) ^ 2 * v 3 * h 0 + v 0 * (v 3) ^ 2 * h 1 + -(v 0 * (v 3) ^ 2 * h 0) + -(v 0 * v 2 * v 3 * h 1) + (4 : ℝ) * (v 0 * v 1 * v 4 * h 1) + -(v 0 * v 1 * v 3 * h 0) = 0 := by
      linear_combination
        (-(v 1 * v 3 * h 1) + -(v 1 * v 3 * h 0) + v 1 * v 2 * h 1 + (-2 : ℝ) * ((v 1) ^ 2 * h 1) + -((v 1) ^ 2 * h 0) + (-4 : ℝ) * (v 0 * v 4 * h 1) + v 0 * v 3 * h 1 + v 0 * v 3 * h 0 + -(v 0 * v 2 * h 1) + v 0 * v 1 * h 0) * g0 +
      ((-2 : ℝ) * (v 1 * v 3 * h 1) + (-2 : ℝ) * ((v 1) ^ 2 * h 1)) * g1 +
      ((2 : ℝ) * (v 1 * v 3 * h 1) + (2 : ℝ) * ((v 1) ^ 2 * h 1)) * g2 +
      ((-2 : ℝ) * (v 1 * v 3 * h 1) + (2 : ℝ) * (v 0 * v 3 * h 1)) * g3 +
      (-(v 0)) * g5 +
      (-(v 0 * v 1) + (v 0) ^ 2) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork91, CodedBimolNetwork.toNetwork,
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
    have g0 : -(v 3) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : (4 : ℝ) * (v 4) + -(v 3) + (2 : ℝ) * (v 2) = 0 := by
      nlinarith [hg1]
    have g2 : v 3 + v 1 = 0 := by
      nlinarith [hg2]
    have g3 : (2 : ℝ) * (v 4) + -(v 3) + (2 : ℝ) * (v 2) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g4 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) + v 1 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork91, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -(v 2 * (v 3) ^ 2 * h 1) + v 2 * (v 3) ^ 2 * h 0 + (v 2) ^ 2 * v 3 * h 1 + (-4 : ℝ) * (v 1 * v 2 * v 4 * h 1) + v 1 * v 2 * v 3 * h 0 = 0 := by
      linear_combination
        (-(v 2 * v 3 * h 0) + -(v 1 * v 2 * h 1) + -(v 1 * v 2 * h 0)) * g0 +
      (v 2 * v 3 * h 1) * g1 +
      ((-6 : ℝ) * (v 2 * v 4 * h 1) + v 2 * v 3 * h 1 + (-2 : ℝ) * ((v 2) ^ 2 * h 1) + -(v 0 * v 2 * h 0)) * g2 +
      (v 1 * v 2 * h 1) * g3 +
      (-(v 2 * v 3 * h 1)) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork91_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork91.toNetwork := by
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
  simp [cubicResidualNetwork91, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork91_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork91.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork91_jacobianNonzero
    cubicResidualNetwork91_fourCharts

def cubicResidualNetwork92 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .yy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork92_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork92.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork92, CodedBimolNetwork.toNetwork,
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
    have g0 : v 3 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g2 : (-4 : ℝ) * (v 3 * v 4) + v 2 * v 3 + -(v 1 * v 3) + (4 : ℝ) * (v 0 * v 4) + v 0 * v 3 + -(v 0 * v 2) = 0 := by
      nlinarith [hdet]
    simp [-mul_eq_zero, cubicResidualNetwork92, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (-4 : ℝ) * ((v 3) ^ 2 * v 4 * h 1) + v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + (8 : ℝ) * (v 0 * v 3 * v 4 * h 1) + -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 + v 0 * v 1 * v 3 * h 0 + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) + -((v 0) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((-8 : ℝ) * (v 3 * v 4 * h 1) + v 2 * v 3 * h 1 + -(v 1 * v 3 * h 0) + (4 : ℝ) * (v 0 * v 4 * h 1) + v 0 * v 3 * h 0) * g0 +
      (-(v 3 * h 1)) * g2
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork92, CodedBimolNetwork.toNetwork,
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
    have g0 : v 3 + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : -(v 3) + v 1 = 0 := by
      nlinarith [hg1]
    have g2 : v 3 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g5 : (12 : ℝ) * ((v 3) ^ 3 * v 4) + (-2 : ℝ) * (v 2 * (v 3) ^ 3) + (-16 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (2 : ℝ) * (v 0 * v 2 * (v 3) ^ 2) + (4 : ℝ) * ((v 0) ^ 2 * v 3 * v 4) = 0 := by
      nlinarith [hfold]
    have g6 : v 3 * h 1 + v 3 * h 0 + (-2 : ℝ) * ((v 3) ^ 3) + -(v 0 * h 0) + (2 : ℝ) * (v 0 * (v 3) ^ 2) = 0 := by
      nlinarith [hc0]
    simp [-mul_eq_zero, cubicResidualNetwork92, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (-8 : ℝ) * ((v 3) ^ 2 * v 4 * h 1) + (4 : ℝ) * ((v 3) ^ 2 * v 4 * h 0) + v 2 * (v 3) ^ 2 * h 1 + -(v 2 * (v 3) ^ 2 * h 0) + (4 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (-4 : ℝ) * (v 0 * v 3 * v 4 * h 0) + v 0 * v 2 * v 3 * h 0 = 0 := by
      linear_combination
        ((-2 : ℝ) * (v 3 * v 4 * h 1) + (-2 : ℝ) * (v 0 * v 4 * h 0)) * g0 +
      ((2 : ℝ) * (v 2 * v 3 * h 0) + (-2 : ℝ) * (v 0 * v 2 * h 0)) * g1 +
      ((10 : ℝ) * (v 3 * v 4 * h 0) + (-2 : ℝ) * (v 1 * v 2 * h 0)) * g2 +
      (-(v 3)) * g5 +
      ((-6 : ℝ) * (v 3 * v 4) + v 2 * v 3 + (2 : ℝ) * (v 0 * v 4)) * g6
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork92, CodedBimolNetwork.toNetwork,
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
    have g0 : v 3 + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : v 3 = 0 := by
      nlinarith [hg1]
    simp [-mul_eq_zero, cubicResidualNetwork92, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (4 : ℝ) * ((v 3) ^ 2 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 3 * v 4 * h 1) + -(v 1 * (v 3) ^ 2 * h 1) + v 1 * (v 3) ^ 2 * h 0 + v 1 * v 2 * v 3 * h 1 + -((v 1) ^ 2 * v 3 * h 0) + v 0 * (v 3) ^ 2 * h 1 + -(v 0 * (v 3) ^ 2 * h 0) + -(v 0 * v 2 * v 3 * h 1) + (4 : ℝ) * (v 0 * v 1 * v 4 * h 1) + v 0 * v 1 * v 3 * h 0 = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 1 * v 4 * h 1)) * g0 +
      ((4 : ℝ) * (v 3 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 4 * h 1) + -(v 1 * v 3 * h 1) + v 1 * v 3 * h 0 + v 1 * v 2 * h 1 + -((v 1) ^ 2 * h 0) + v 0 * v 3 * h 1 + -(v 0 * v 3 * h 0) + -(v 0 * v 2 * h 1) + v 0 * v 1 * h 0) * g1
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork92, CodedBimolNetwork.toNetwork,
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
    have g1 : v 3 = 0 := by
      nlinarith [hg1]
    simp [-mul_eq_zero, cubicResidualNetwork92, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (16 : ℝ) * (v 3 * (v 4) ^ 2 * h 1) + (8 : ℝ) * ((v 3) ^ 2 * v 4 * h 1) + (-4 : ℝ) * ((v 3) ^ 2 * v 4 * h 0) + (-8 : ℝ) * (v 2 * v 3 * v 4 * h 1) + -(v 2 * (v 3) ^ 2 * h 1) + v 2 * (v 3) ^ 2 * h 0 + (v 2) ^ 2 * v 3 * h 1 + (-4 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (4 : ℝ) * (v 1 * v 3 * v 4 * h 0) + -(v 1 * v 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((16 : ℝ) * ((v 4) ^ 2 * h 1) + (8 : ℝ) * (v 3 * v 4 * h 1) + (-4 : ℝ) * (v 3 * v 4 * h 0) + (-8 : ℝ) * (v 2 * v 4 * h 1) + -(v 2 * v 3 * h 1) + v 2 * v 3 * h 0 + (v 2) ^ 2 * h 1 + (-4 : ℝ) * (v 1 * v 4 * h 1) + (4 : ℝ) * (v 1 * v 4 * h 0) + -(v 1 * v 2 * h 0)) * g1
    nlinarith [hcertificate]

theorem cubicResidualNetwork92_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork92.toNetwork := by
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
  simp [cubicResidualNetwork92, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork92_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork92.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork92_jacobianNonzero
    cubicResidualNetwork92_fourCharts

def cubicResidualNetwork93 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xx, .xy), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork93_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork93.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork93, CodedBimolNetwork.toNetwork,
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
    have g2 : -(v 1 * v 4) + -(v 1 * v 2) + v 0 * v 4 + v 0 * v 2 = 0 := by
      nlinarith [hdet]
    have g3 : (-2 : ℝ) * (v 1 * (v 4) ^ 3) + (2 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * (v 2) ^ 2 * v 3) + (2 : ℝ) * ((v 1) ^ 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 1) ^ 2 * v 2 * v 4) + (2 : ℝ) * (v 0 * (v 4) ^ 3) + (-2 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * v 2 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * (v 2) ^ 2 * v 3) + (-2 : ℝ) * ((v 0) ^ 2 * (v 4) ^ 2) + (-2 : ℝ) * ((v 0) ^ 2 * v 2 * v 4) = 0 := by
      nlinarith [hfold]
    have g4 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + (-2 : ℝ) * (v 3 * h 0) + (2 : ℝ) * (v 3 * (v 4) ^ 2) + v 2 * h 1 + (-2 : ℝ) * (v 2 * (v 4) ^ 2) + (-2 : ℝ) * ((v 2) ^ 2 * v 3) + -(v 1 * h 0) + (2 : ℝ) * (v 1 * (v 4) ^ 2) + (2 : ℝ) * (v 1 * v 2 * v 4) + -(v 0 * h 0) + (2 : ℝ) * (v 0 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * v 2 * v 4) = 0 := by
      nlinarith [hc0]
    have g5 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (2 : ℝ) * (v 3 * h 0) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + -(v 2 * h 1) + (2 : ℝ) * (v 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 2) ^ 2 * v 3) + (2 : ℝ) * (v 1 * h 0) + (-2 : ℝ) * (v 1 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * v 2 * v 4) + (-2 : ℝ) * (v 0 * (v 4) ^ 2) + (-2 : ℝ) * (v 0 * v 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork93, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + v 1 * v 2 * v 4 * h 1 + (-2 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (v 1) ^ 2 * v 4 * h 0 + -(v 0 * (v 4) ^ 2 * h 1) + v 0 * (v 4) ^ 2 * h 0 + -(v 0 * v 2 * v 4 * h 1) + (2 : ℝ) * (v 0 * v 2 * v 3 * h 0) + -((v 0) ^ 2 * v 4 * h 0) = 0 := by
      linear_combination
        (-(v 4 * h 1) + v 4 * h 0 + (2 : ℝ) * (v 3 * h 1) + (2 : ℝ) * (v 3 * h 0) + -(v 2 * h 0) + v 1 * h 1 + v 0 * h 1) * g2 +
      ((-2 : ℝ) * (v 3) + -(v 1) + -(v 0)) * g3 +
      ((4 : ℝ) * ((v 3) ^ 2) + -((v 2) ^ 2) + (6 : ℝ) * (v 1 * v 3) + (2 : ℝ) * ((v 1) ^ 2) + (2 : ℝ) * (v 0 * v 3) + (2 : ℝ) * (v 0 * v 1)) * g4 +
      ((4 : ℝ) * ((v 3) ^ 2) + -((v 2) ^ 2) + (4 : ℝ) * (v 1 * v 3) + (v 1) ^ 2 + (4 : ℝ) * (v 0 * v 3) + (2 : ℝ) * (v 0 * v 1) + (v 0) ^ 2) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork93, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork93, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two] <;> ring
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork93, CodedBimolNetwork.toNetwork,
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
    have g4 : -(v 1 * v 4) + -(v 1 * v 2) + v 0 * v 4 + v 0 * v 2 = 0 := by
      nlinarith [hdet]
    have g5 : (-2 : ℝ) * (v 1 * (v 4) ^ 3) + (2 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * (v 2) ^ 2 * v 3) + (4 : ℝ) * ((v 1) ^ 2 * (v 4) ^ 2) + (4 : ℝ) * ((v 1) ^ 2 * v 2 * v 4) + (2 : ℝ) * (v 0 * (v 4) ^ 3) + (-2 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * v 2 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * (v 2) ^ 2 * v 3) + (-4 : ℝ) * (v 0 * v 1 * (v 4) ^ 2) + (-4 : ℝ) * (v 0 * v 1 * v 2 * v 4) = 0 := by
      nlinarith [hfold]
    have g6 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + (-2 : ℝ) * (v 3 * h 0) + (2 : ℝ) * (v 3 * (v 4) ^ 2) + v 2 * h 1 + (-2 : ℝ) * (v 2 * (v 4) ^ 2) + (-2 : ℝ) * ((v 2) ^ 2 * v 3) + -(v 1 * h 0) + (4 : ℝ) * (v 1 * (v 4) ^ 2) + (4 : ℝ) * (v 1 * v 2 * v 4) + -(v 0 * h 0) = 0 := by
      nlinarith [hc0]
    have g7 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (2 : ℝ) * (v 3 * h 0) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + -(v 2 * h 1) + (2 : ℝ) * (v 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 2) ^ 2 * v 3) + (2 : ℝ) * (v 1 * h 0) + (-4 : ℝ) * (v 1 * (v 4) ^ 2) + (-4 : ℝ) * (v 1 * v 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork93, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + -(v 1 * v 2 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * v 4 * h 0) + v 0 * (v 4) ^ 2 * h 1 + -(v 0 * (v 4) ^ 2 * h 0) + v 0 * v 2 * v 4 * h 1 + (-2 : ℝ) * (v 0 * v 2 * v 3 * h 0) + (2 : ℝ) * (v 0 * v 1 * v 4 * h 0) = 0 := by
      linear_combination
        (v 4 * h 1 + -(v 4 * h 0) + v 2 * h 0 + (-2 : ℝ) * (v 1 * h 1)) * g4 +
      ((2 : ℝ) * (v 1)) * g5 +
      ((2 : ℝ) * (v 2 * v 3) + (v 2) ^ 2 + (-4 : ℝ) * (v 1 * v 3) + (-4 : ℝ) * ((v 1) ^ 2)) * g6 +
      ((2 : ℝ) * (v 2 * v 3) + (v 2) ^ 2 + (-4 : ℝ) * (v 1 * v 3) + (-2 : ℝ) * ((v 1) ^ 2) + (-2 : ℝ) * (v 0 * v 1)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork93, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork93, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two] <;> ring

theorem cubicResidualNetwork93_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork93.toNetwork := by
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
  simp [cubicResidualNetwork93, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork93_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork93.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork93_jacobianNonzero
    cubicResidualNetwork93_fourCharts

def cubicResidualNetwork94 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xx, .xy), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork94_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork94.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork94, CodedBimolNetwork.toNetwork,
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
    have g2 : v 1 * v 4 + -(v 1 * v 2) + -(v 0 * v 4) + v 0 * v 2 = 0 := by
      nlinarith [hdet]
    have g3 : (2 : ℝ) * (v 1 * (v 4) ^ 3) + (2 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * (v 2) ^ 2 * v 3) + (2 : ℝ) * ((v 1) ^ 2 * (v 4) ^ 2) + (-2 : ℝ) * ((v 1) ^ 2 * v 2 * v 4) + (-2 : ℝ) * (v 0 * (v 4) ^ 3) + (-2 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * v 2 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * (v 2) ^ 2 * v 3) + (-2 : ℝ) * ((v 0) ^ 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 0) ^ 2 * v 2 * v 4) = 0 := by
      nlinarith [hfold]
    have g4 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (-2 : ℝ) * (v 3 * h 0) + (2 : ℝ) * (v 3 * (v 4) ^ 2) + v 2 * h 1 + (-2 : ℝ) * (v 2 * (v 4) ^ 2) + (-2 : ℝ) * ((v 2) ^ 2 * v 3) + -(v 1 * h 0) + (2 : ℝ) * (v 1 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * v 2 * v 4) + -(v 0 * h 0) + (2 : ℝ) * (v 0 * (v 4) ^ 2) + (-2 : ℝ) * (v 0 * v 2 * v 4) = 0 := by
      nlinarith [hc0]
    have g5 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + (2 : ℝ) * (v 3 * h 0) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + -(v 2 * h 1) + (2 : ℝ) * (v 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 2) ^ 2 * v 3) + (2 : ℝ) * (v 1 * h 0) + (-2 : ℝ) * (v 1 * (v 4) ^ 2) + (2 : ℝ) * (v 1 * v 2 * v 4) + (-2 : ℝ) * (v 0 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * v 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork94, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + -(v 1 * v 2 * v 4 * h 1) + (-2 : ℝ) * (v 1 * v 2 * v 3 * h 0) + -((v 1) ^ 2 * v 4 * h 0) + -(v 0 * (v 4) ^ 2 * h 1) + v 0 * (v 4) ^ 2 * h 0 + v 0 * v 2 * v 4 * h 1 + (2 : ℝ) * (v 0 * v 2 * v 3 * h 0) + (v 0) ^ 2 * v 4 * h 0 = 0 := by
      linear_combination
        (v 4 * h 1 + -(v 4 * h 0) + (2 : ℝ) * (v 3 * h 1) + (2 : ℝ) * (v 3 * h 0) + -(v 2 * h 0) + v 1 * h 1 + v 0 * h 1) * g2 +
      ((-2 : ℝ) * (v 3) + -(v 1) + -(v 0)) * g3 +
      ((4 : ℝ) * ((v 3) ^ 2) + -((v 2) ^ 2) + (6 : ℝ) * (v 1 * v 3) + (2 : ℝ) * ((v 1) ^ 2) + (2 : ℝ) * (v 0 * v 3) + (2 : ℝ) * (v 0 * v 1)) * g4 +
      ((4 : ℝ) * ((v 3) ^ 2) + -((v 2) ^ 2) + (4 : ℝ) * (v 1 * v 3) + (v 1) ^ 2 + (4 : ℝ) * (v 0 * v 3) + (2 : ℝ) * (v 0 * v 1) + (v 0) ^ 2) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork94, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork94, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two] <;> ring
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork94, CodedBimolNetwork.toNetwork,
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
    have g4 : v 1 * v 4 + -(v 1 * v 2) + -(v 0 * v 4) + v 0 * v 2 = 0 := by
      nlinarith [hdet]
    have g6 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (-2 : ℝ) * (v 3 * h 0) + (2 : ℝ) * (v 3 * (v 4) ^ 2) + v 2 * h 1 + (-2 : ℝ) * (v 2 * (v 4) ^ 2) + (-2 : ℝ) * ((v 2) ^ 2 * v 3) + -(v 1 * h 0) + (4 : ℝ) * (v 1 * (v 4) ^ 2) + (-4 : ℝ) * (v 1 * v 2 * v 4) + -(v 0 * h 0) = 0 := by
      nlinarith [hc0]
    have g7 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + (2 : ℝ) * (v 3 * h 0) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + -(v 2 * h 1) + (2 : ℝ) * (v 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 2) ^ 2 * v 3) + (2 : ℝ) * (v 1 * h 0) + (-4 : ℝ) * (v 1 * (v 4) ^ 2) + (4 : ℝ) * (v 1 * v 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork94, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + v 1 * v 2 * v 4 * h 1 + (2 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (2 : ℝ) * ((v 1) ^ 2 * v 4 * h 0) + v 0 * (v 4) ^ 2 * h 1 + -(v 0 * (v 4) ^ 2 * h 0) + -(v 0 * v 2 * v 4 * h 1) + (-2 : ℝ) * (v 0 * v 2 * v 3 * h 0) + (-2 : ℝ) * (v 0 * v 1 * v 4 * h 0) = 0 := by
      linear_combination
        (-(v 4 * h 1) + v 4 * h 0 + (2 : ℝ) * (v 1 * h 0)) * g4 +
      (v 2 * v 4 + (2 : ℝ) * (v 2 * v 3) + (2 : ℝ) * (v 1 * v 2)) * g6 +
      (v 2 * v 4 + (2 : ℝ) * (v 2 * v 3) + (2 : ℝ) * (v 1 * v 2)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork94, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork94, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two] <;> ring

theorem cubicResidualNetwork94_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork94.toNetwork := by
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
  simp [cubicResidualNetwork94, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork94_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork94.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork94_jacobianNonzero
    cubicResidualNetwork94_fourCharts

def cubicResidualNetwork95 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xx, .xy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork95_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork95.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork95, CodedBimolNetwork.toNetwork,
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
    have g0 : (2 : ℝ) * (v 4) + -(v 3) + v 2 + -(v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g1 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [heq1]
    have g2 : (-4 : ℝ) * (v 1 * v 4) + -(v 1 * v 2) + (4 : ℝ) * (v 0 * v 4) + v 0 * v 2 = 0 := by
      nlinarith [hdet]
    simp [-mul_eq_zero, cubicResidualNetwork95, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (8 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 3 * v 4 * h 0) + (-2 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (4 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (-8 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (8 : ℝ) * (v 0 * v 3 * v 4 * h 0) + (2 : ℝ) * (v 0 * v 2 * v 3 * h 0) + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) = 0 := by
      linear_combination
        ((4 : ℝ) * ((v 4) ^ 2 * h 1) + (3 : ℝ) * ((v 3) ^ 2 * h 1) + (2 : ℝ) * (v 2 * v 4 * h 1) + (-3 : ℝ) * (v 2 * v 3 * h 1) + (6 : ℝ) * (v 1 * v 3 * h 1) + (8 : ℝ) * (v 1 * v 3 * h 0) + (-4 : ℝ) * (v 1 * v 2 * h 0) + (16 : ℝ) * ((v 1) ^ 2 * h 0) + -(v 0 * v 2 * h 1)) * g0 +
      ((4 : ℝ) * ((v 4) ^ 2 * h 1) + (3 : ℝ) * ((v 3) ^ 2 * h 1) + (2 : ℝ) * (v 2 * v 4 * h 1) + (-3 : ℝ) * (v 2 * v 3 * h 1) + (2 : ℝ) * (v 1 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 4 * h 0) + (3 : ℝ) * (v 1 * v 3 * h 1) + (8 : ℝ) * (v 1 * v 3 * h 0) + (-6 : ℝ) * (v 1 * v 2 * h 0) + (8 : ℝ) * ((v 1) ^ 2 * h 0) + (-2 : ℝ) * (v 0 * v 4 * h 1) + (8 : ℝ) * (v 0 * v 4 * h 0) + (3 : ℝ) * (v 0 * v 3 * h 1) + -(v 0 * v 2 * h 1) + (2 : ℝ) * (v 0 * v 2 * h 0) + (8 : ℝ) * (v 0 * v 1 * h 0)) * g1 +
      ((4 : ℝ) * (v 4 * h 0) + (2 : ℝ) * (v 2 * h 0) + -(v 0 * h 1)) * g2
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork95, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork95, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two] <;> ring
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork95, CodedBimolNetwork.toNetwork,
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
    have g0 : (-2 : ℝ) * (v 3) + -(v 1) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : (4 : ℝ) * (v 4) + v 2 = 0 := by
      nlinarith [hg1]
    have g2 : (2 : ℝ) * (v 4) + -(v 3) + v 2 + -(v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork95, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (-8 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (8 : ℝ) * (v 1 * v 3 * v 4 * h 0) + (2 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (-8 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (8 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (-8 : ℝ) * (v 0 * v 3 * v 4 * h 0) + (-2 : ℝ) * (v 0 * v 2 * v 3 * h 0) + (8 : ℝ) * (v 0 * v 1 * v 4 * h 1) = 0 := by
      linear_combination
        ((-4 : ℝ) * ((v 3) ^ 2 * h 1) + (2 : ℝ) * (v 2 * v 3 * h 1) + (-2 : ℝ) * (v 1 * v 2 * h 1) + (-16 : ℝ) * (v 0 * v 4 * h 1) + (-12 : ℝ) * (v 0 * v 3 * h 1) + (-8 : ℝ) * ((v 0) ^ 2 * h 1)) * g0 +
      ((-4 : ℝ) * ((v 3) ^ 2 * h 1) + (-2 : ℝ) * (v 1 * v 3 * h 1) + (2 : ℝ) * (v 1 * v 3 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * h 1) + (-14 : ℝ) * (v 0 * v 3 * h 1) + (-2 : ℝ) * (v 0 * v 3 * h 0) + (-2 : ℝ) * (v 0 * v 1 * h 1) + (-8 : ℝ) * ((v 0) ^ 2 * h 1)) * g1 +
      ((12 : ℝ) * ((v 3) ^ 2 * h 1) + (20 : ℝ) * (v 0 * v 3 * h 1) + (8 : ℝ) * ((v 0) ^ 2 * h 1)) * g2 +
      ((4 : ℝ) * ((v 3) ^ 2 * h 1) + (4 : ℝ) * (v 0 * v 3 * h 1)) * g3
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork95, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork95, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two] <;> ring

theorem cubicResidualNetwork95_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork95.toNetwork := by
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
  simp [cubicResidualNetwork95, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork95_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork95.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork95_jacobianNonzero
    cubicResidualNetwork95_fourCharts

end SmallCusp

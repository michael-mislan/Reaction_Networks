import proofs.SmallCusp.Obstruction.CubicDegeneracy
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

def cubicResidualNetwork96 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xx, .xy), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork96_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork96.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork96, CodedBimolNetwork.toNetwork,
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
    have g0 : v 4 + -(v 3) + (2 : ℝ) * (v 2) + -(v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g1 : -(v 4) + v 3 + -(v 2) + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [heq1]
    have g2 : v 2 * v 4 + (-2 : ℝ) * (v 2 * v 3) + -(v 1 * v 4) + (-3 : ℝ) * (v 1 * v 2) + v 0 * v 4 + v 0 * v 2 = 0 := by
      nlinarith [hdet]
    have g3 : (-2 : ℝ) * (v 1 * (v 4) ^ 3) + (2 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (-4 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (-8 : ℝ) * (v 1 * (v 2) ^ 2 * v 3) + (2 : ℝ) * ((v 1) ^ 2 * (v 4) ^ 2) + (4 : ℝ) * ((v 1) ^ 2 * v 2 * v 4) + (2 : ℝ) * (v 0 * (v 4) ^ 3) + (-2 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (4 : ℝ) * (v 0 * v 2 * (v 4) ^ 2) + (8 : ℝ) * (v 0 * (v 2) ^ 2 * v 3) + (-2 : ℝ) * ((v 0) ^ 2 * (v 4) ^ 2) + (-4 : ℝ) * ((v 0) ^ 2 * v 2 * v 4) = 0 := by
      nlinarith [hfold]
    have g4 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + (-2 : ℝ) * (v 3 * h 0) + (2 : ℝ) * (v 3 * (v 4) ^ 2) + (2 : ℝ) * (v 2 * h 1) + (-4 : ℝ) * (v 2 * (v 4) ^ 2) + (-8 : ℝ) * ((v 2) ^ 2 * v 3) + -(v 1 * h 0) + (2 : ℝ) * (v 1 * (v 4) ^ 2) + (4 : ℝ) * (v 1 * v 2 * v 4) + -(v 0 * h 0) + (2 : ℝ) * (v 0 * (v 4) ^ 2) + (4 : ℝ) * (v 0 * v 2 * v 4) = 0 := by
      nlinarith [hc0]
    have g5 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (2 : ℝ) * (v 3 * h 0) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + -(v 2 * h 1) + (4 : ℝ) * (v 2 * (v 4) ^ 2) + (8 : ℝ) * ((v 2) ^ 2 * v 3) + (2 : ℝ) * (v 1 * h 0) + (-2 : ℝ) * (v 1 * (v 4) ^ 2) + (-4 : ℝ) * (v 1 * v 2 * v 4) + (-2 : ℝ) * (v 0 * (v 4) ^ 2) + (-4 : ℝ) * (v 0 * v 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork96, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + (2 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (v 1) ^ 2 * v 4 * h 0 + -(v 0 * (v 4) ^ 2 * h 1) + v 0 * (v 4) ^ 2 * h 0 + (-2 : ℝ) * (v 0 * v 2 * v 4 * h 1) + (4 : ℝ) * (v 0 * v 2 * v 3 * h 0) + -((v 0) ^ 2 * v 4 * h 0) = 0 := by
      linear_combination
        (((-1 : ℝ) / 4) * ((v 4) ^ 2 * h 0) + ((5 : ℝ) / 6) * (v 3 * v 4 * h 1) + ((37 : ℝ) / 12) * (v 3 * v 4 * h 0) + ((-11 : ℝ) / 3) * ((v 3) ^ 2 * h 0) + ((-5 : ℝ) / 12) * (v 2 * v 4 * h 1) + ((1 : ℝ) / 4) * ((v 2) ^ 2 * h 1) + ((-3 : ℝ) / 2) * ((v 2) ^ 2 * h 0) + ((5 : ℝ) / 3) * (v 1 * v 4 * h 1) + ((-47 : ℝ) / 6) * (v 1 * v 3 * h 0) + -((v 1) ^ 2 * h 0) + ((1 : ℝ) / 2) * (v 0 * v 4 * h 0) + ((1 : ℝ) / 2) * (v 0 * v 3 * h 0) + ((-13 : ℝ) / 6) * (v 0 * v 2 * h 0) + v 0 * v 1 * h 0) * g0 +
      (((-1 : ℝ) / 4) * ((v 4) ^ 2 * h 0) + ((5 : ℝ) / 6) * (v 3 * v 4 * h 1) + ((37 : ℝ) / 12) * (v 3 * v 4 * h 0) + ((-11 : ℝ) / 3) * ((v 3) ^ 2 * h 0) + ((5 : ℝ) / 12) * (v 2 * v 4 * h 1) + ((3 : ℝ) / 4) * (v 2 * v 4 * h 0) + ((11 : ℝ) / 4) * ((v 2) ^ 2 * h 1) + (-3 : ℝ) * ((v 2) ^ 2 * h 0) + ((5 : ℝ) / 6) * (v 1 * v 4 * h 1) + ((3 : ℝ) / 4) * (v 1 * v 4 * h 0) + ((-25 : ℝ) / 6) * (v 1 * v 3 * h 0) + ((-1 : ℝ) / 2) * ((v 1) ^ 2 * h 0) + ((5 : ℝ) / 6) * (v 0 * v 4 * h 1) + ((-1 : ℝ) / 4) * (v 0 * v 4 * h 0) + ((-19 : ℝ) / 6) * (v 0 * v 3 * h 0) + ((-35 : ℝ) / 6) * (v 0 * v 2 * h 0) + ((1 : ℝ) / 2) * ((v 0) ^ 2 * h 0)) * g1 +
      (((-1 : ℝ) / 6) * (v 4 * h 1) + ((1 : ℝ) / 6) * (v 3 * h 0) + ((-3 : ℝ) / 4) * (v 2 * h 1) + ((-3 : ℝ) / 4) * (v 2 * h 0) + ((-5 : ℝ) / 3) * (v 0 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + (4 : ℝ) * (v 2 * (v 4) ^ 2) + (8 : ℝ) * ((v 2) ^ 2 * v 3) + (-2 : ℝ) * (v 1 * (v 4) ^ 2) + (-4 : ℝ) * (v 1 * v 2 * v 4) + (-2 : ℝ) * (v 0 * (v 4) ^ 2) + (-4 : ℝ) * (v 0 * v 2 * v 4)) * g2 +
      (-(v 4)) * g3 +
      (((7 : ℝ) / 2) * (v 2 * v 4) + (-2 : ℝ) * (v 2 * v 3) + ((9 : ℝ) / 4) * ((v 2) ^ 2) + ((-9 : ℝ) / 2) * (v 1 * v 2) + ((-5 : ℝ) / 3) * (v 0 * v 4)) * g4 +
      (((5 : ℝ) / 2) * (v 2 * v 4) + ((9 : ℝ) / 4) * ((v 2) ^ 2) + ((-3 : ℝ) / 2) * (v 1 * v 2) + ((-5 : ℝ) / 3) * (v 0 * v 4) + -(v 0 * v 2)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork96, CodedBimolNetwork.toNetwork,
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
    have g0 : v 4 + (-2 : ℝ) * (v 3) + -(v 1) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : -(v 4) + (2 : ℝ) * (v 3) + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [hg1]
    have g2 : v 4 + -(v 3) + (2 : ℝ) * (v 2) + -(v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : -(v 4) + v 3 + -(v 2) + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork96, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 2 * (v 4) ^ 2 * h 1 + -(v 2 * (v 4) ^ 2 * h 0) + (2 : ℝ) * ((v 2) ^ 2 * v 4 * h 1) + (-4 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + v 1 * v 2 * v 4 * h 0 + v 0 * v 2 * v 4 * h 0 = 0 := by
      linear_combination
        ((-3 : ℝ) * (v 2 * v 4 * h 0) + (-4 : ℝ) * ((v 2) ^ 2 * h 0) + (4 : ℝ) * (v 1 * v 2 * h 1) + (-4 : ℝ) * ((v 1) ^ 2 * h 1)) * g0 +
      ((3 : ℝ) * (v 2 * v 4 * h 1) + (-4 : ℝ) * (v 2 * v 4 * h 0) + (-8 : ℝ) * ((v 2) ^ 2 * h 0) + (2 : ℝ) * (v 1 * v 4 * h 1) + (4 : ℝ) * (v 1 * v 2 * h 1) + (-6 : ℝ) * ((v 1) ^ 2 * h 1) + (-2 : ℝ) * (v 0 * v 3 * h 1) + (2 : ℝ) * (v 0 * v 2 * h 1) + (-2 : ℝ) * (v 0 * v 1 * h 1)) * g1 +
      ((-2 : ℝ) * (v 3 * v 4 * h 1) + (-2 : ℝ) * (v 2 * v 4 * h 1) + (2 : ℝ) * (v 2 * v 4 * h 0) + (4 : ℝ) * ((v 2) ^ 2 * h 0) + (2 : ℝ) * (v 1 * v 4 * h 1)) * g2 +
      ((-2 : ℝ) * (v 3 * v 4 * h 1) + (-6 : ℝ) * (v 2 * v 4 * h 1) + (4 : ℝ) * (v 2 * v 4 * h 0) + (8 : ℝ) * ((v 2) ^ 2 * h 0) + (4 : ℝ) * ((v 1) ^ 2 * h 1) + (4 : ℝ) * (v 0 * v 3 * h 1)) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork96, CodedBimolNetwork.toNetwork,
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
    have g0 : v 4 + (-2 : ℝ) * (v 3) + -(v 1) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : v 4 + (2 : ℝ) * (v 2) = 0 := by
      nlinarith [hg1]
    have g2 : v 4 + -(v 3) + (2 : ℝ) * (v 2) + -(v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : -(v 4) + v 3 + -(v 2) + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [heq1]
    have g4 : v 2 * v 4 + (-2 : ℝ) * (v 2 * v 3) + -(v 1 * v 4) + (-3 : ℝ) * (v 1 * v 2) + v 0 * v 4 + v 0 * v 2 = 0 := by
      nlinarith [hdet]
    have g6 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + (-2 : ℝ) * (v 3 * h 0) + (2 : ℝ) * (v 3 * (v 4) ^ 2) + (2 : ℝ) * (v 2 * h 1) + (-2 : ℝ) * (v 2 * (v 4) ^ 2) + (-2 : ℝ) * ((v 2) ^ 2 * v 3) + -(v 1 * h 0) + (4 : ℝ) * (v 1 * (v 4) ^ 2) + (4 : ℝ) * (v 1 * v 2 * v 4) + -(v 0 * h 0) = 0 := by
      nlinarith [hc0]
    have g7 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (2 : ℝ) * (v 3 * h 0) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + -(v 2 * h 1) + (2 : ℝ) * (v 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 2) ^ 2 * v 3) + (2 : ℝ) * (v 1 * h 0) + (-4 : ℝ) * (v 1 * (v 4) ^ 2) + (-4 : ℝ) * (v 1 * v 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork96, CodedBimolNetwork.toNetwork,
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
        ((2 : ℝ) * (v 1 * v 3 * h 0) + (2 : ℝ) * (v 0 * v 3 * h 1) + (4 : ℝ) * (v 0 * v 1 * h 1) + (4 : ℝ) * (v 0 * v 1 * h 0)) * g0 +
      (-(v 1 * v 4 * h 1) + v 1 * v 4 * h 0 + (2 : ℝ) * (v 1 * v 3 * h 0) + (3 : ℝ) * (v 1 * v 2 * h 1) + (-6 : ℝ) * ((v 1) ^ 2 * h 0) + v 0 * v 4 * h 1 + (-2 : ℝ) * (v 0 * v 4 * h 0) + (2 : ℝ) * (v 0 * v 3 * h 1) + v 0 * v 3 * h 0 + v 0 * v 2 * h 1 + (9 : ℝ) * (v 0 * v 1 * h 0) + -((v 0) ^ 2 * h 0)) * g1 +
      ((-2 : ℝ) * (v 1 * v 3 * h 0) + (-4 : ℝ) * (v 1 * v 2 * h 1) + (4 : ℝ) * ((v 1) ^ 2 * h 0) + v 0 * v 4 * h 0 + (-2 : ℝ) * (v 0 * v 3 * h 1) + (-4 : ℝ) * (v 0 * v 1 * h 1) + (-4 : ℝ) * (v 0 * v 1 * h 0)) * g2 +
      ((2 : ℝ) * (v 1 * v 3 * h 0) + (-2 : ℝ) * (v 1 * v 2 * h 1) + (2 : ℝ) * ((v 1) ^ 2 * h 0) + (2 : ℝ) * (v 0 * v 3 * h 1) + (2 : ℝ) * (v 0 * v 2 * h 1) + (2 : ℝ) * (v 0 * v 1 * h 0)) * g3 +
      ((-2 : ℝ) * (v 1 * h 0) + (2 : ℝ) * (v 0 * h 0)) * g4 +
      ((-2 : ℝ) * (v 1 * v 3)) * g6 +
      ((-2 : ℝ) * (v 1 * v 3)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork96, CodedBimolNetwork.toNetwork,
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
    have g0 : v 4 + (-2 : ℝ) * (v 3) + -(v 1) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : v 4 + (2 : ℝ) * (v 2) = 0 := by
      nlinarith [hg1]
    have g2 : -(v 4) + (2 : ℝ) * (v 3) + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [hg2]
    have g3 : v 4 + -(v 3) + (2 : ℝ) * (v 2) + -(v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g4 : -(v 4) + v 3 + -(v 2) + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork96, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -(v 2 * (v 4) ^ 2 * h 1) + v 2 * (v 4) ^ 2 * h 0 + -((v 2) ^ 2 * v 4 * h 1) + (2 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + (-2 : ℝ) * (v 1 * v 2 * v 4 * h 0) = 0 := by
      linear_combination
        (((1 : ℝ) / 2) * ((v 4) ^ 2 * h 1) + ((-1 : ℝ) / 2) * ((v 4) ^ 2 * h 0)) * g0 +
      (((1 : ℝ) / 2) * (v 3 * v 4 * h 0) + ((-1 : ℝ) / 2) * (v 2 * v 4 * h 1) + v 2 * v 3 * h 0) * g1 +
      (((1 : ℝ) / 2) * ((v 4) ^ 2 * h 1) + -((v 4) ^ 2 * h 0) + -(v 2 * v 4 * h 0)) * g2 +
      (((-1 : ℝ) / 2) * ((v 4) ^ 2 * h 1) + ((1 : ℝ) / 2) * ((v 4) ^ 2 * h 0)) * g3 +
      (((-1 : ℝ) / 2) * ((v 4) ^ 2 * h 1) + (v 4) ^ 2 * h 0) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork96_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork96.toNetwork := by
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
  simp [cubicResidualNetwork96, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork96_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork96.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork96_jacobianNonzero
    cubicResidualNetwork96_fourCharts

def cubicResidualNetwork97 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xx, .xy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork97_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork97.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork97, CodedBimolNetwork.toNetwork,
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
    have g0 : (2 : ℝ) * (v 4) + -(v 3) + (2 : ℝ) * (v 2) + -(v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g1 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [heq1]
    have g2 : (-2 : ℝ) * (v 2 * v 3) + (-4 : ℝ) * (v 1 * v 4) + (-3 : ℝ) * (v 1 * v 2) + (4 : ℝ) * (v 0 * v 4) + v 0 * v 2 = 0 := by
      nlinarith [hdet]
    have g4 : (4 : ℝ) * (v 4 * h 1) + (-2 : ℝ) * (v 3 * h 0) + (-32 : ℝ) * (v 3 * (v 4) ^ 2) + (16 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * (v 2 * h 1) + (-32 : ℝ) * (v 2 * v 3 * v 4) + (-8 : ℝ) * ((v 2) ^ 2 * v 3) + -(v 1 * h 0) + (16 : ℝ) * (v 1 * v 3 * v 4) + (4 : ℝ) * ((v 1) ^ 2 * v 4) + -(v 0 * h 0) + (16 : ℝ) * (v 0 * v 3 * v 4) + (8 : ℝ) * (v 0 * v 1 * v 4) + (4 : ℝ) * ((v 0) ^ 2 * v 4) = 0 := by
      nlinarith [hc0]
    have g5 : (-4 : ℝ) * (v 4 * h 1) + (2 : ℝ) * (v 3 * h 0) + (32 : ℝ) * (v 3 * (v 4) ^ 2) + (-16 : ℝ) * ((v 3) ^ 2 * v 4) + -(v 2 * h 1) + (32 : ℝ) * (v 2 * v 3 * v 4) + (8 : ℝ) * ((v 2) ^ 2 * v 3) + (2 : ℝ) * (v 1 * h 0) + (-16 : ℝ) * (v 1 * v 3 * v 4) + (-4 : ℝ) * ((v 1) ^ 2 * v 4) + (-16 : ℝ) * (v 0 * v 3 * v 4) + (-8 : ℝ) * (v 0 * v 1 * v 4) + (-4 : ℝ) * ((v 0) ^ 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork97, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (8 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 3 * v 4 * h 0) + (-4 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (4 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (-8 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (8 : ℝ) * (v 0 * v 3 * v 4 * h 0) + (4 : ℝ) * (v 0 * v 2 * v 3 * h 0) + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) = 0 := by
      linear_combination
        ((16 : ℝ) * ((v 4) ^ 2 * h 1) + (-32 : ℝ) * ((v 4) ^ 2 * h 0) + (10 : ℝ) * (v 3 * v 4 * h 1) + -((v 3) ^ 2 * h 1) + (-24 : ℝ) * (v 2 * v 4 * h 0) + (5 : ℝ) * (v 2 * v 3 * h 1) + (-4 : ℝ) * (v 2 * v 3 * h 0) + (-4 : ℝ) * ((v 2) ^ 2 * h 1) + (-4 : ℝ) * ((v 2) ^ 2 * h 0) + (16 : ℝ) * (v 1 * v 4 * h 0) + (6 : ℝ) * (v 1 * v 2 * h 1) + (4 : ℝ) * ((v 1) ^ 2 * h 1) + (2 : ℝ) * (v 0 * v 3 * h 1) + (-2 : ℝ) * (v 0 * v 2 * h 1) + (4 : ℝ) * (v 0 * v 1 * h 1)) * g0 +
      ((16 : ℝ) * ((v 4) ^ 2 * h 1) + (-32 : ℝ) * ((v 4) ^ 2 * h 0) + (10 : ℝ) * (v 3 * v 4 * h 1) + -((v 3) ^ 2 * h 1) + (-40 : ℝ) * (v 2 * v 4 * h 0) + (6 : ℝ) * (v 2 * v 3 * h 1) + (-4 : ℝ) * (v 2 * v 3 * h 0) + (-8 : ℝ) * ((v 2) ^ 2 * h 1) + (-8 : ℝ) * ((v 2) ^ 2 * h 0) + (8 : ℝ) * (v 1 * v 4 * h 0) + v 1 * v 3 * h 1 + (2 : ℝ) * ((v 1) ^ 2 * h 1) + (8 : ℝ) * (v 0 * v 4 * h 0) + v 0 * v 3 * h 1 + (4 : ℝ) * (v 0 * v 1 * h 1) + (2 : ℝ) * ((v 0) ^ 2 * h 1)) * g1 +
      ((4 : ℝ) * (v 4 * h 1) + (-8 : ℝ) * (v 4 * h 0) + (-4 : ℝ) * (v 2 * h 0)) * g2 +
      ((-16 : ℝ) * ((v 4) ^ 2) + (-8 : ℝ) * (v 2 * v 4)) * g4 +
      ((-16 : ℝ) * ((v 4) ^ 2) + (-8 : ℝ) * (v 2 * v 4)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork97, CodedBimolNetwork.toNetwork,
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
    have g1 : (2 : ℝ) * (v 3) + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [hg1]
    have g2 : (2 : ℝ) * (v 4) + -(v 3) + (2 : ℝ) * (v 2) + -(v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork97, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (8 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (-8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (-4 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + (4 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (4 : ℝ) * (v 0 * v 2 * v 4 * h 1) = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 2 * v 4 * h 1) + (2 : ℝ) * (v 2 * v 3 * h 0) + (2 : ℝ) * (v 1 * v 2 * h 0) + (-4 : ℝ) * ((v 1) ^ 2 * h 0)) * g0 +
      ((-4 : ℝ) * (v 2 * v 4 * h 0) + (-2 : ℝ) * ((v 2) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 3 * h 0) + (5 : ℝ) * (v 1 * v 2 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * h 0) + (2 : ℝ) * (v 0 * v 3 * h 0) + v 0 * v 2 * h 0 + (-2 : ℝ) * (v 0 * v 1 * h 0)) * g1 +
      ((4 : ℝ) * ((v 3) ^ 2 * h 0)) * g2 +
      ((4 : ℝ) * ((v 3) ^ 2 * h 0) + (-4 : ℝ) * (v 1 * v 2 * h 0)) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork97, CodedBimolNetwork.toNetwork,
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
    have g1 : (4 : ℝ) * (v 4) + (2 : ℝ) * (v 2) = 0 := by
      nlinarith [hg1]
    have g2 : (2 : ℝ) * (v 4) + -(v 3) + (2 : ℝ) * (v 2) + -(v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [heq1]
    have g4 : (-2 : ℝ) * (v 2 * v 3) + (-4 : ℝ) * (v 1 * v 4) + (-3 : ℝ) * (v 1 * v 2) + (4 : ℝ) * (v 0 * v 4) + v 0 * v 2 = 0 := by
      nlinarith [hdet]
    have g5 : (-32 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (16 : ℝ) * (v 1 * (v 3) ^ 2 * v 4) + (-16 : ℝ) * (v 1 * v 2 * v 3 * v 4) + (-2 : ℝ) * (v 1 * (v 2) ^ 2 * v 3) + (32 : ℝ) * ((v 1) ^ 2 * v 3 * v 4) + (16 : ℝ) * ((v 1) ^ 3 * v 4) + (32 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (-16 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (16 : ℝ) * (v 0 * v 2 * v 3 * v 4) + (2 : ℝ) * (v 0 * (v 2) ^ 2 * v 3) + (-32 : ℝ) * (v 0 * v 1 * v 3 * v 4) + (-16 : ℝ) * (v 0 * (v 1) ^ 2 * v 4) = 0 := by
      nlinarith [hfold]
    have g6 : (4 : ℝ) * (v 4 * h 1) + (-2 : ℝ) * (v 3 * h 0) + (-32 : ℝ) * (v 3 * (v 4) ^ 2) + (16 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * (v 2 * h 1) + (-16 : ℝ) * (v 2 * v 3 * v 4) + (-2 : ℝ) * ((v 2) ^ 2 * v 3) + -(v 1 * h 0) + (32 : ℝ) * (v 1 * v 3 * v 4) + (16 : ℝ) * ((v 1) ^ 2 * v 4) + -(v 0 * h 0) = 0 := by
      nlinarith [hc0]
    have g7 : (-4 : ℝ) * (v 4 * h 1) + (2 : ℝ) * (v 3 * h 0) + (32 : ℝ) * (v 3 * (v 4) ^ 2) + (-16 : ℝ) * ((v 3) ^ 2 * v 4) + -(v 2 * h 1) + (16 : ℝ) * (v 2 * v 3 * v 4) + (2 : ℝ) * ((v 2) ^ 2 * v 3) + (2 : ℝ) * (v 1 * h 0) + (-32 : ℝ) * (v 1 * v 3 * v 4) + (-16 : ℝ) * ((v 1) ^ 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork97, CodedBimolNetwork.toNetwork,
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
        (((16 : ℝ) / 3) * ((v 4) ^ 2 * h 1) + ((-8 : ℝ) / 3) * (v 2 * v 3 * h 1) + ((7 : ℝ) / 2) * (v 1 * v 3 * h 0) + ((-16 : ℝ) / 3) * (v 1 * v 2 * h 1) + ((-13 : ℝ) / 3) * (v 1 * v 2 * h 0) + (-6 : ℝ) * (v 0 * v 4 * h 0) + (-4 : ℝ) * (v 0 * v 3 * h 1) + (-5 : ℝ) * (v 0 * v 3 * h 0) + (8 : ℝ) * (v 0 * v 2 * h 1) + (-8 : ℝ) * ((v 0) ^ 2 * h 1) + (-3 : ℝ) * ((v 0) ^ 2 * h 0)) * g0 +
      (((8 : ℝ) / 3) * (v 3 * v 4 * h 1) + ((-20 : ℝ) / 3) * (v 2 * v 3 * h 1) + ((4 : ℝ) / 3) * (v 1 * v 4 * h 1) + (-2 : ℝ) * (v 1 * v 3 * h 1) + ((17 : ℝ) / 6) * (v 1 * v 3 * h 0) + ((-16 : ℝ) / 3) * (v 1 * v 2 * h 1) + (-2 : ℝ) * ((v 1) ^ 2 * h 1) + ((1 : ℝ) / 12) * ((v 1) ^ 2 * h 0) + ((4 : ℝ) / 3) * (v 0 * v 4 * h 1) + (-2 : ℝ) * (v 0 * v 3 * h 1) + ((-22 : ℝ) / 3) * (v 0 * v 3 * h 0) + ((2 : ℝ) / 3) * (v 0 * v 2 * h 1) + (2 : ℝ) * (v 0 * v 1 * h 1) + ((-19 : ℝ) / 12) * (v 0 * v 1 * h 0) + (-4 : ℝ) * ((v 0) ^ 2 * h 1) + (-3 : ℝ) * ((v 0) ^ 2 * h 0)) * g1 +
      (((16 : ℝ) / 3) * ((v 3) ^ 2 * h 0) + ((8 : ℝ) / 3) * (v 2 * v 3 * h 1) + ((4 : ℝ) / 3) * (v 1 * v 2 * h 1) + ((-1 : ℝ) / 3) * ((v 1) ^ 2 * h 0) + (12 : ℝ) * (v 0 * v 3 * h 1) + (8 : ℝ) * (v 0 * v 3 * h 0) + (8 : ℝ) * ((v 0) ^ 2 * h 1) + (3 : ℝ) * ((v 0) ^ 2 * h 0)) * g2 +
      (((16 : ℝ) / 3) * ((v 3) ^ 2 * h 0) + ((-8 : ℝ) / 3) * (v 2 * v 3 * h 1) + ((5 : ℝ) / 3) * (v 1 * v 3 * h 0) + ((-1 : ℝ) / 6) * ((v 1) ^ 2 * h 0) + (4 : ℝ) * (v 0 * v 3 * h 1) + ((10 : ℝ) / 3) * (v 0 * v 3 * h 0) + ((-1 : ℝ) / 6) * (v 0 * v 1 * h 0)) * g3 +
      (((-128 : ℝ) / 3) * (v 3 * (v 4) ^ 2) + ((64 : ℝ) / 3) * ((v 3) ^ 2 * v 4) + ((-64 : ℝ) / 3) * (v 2 * v 3 * v 4) + ((-8 : ℝ) / 3) * ((v 2) ^ 2 * v 3) + ((128 : ℝ) / 3) * (v 1 * v 3 * v 4) + ((64 : ℝ) / 3) * ((v 1) ^ 2 * v 4)) * g4 +
      (((16 : ℝ) / 3) * (v 4)) * g5 +
      (((8 : ℝ) / 3) * (v 2 * v 3) + (4 : ℝ) * (v 1 * v 2)) * g6 +
      (((4 : ℝ) / 3) * (v 0 * v 2)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork97, CodedBimolNetwork.toNetwork,
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
    have g1 : (4 : ℝ) * (v 4) + (2 : ℝ) * (v 2) = 0 := by
      nlinarith [hg1]
    have g2 : (2 : ℝ) * (v 3) + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [hg2]
    have g4 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork97, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (-8 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (2 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 1) = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 3 * v 4 * h 1) + (4 : ℝ) * (v 3 * v 4 * h 0) + (v 2) ^ 2 * h 0 + (-4 : ℝ) * (v 1 * v 4 * h 1) + (4 : ℝ) * (v 1 * v 4 * h 0) + (-2 : ℝ) * (v 1 * v 2 * h 0)) * g1 +
      ((8 : ℝ) * ((v 4) ^ 2 * h 1) + (-8 : ℝ) * ((v 4) ^ 2 * h 0)) * g2 +
      ((2 : ℝ) * ((v 2) ^ 2 * h 0)) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork97_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork97.toNetwork := by
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
  simp [cubicResidualNetwork97, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork97_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork97.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork97_jacobianNonzero
    cubicResidualNetwork97_fourCharts

def cubicResidualNetwork98 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.xx, .xy), (.xy, .xx), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork98_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork98.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork98, CodedBimolNetwork.toNetwork,
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
    have g0 : (2 : ℝ) * (v 4) + v 3 + -(v 2) + -(v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g1 : (-2 : ℝ) * (v 4) + -(v 3) + v 2 + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [heq1]
    have g2 : (-4 : ℝ) * (v 1 * v 4) + -(v 1 * v 3) + (4 : ℝ) * (v 0 * v 4) + v 0 * v 3 = 0 := by
      nlinarith [hdet]
    simp [-mul_eq_zero, cubicResidualNetwork98, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + (8 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (4 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (v 1) ^ 2 * v 3 * h 0 + -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 + (-8 : ℝ) * (v 0 * v 2 * v 4 * h 1) + (8 : ℝ) * (v 0 * v 2 * v 4 * h 0) + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) + -((v 0) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        (((1 : ℝ) / 2) * ((v 3) ^ 2 * h 1) + ((-1 : ℝ) / 2) * ((v 3) ^ 2 * h 0) + ((-1 : ℝ) / 2) * (v 2 * v 3 * h 1) + v 2 * v 3 * h 0 + -((v 2) ^ 2 * h 1) + -(v 1 * v 3 * h 0) + (4 : ℝ) * ((v 1) ^ 2 * h 1) + (-4 : ℝ) * (v 0 * v 4 * h 0) + -(v 0 * v 3 * h 1)) * g0 +
      (((1 : ℝ) / 2) * ((v 3) ^ 2 * h 1) + ((-1 : ℝ) / 2) * ((v 3) ^ 2 * h 0) + ((-1 : ℝ) / 2) * (v 2 * v 3 * h 1) + v 2 * v 3 * h 0 + -((v 2) ^ 2 * h 1) + -(v 1 * v 3 * h 1) + v 1 * v 2 * h 1 + (2 : ℝ) * ((v 1) ^ 2 * h 1) + (-4 : ℝ) * (v 0 * v 4 * h 0) + -(v 0 * v 3 * h 0) + -(v 0 * v 2 * h 1) + (2 : ℝ) * (v 0 * v 1 * h 1)) * g1 +
      (((1 : ℝ) / 2) * (v 3 * h 1) + ((-1 : ℝ) / 2) * (v 3 * h 0) + ((-5 : ℝ) / 2) * (v 2 * h 1) + (2 : ℝ) * (v 2 * h 0) + -(v 0 * h 1) + -(v 0 * h 0)) * g2
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork98, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork98, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork98, CodedBimolNetwork.toNetwork,
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
    have g0 : v 3 + (-2 : ℝ) * (v 2) + -(v 1) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : (4 : ℝ) * (v 4) + v 3 = 0 := by
      nlinarith [hg1]
    have g2 : (2 : ℝ) * (v 4) + v 3 + -(v 2) + -(v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : (-2 : ℝ) * (v 4) + -(v 3) + v 2 + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork98, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -(v 1 * (v 3) ^ 2 * h 1) + v 1 * (v 3) ^ 2 * h 0 + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (-8 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (-2 : ℝ) * ((v 1) ^ 2 * v 3 * h 0) + v 0 * (v 3) ^ 2 * h 1 + -(v 0 * (v 3) ^ 2 * h 0) + (8 : ℝ) * (v 0 * v 2 * v 4 * h 1) + (-8 : ℝ) * (v 0 * v 2 * v 4 * h 0) + (8 : ℝ) * (v 0 * v 1 * v 4 * h 1) + (2 : ℝ) * (v 0 * v 1 * v 3 * h 0) = 0 := by
      linear_combination
        (-(v 1 * v 3 * h 1) + (2 : ℝ) * (v 1 * v 2 * h 1) + (4 : ℝ) * ((v 1) ^ 2 * h 1)) * g0 +
      ((4 : ℝ) * (v 1 * v 4 * h 0) + v 1 * v 3 * h 0 + (v 1) ^ 2 * h 1 + (-2 : ℝ) * ((v 1) ^ 2 * h 0) + (-4 : ℝ) * (v 0 * v 4 * h 0) + -(v 0 * v 3 * h 1) + -(v 0 * v 3 * h 0) + (2 : ℝ) * (v 0 * v 2 * h 1) + v 0 * v 1 * h 1 + (2 : ℝ) * (v 0 * v 1 * h 0)) * g1 +
      ((-8 : ℝ) * (v 1 * v 4 * h 0) + (-4 : ℝ) * (v 1 * v 2 * h 1) + (-8 : ℝ) * ((v 1) ^ 2 * h 1)) * g2 +
      ((-2 : ℝ) * ((v 1) ^ 2 * h 1) + (-8 : ℝ) * (v 0 * v 4 * h 0) + (-2 : ℝ) * (v 0 * v 3 * h 1) + (-2 : ℝ) * (v 0 * v 1 * h 1)) * g3
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork98, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork98, CodedBimolNetwork.toNetwork,
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

theorem cubicResidualNetwork98_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork98.toNetwork := by
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
  simp [cubicResidualNetwork98, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork98_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork98.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork98_jacobianNonzero
    cubicResidualNetwork98_fourCharts

def cubicResidualNetwork99 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.xx, .xy), (.xy, .yy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork99_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork99.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork99, CodedBimolNetwork.toNetwork,
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
    have g0 : (2 : ℝ) * (v 4) + -(v 3) + -(v 2) + -(v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g1 : (-2 : ℝ) * (v 4) + v 3 + v 2 + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [heq1]
    have g2 : (-4 : ℝ) * (v 1 * v 4) + v 1 * v 3 + (4 : ℝ) * (v 0 * v 4) + -(v 0 * v 3) = 0 := by
      nlinarith [hdet]
    simp [-mul_eq_zero, cubicResidualNetwork99, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + (8 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (4 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + -((v 1) ^ 2 * v 3 * h 0) + -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 + (-8 : ℝ) * (v 0 * v 2 * v 4 * h 1) + (8 : ℝ) * (v 0 * v 2 * v 4 * h 0) + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) + (v 0) ^ 2 * v 3 * h 0 = 0 := by
      linear_combination
        ((-14 : ℝ) * ((v 4) ^ 2 * h 0) + (-8 : ℝ) * (v 2 * v 4 * h 0) + ((-1 : ℝ) / 2) * ((v 2) ^ 2 * h 0) + (-4 : ℝ) * (v 1 * v 4 * h 1) + (-2 : ℝ) * (v 1 * v 3 * h 1) + (2 : ℝ) * ((v 1) ^ 2 * h 0) + (-3 : ℝ) * (v 0 * v 4 * h 0) + v 0 * v 3 * h 1 + ((1 : ℝ) / 2) * (v 0 * v 2 * h 0) + v 0 * v 1 * h 0) * g0 +
      ((-14 : ℝ) * ((v 4) ^ 2 * h 0) + (-8 : ℝ) * (v 2 * v 4 * h 0) + ((-1 : ℝ) / 2) * ((v 2) ^ 2 * h 0) + -(v 1 * v 4 * h 0) + -(v 1 * v 3 * h 1) + ((1 : ℝ) / 2) * (v 1 * v 2 * h 0) + (v 1) ^ 2 * h 0 + (-4 : ℝ) * (v 0 * v 4 * h 1) + (-2 : ℝ) * (v 0 * v 4 * h 0) + ((3 : ℝ) / 2) * (v 0 * v 1 * h 0) + ((1 : ℝ) / 2) * ((v 0) ^ 2 * h 0)) * g1 +
      ((-2 : ℝ) * (v 4 * h 1) + (-3 : ℝ) * (v 4 * h 0) + -(v 3 * h 0) + -(v 2 * h 1) + ((-1 : ℝ) / 2) * (v 2 * h 0) + -(v 0 * h 1) + ((-1 : ℝ) / 2) * (v 0 * h 0)) * g2
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork99, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork99, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork99, CodedBimolNetwork.toNetwork,
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
    have g0 : -(v 3) + (-2 : ℝ) * (v 2) + -(v 1) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : (4 : ℝ) * (v 4) + -(v 3) = 0 := by
      nlinarith [hg1]
    have g2 : (2 : ℝ) * (v 4) + -(v 3) + -(v 2) + -(v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : (-2 : ℝ) * (v 4) + v 3 + v 2 + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork99, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -(v 1 * (v 3) ^ 2 * h 1) + v 1 * (v 3) ^ 2 * h 0 + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (-8 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (2 : ℝ) * ((v 1) ^ 2 * v 3 * h 0) + v 0 * (v 3) ^ 2 * h 1 + -(v 0 * (v 3) ^ 2 * h 0) + (8 : ℝ) * (v 0 * v 2 * v 4 * h 1) + (-8 : ℝ) * (v 0 * v 2 * v 4 * h 0) + (8 : ℝ) * (v 0 * v 1 * v 4 * h 1) + (-2 : ℝ) * (v 0 * v 1 * v 3 * h 0) = 0 := by
      linear_combination
        ((4 : ℝ) * (v 1 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 4 * h 0) + (2 : ℝ) * (v 1 * v 2 * h 1) + (-2 : ℝ) * (v 1 * v 2 * h 0) + (4 : ℝ) * (v 0 * v 1 * h 1) + (-4 : ℝ) * (v 0 * v 1 * h 0)) * g0 +
      (v 1 * v 3 * h 1 + -(v 1 * v 3 * h 0) + (2 : ℝ) * (v 1 * v 2 * h 1) + (-2 : ℝ) * (v 1 * v 2 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * h 1) + (-4 : ℝ) * (v 0 * v 4 * h 0) + v 0 * v 3 * h 1 + v 0 * v 3 * h 0 + (2 : ℝ) * (v 0 * v 2 * h 1) + (6 : ℝ) * (v 0 * v 1 * h 1)) * g1 +
      ((-4 : ℝ) * (v 1 * v 2 * h 1) + (4 : ℝ) * (v 1 * v 2 * h 0) + (4 : ℝ) * ((v 1) ^ 2 * h 1) + (-4 : ℝ) * ((v 1) ^ 2 * h 0) + (-4 : ℝ) * (v 0 * v 1 * h 1) + (4 : ℝ) * (v 0 * v 1 * h 0)) * g2 +
      ((2 : ℝ) * ((v 1) ^ 2 * h 1) + (-2 : ℝ) * ((v 1) ^ 2 * h 0) + (-8 : ℝ) * (v 0 * v 4 * h 0) + (2 : ℝ) * (v 0 * v 3 * h 1) + (2 : ℝ) * (v 0 * v 1 * h 1) + (-2 : ℝ) * (v 0 * v 1 * h 0)) * g3
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork99, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork99, CodedBimolNetwork.toNetwork,
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

theorem cubicResidualNetwork99_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork99.toNetwork := by
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
  simp [cubicResidualNetwork99, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork99_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork99.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork99_jacobianNonzero
    cubicResidualNetwork99_fourCharts

def cubicResidualNetwork100 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xy, .xx), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork100_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork100.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork100, CodedBimolNetwork.toNetwork,
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
    have g0 : (2 : ℝ) * (v 4) + v 3 + v 2 + -(v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g1 : (-2 : ℝ) * (v 4) + -(v 3) + -(v 2) + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [heq1]
    have g2 : (-4 : ℝ) * (v 1 * v 4) + -(v 1 * v 3) + -(v 1 * v 2) + (4 : ℝ) * (v 0 * v 4) + v 0 * v 3 + v 0 * v 2 = 0 := by
      nlinarith [hdet]
    simp [-mul_eq_zero, cubicResidualNetwork100, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + v 1 * v 2 * v 3 * h 1 + (4 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (v 1) ^ 2 * v 3 * h 0 + -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 + -(v 0 * v 2 * v 3 * h 1) + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) + -((v 0) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((4 : ℝ) * ((v 4) ^ 2 * h 1) + (-4 : ℝ) * ((v 4) ^ 2 * h 0) + (2 : ℝ) * (v 2 * v 4 * h 1) + (-4 : ℝ) * (v 2 * v 4 * h 0) + -((v 2) ^ 2 * h 0) + (2 : ℝ) * (v 1 * v 3 * h 1) + (-3 : ℝ) * (v 1 * v 3 * h 0) + (4 : ℝ) * ((v 1) ^ 2 * h 0) + (-4 : ℝ) * (v 0 * v 4 * h 0) + (-2 : ℝ) * (v 0 * v 3 * h 1) + v 0 * v 3 * h 0 + (-2 : ℝ) * (v 0 * v 2 * h 1) + (4 : ℝ) * (v 0 * v 1 * h 1) + (-4 : ℝ) * (v 0 * v 1 * h 0)) * g0 +
      ((4 : ℝ) * ((v 4) ^ 2 * h 1) + (-4 : ℝ) * ((v 4) ^ 2 * h 0) + (2 : ℝ) * (v 2 * v 4 * h 1) + (-4 : ℝ) * (v 2 * v 4 * h 0) + -((v 2) ^ 2 * h 0) + (2 : ℝ) * (v 1 * v 4 * h 1) + (-2 : ℝ) * (v 1 * v 4 * h 0) + v 1 * v 3 * h 1 + (-2 : ℝ) * (v 1 * v 3 * h 0) + -(v 1 * v 2 * h 0) + (2 : ℝ) * ((v 1) ^ 2 * h 0) + (-2 : ℝ) * (v 0 * v 4 * h 1) + (-2 : ℝ) * (v 0 * v 4 * h 0) + -(v 0 * v 3 * h 1) + (-2 : ℝ) * (v 0 * v 2 * h 1) + v 0 * v 2 * h 0 + (2 : ℝ) * (v 0 * v 1 * h 1) + (2 : ℝ) * ((v 0) ^ 2 * h 1) + (-2 : ℝ) * ((v 0) ^ 2 * h 0)) * g1 +
      ((-2 : ℝ) * (v 0 * h 0)) * g2
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork100, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork100, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork100, CodedBimolNetwork.toNetwork,
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
    have g0 : v 3 + -(v 1) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : (4 : ℝ) * (v 4) + v 3 + v 2 = 0 := by
      nlinarith [hg1]
    have g2 : (2 : ℝ) * (v 4) + v 3 + v 2 + -(v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : (-2 : ℝ) * (v 4) + -(v 3) + -(v 2) + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork100, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -(v 1 * (v 3) ^ 2 * h 1) + v 1 * (v 3) ^ 2 * h 0 + -(v 1 * v 2 * v 3 * h 1) + (-8 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (-2 : ℝ) * ((v 1) ^ 2 * v 3 * h 0) + v 0 * (v 3) ^ 2 * h 1 + -(v 0 * (v 3) ^ 2 * h 0) + v 0 * v 2 * v 3 * h 1 + (8 : ℝ) * (v 0 * v 1 * v 4 * h 1) + (2 : ℝ) * (v 0 * v 1 * v 3 * h 0) = 0 := by
      linear_combination
        ((-2 : ℝ) * (v 1 * v 3 * h 1) + (-2 : ℝ) * (v 1 * v 2 * h 1) + (-8 : ℝ) * (v 0 * v 4 * h 1)) * g0 +
      (-(v 1 * v 3 * h 1) + -(v 1 * v 3 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * h 1) + (3 : ℝ) * (v 0 * v 3 * h 1) + v 0 * v 3 * h 0 + (-2 : ℝ) * ((v 0) ^ 2 * h 1)) * g1 +
      (-(v 2 * v 3 * h 0) + (4 : ℝ) * (v 1 * v 3 * h 1) + (2 : ℝ) * (v 1 * v 3 * h 0) + (-2 : ℝ) * (v 0 * v 3 * h 1) + (-2 : ℝ) * (v 0 * v 2 * h 1)) * g2 +
      (-(v 2 * v 3 * h 0) + (2 : ℝ) * (v 1 * v 3 * h 1) + (2 : ℝ) * (v 0 * v 3 * h 0) + (-2 : ℝ) * (v 0 * v 2 * h 1)) * g3
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork100, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork100, CodedBimolNetwork.toNetwork,
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

theorem cubicResidualNetwork100_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork100.toNetwork := by
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
  simp [cubicResidualNetwork100, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork100_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork100.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork100_jacobianNonzero
    cubicResidualNetwork100_fourCharts

def cubicResidualNetwork101 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xy, .yy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork101_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork101.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork101, CodedBimolNetwork.toNetwork,
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
    have g2 : (-4 : ℝ) * (v 1 * v 4) + v 1 * v 3 + -(v 1 * v 2) + (4 : ℝ) * (v 0 * v 4) + -(v 0 * v 3) + v 0 * v 2 = 0 := by
      nlinarith [hdet]
    simp [-mul_eq_zero, cubicResidualNetwork101, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + -(v 1 * v 2 * v 3 * h 1) + (4 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + -((v 1) ^ 2 * v 3 * h 0) + -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 + v 0 * v 2 * v 3 * h 1 + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) + (v 0) ^ 2 * v 3 * h 0 = 0 := by
      linear_combination
        ((-4 : ℝ) * ((v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 2 * v 4 * h 0) + v 2 * v 3 * h 1 + -((v 2) ^ 2 * h 1) + -((v 2) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 3 * h 1) + (3 : ℝ) * (v 1 * v 3 * h 0) + (2 : ℝ) * (v 1 * v 2 * h 1) + (4 : ℝ) * ((v 1) ^ 2 * h 1) + (4 : ℝ) * ((v 1) ^ 2 * h 0) + (-8 : ℝ) * (v 0 * v 4 * h 0) + (2 : ℝ) * (v 0 * v 3 * h 1) + (-2 : ℝ) * (v 0 * v 2 * h 1) + -(v 0 * v 2 * h 0) + (4 : ℝ) * (v 0 * v 1 * h 1) + (-4 : ℝ) * (v 0 * v 1 * h 0)) * g0 +
      ((-4 : ℝ) * ((v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 2 * v 4 * h 0) + v 2 * v 3 * h 1 + -((v 2) ^ 2 * h 1) + -((v 2) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 4 * h 0) + (2 : ℝ) * (v 1 * v 3 * h 0) + -(v 1 * v 2 * h 0) + (2 : ℝ) * ((v 1) ^ 2 * h 1) + (2 : ℝ) * ((v 1) ^ 2 * h 0) + (-6 : ℝ) * (v 0 * v 4 * h 0) + v 0 * v 3 * h 0 + (4 : ℝ) * (v 0 * v 1 * h 1) + (2 : ℝ) * ((v 0) ^ 2 * h 1) + (-2 : ℝ) * ((v 0) ^ 2 * h 0)) * g1 +
      (-(v 3 * h 1) + v 2 * h 1 + (-3 : ℝ) * (v 0 * h 0)) * g2
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork101, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork101, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork101, CodedBimolNetwork.toNetwork,
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
    have g0 : -(v 3) + -(v 1) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : (4 : ℝ) * (v 4) + -(v 3) + v 2 = 0 := by
      nlinarith [hg1]
    have g2 : (2 : ℝ) * (v 4) + -(v 3) + v 2 + -(v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork101, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -(v 1 * (v 3) ^ 2 * h 1) + v 1 * (v 3) ^ 2 * h 0 + v 1 * v 2 * v 3 * h 1 + (-8 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (2 : ℝ) * ((v 1) ^ 2 * v 3 * h 0) + v 0 * (v 3) ^ 2 * h 1 + -(v 0 * (v 3) ^ 2 * h 0) + -(v 0 * v 2 * v 3 * h 1) + (8 : ℝ) * (v 0 * v 1 * v 4 * h 1) + (-2 : ℝ) * (v 0 * v 1 * v 3 * h 0) = 0 := by
      linear_combination
        (-((v 3) ^ 2 * h 1) + v 2 * v 3 * h 1 + (-2 : ℝ) * (v 1 * v 3 * h 1) + (-2 : ℝ) * (v 1 * v 2 * h 1) + (8 : ℝ) * (v 0 * v 1 * h 1)) * g0 +
      (-((v 3) ^ 2 * h 1) + (-2 : ℝ) * ((v 1) ^ 2 * h 1) + (6 : ℝ) * (v 0 * v 1 * h 1)) * g1 +
      ((v 3) ^ 2 * h 0 + (-4 : ℝ) * (v 1 * v 3 * h 1) + (2 : ℝ) * (v 1 * v 3 * h 0) + (-8 : ℝ) * (v 0 * v 1 * h 1)) * g2 +
      ((-2 : ℝ) * ((v 3) ^ 2 * h 1) + (v 3) ^ 2 * h 0 + (-4 : ℝ) * (v 1 * v 3 * h 1) + (2 : ℝ) * (v 1 * v 3 * h 0)) * g3
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork101, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork101, CodedBimolNetwork.toNetwork,
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

theorem cubicResidualNetwork101_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork101.toNetwork := by
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
  simp [cubicResidualNetwork101, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork101_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork101.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork101_jacobianNonzero
    cubicResidualNetwork101_fourCharts

def cubicResidualNetwork102 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xy, .yy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork102_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork102.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork102, CodedBimolNetwork.toNetwork,
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
    have g0 : (2 : ℝ) * (v 4) + -(v 3) + (2 : ℝ) * (v 2) + -(v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g1 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [heq1]
    have g2 : -(v 2 * v 3) + (-4 : ℝ) * (v 1 * v 4) + v 1 * v 3 + (-3 : ℝ) * (v 1 * v 2) + (4 : ℝ) * (v 0 * v 4) + -(v 0 * v 3) + v 0 * v 2 = 0 := by
      nlinarith [hdet]
    have g3 : (-4 : ℝ) * (v 1 * (v 3) ^ 2 * v 4) + (2 : ℝ) * (v 1 * (v 3) ^ 3) + (-4 : ℝ) * (v 1 * v 2 * (v 3) ^ 2) + (2 : ℝ) * ((v 1) ^ 2 * (v 3) ^ 2) + (-4 : ℝ) * ((v 1) ^ 2 * v 2 * v 3) + (4 : ℝ) * ((v 1) ^ 3 * v 4) + (4 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (-2 : ℝ) * (v 0 * (v 3) ^ 3) + (4 : ℝ) * (v 0 * v 2 * (v 3) ^ 2) + (4 : ℝ) * (v 0 * (v 1) ^ 2 * v 4) + (-2 : ℝ) * ((v 0) ^ 2 * (v 3) ^ 2) + (4 : ℝ) * ((v 0) ^ 2 * v 2 * v 3) + (-4 : ℝ) * ((v 0) ^ 2 * v 1 * v 4) + (-4 : ℝ) * ((v 0) ^ 3 * v 4) = 0 := by
      nlinarith [hfold]
    have g4 : (4 : ℝ) * (v 4 * h 1) + -(v 3 * h 1) + -(v 3 * h 0) + (-4 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + (2 : ℝ) * (v 2 * h 1) + (-4 : ℝ) * (v 2 * (v 3) ^ 2) + -(v 1 * h 0) + (2 : ℝ) * (v 1 * (v 3) ^ 2) + (-4 : ℝ) * (v 1 * v 2 * v 3) + (4 : ℝ) * ((v 1) ^ 2 * v 4) + -(v 0 * h 0) + (2 : ℝ) * (v 0 * (v 3) ^ 2) + (-4 : ℝ) * (v 0 * v 2 * v 3) + (8 : ℝ) * (v 0 * v 1 * v 4) + (4 : ℝ) * ((v 0) ^ 2 * v 4) = 0 := by
      nlinarith [hc0]
    have g5 : (-4 : ℝ) * (v 4 * h 1) + v 3 * h 1 + v 3 * h 0 + (4 : ℝ) * ((v 3) ^ 2 * v 4) + (-2 : ℝ) * ((v 3) ^ 3) + -(v 2 * h 1) + (4 : ℝ) * (v 2 * (v 3) ^ 2) + (2 : ℝ) * (v 1 * h 0) + (-2 : ℝ) * (v 1 * (v 3) ^ 2) + (4 : ℝ) * (v 1 * v 2 * v 3) + (-4 : ℝ) * ((v 1) ^ 2 * v 4) + (-2 : ℝ) * (v 0 * (v 3) ^ 2) + (4 : ℝ) * (v 0 * v 2 * v 3) + (-8 : ℝ) * (v 0 * v 1 * v 4) + (-4 : ℝ) * ((v 0) ^ 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork102, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 2 * v 3 * h 1) + (4 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + -((v 1) ^ 2 * v 3 * h 0) + -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 + (2 : ℝ) * (v 0 * v 2 * v 3 * h 1) + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) + (v 0) ^ 2 * v 3 * h 0 = 0 := by
      linear_combination
        ((-28 : ℝ) * ((v 4) ^ 2 * h 1) + (12 : ℝ) * ((v 4) ^ 2 * h 0) + (8 : ℝ) * (v 3 * v 4 * h 1) + (2 : ℝ) * (v 2 * v 4 * h 1) + v 2 * v 3 * h 0 + (v 2) ^ 2 * h 1 + (-3 : ℝ) * ((v 2) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 3 * h 1) + (3 : ℝ) * (v 1 * v 3 * h 0) + (4 : ℝ) * ((v 1) ^ 2 * h 0) + (-3 : ℝ) * (v 0 * v 3 * h 0) + (2 : ℝ) * (v 0 * v 2 * h 0) + (-4 : ℝ) * (v 0 * v 1 * h 1) + (-4 : ℝ) * (v 0 * v 1 * h 0)) * g0 +
      ((-28 : ℝ) * ((v 4) ^ 2 * h 1) + (12 : ℝ) * ((v 4) ^ 2 * h 0) + (8 : ℝ) * (v 3 * v 4 * h 1) + (-12 : ℝ) * (v 2 * v 4 * h 1) + (6 : ℝ) * (v 2 * v 4 * h 0) + (3 : ℝ) * (v 2 * v 3 * h 1) + (4 : ℝ) * (v 2 * v 3 * h 0) + (-7 : ℝ) * ((v 2) ^ 2 * h 1) + (-6 : ℝ) * ((v 2) ^ 2 * h 0) + (2 : ℝ) * (v 1 * v 4 * h 1) + (6 : ℝ) * (v 1 * v 4 * h 0) + -(v 1 * v 3 * h 1) + (2 : ℝ) * (v 1 * v 3 * h 0) + (-3 : ℝ) * (v 1 * v 2 * h 0) + (2 : ℝ) * ((v 1) ^ 2 * h 0) + (-2 : ℝ) * (v 0 * v 4 * h 1) + (-6 : ℝ) * (v 0 * v 4 * h 0) + -(v 0 * v 3 * h 1) + (-2 : ℝ) * (v 0 * v 3 * h 0) + (11 : ℝ) * (v 0 * v 2 * h 0) + (-2 : ℝ) * (v 0 * v 1 * h 1) + (-2 : ℝ) * ((v 0) ^ 2 * h 1) + (-2 : ℝ) * ((v 0) ^ 2 * h 0)) * g1 +
      ((-5 : ℝ) * (v 2 * h 1) + (-5 : ℝ) * (v 2 * h 0) + (-2 : ℝ) * (v 0 * h 1) + (-12 : ℝ) * ((v 3) ^ 2 * v 4) + (6 : ℝ) * ((v 3) ^ 3) + (-12 : ℝ) * (v 2 * (v 3) ^ 2) + (6 : ℝ) * (v 1 * (v 3) ^ 2) + (-12 : ℝ) * (v 1 * v 2 * v 3) + (12 : ℝ) * ((v 1) ^ 2 * v 4) + (6 : ℝ) * (v 0 * (v 3) ^ 2) + (-12 : ℝ) * (v 0 * v 2 * v 3) + (24 : ℝ) * (v 0 * v 1 * v 4) + (12 : ℝ) * ((v 0) ^ 2 * v 4)) * g2 +
      ((4 : ℝ) * (v 4) + (-3 : ℝ) * (v 3) + (9 : ℝ) * (v 2)) * g3 +
      ((-32 : ℝ) * (v 2 * v 4) + (3 : ℝ) * (v 2 * v 3) + (-9 : ℝ) * ((v 2) ^ 2) + (4 : ℝ) * (v 0 * v 4)) * g4 +
      ((-32 : ℝ) * (v 2 * v 4) + (-9 : ℝ) * ((v 2) ^ 2) + (-8 : ℝ) * (v 1 * v 4) + (12 : ℝ) * (v 0 * v 4) + (-6 : ℝ) * (v 0 * v 2)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork102, CodedBimolNetwork.toNetwork,
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
    have g0 : -(v 3) + -(v 1) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : v 3 + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [hg1]
    have g2 : (2 : ℝ) * (v 4) + -(v 3) + (2 : ℝ) * (v 2) + -(v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork102, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 2 * (v 3) ^ 2 * h 1 + -(v 2 * (v 3) ^ 2 * h 0) + (-2 : ℝ) * ((v 2) ^ 2 * v 3 * h 1) + (4 : ℝ) * (v 1 * v 2 * v 4 * h 1) + -(v 1 * v 2 * v 3 * h 0) + (4 : ℝ) * (v 0 * v 2 * v 4 * h 1) + -(v 0 * v 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 2 * v 4 * h 1) + (4 : ℝ) * (v 1 * v 2 * h 1) + (-2 : ℝ) * (v 1 * v 2 * h 0) + (4 : ℝ) * (v 0 * v 2 * h 1) + (-4 : ℝ) * ((v 0) ^ 2 * h 1)) * g0 +
      ((-4 : ℝ) * (v 2 * v 4 * h 1) + v 2 * v 3 * h 1 + -(v 2 * v 3 * h 0) + (-2 : ℝ) * ((v 2) ^ 2 * h 1) + (6 : ℝ) * (v 1 * v 2 * h 1) + -(v 1 * v 2 * h 0) + (4 : ℝ) * (v 0 * v 2 * h 1) + -(v 0 * v 2 * h 0) + (-4 : ℝ) * ((v 0) ^ 2 * h 1)) * g1 +
      ((4 : ℝ) * ((v 0) ^ 2 * h 1)) * g2 +
      ((-4 : ℝ) * (v 1 * v 2 * h 1) + (4 : ℝ) * ((v 0) ^ 2 * h 1)) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork102, CodedBimolNetwork.toNetwork,
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
    have g0 : -(v 3) + -(v 1) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : (4 : ℝ) * (v 4) + -(v 3) + (2 : ℝ) * (v 2) = 0 := by
      nlinarith [hg1]
    have g2 : (2 : ℝ) * (v 4) + -(v 3) + (2 : ℝ) * (v 2) + -(v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [heq1]
    have g5 : (-4 : ℝ) * (v 1 * (v 3) ^ 2 * v 4) + (2 : ℝ) * (v 1 * (v 3) ^ 3) + (-2 : ℝ) * (v 1 * v 2 * (v 3) ^ 2) + (4 : ℝ) * ((v 1) ^ 2 * (v 3) ^ 2) + (-4 : ℝ) * ((v 1) ^ 2 * v 2 * v 3) + (16 : ℝ) * ((v 1) ^ 3 * v 4) + (4 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (-2 : ℝ) * (v 0 * (v 3) ^ 3) + (2 : ℝ) * (v 0 * v 2 * (v 3) ^ 2) + (-4 : ℝ) * (v 0 * v 1 * (v 3) ^ 2) + (4 : ℝ) * (v 0 * v 1 * v 2 * v 3) + (-16 : ℝ) * (v 0 * (v 1) ^ 2 * v 4) = 0 := by
      nlinarith [hfold]
    have g6 : (4 : ℝ) * (v 4 * h 1) + -(v 3 * h 1) + -(v 3 * h 0) + (-4 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + (2 : ℝ) * (v 2 * h 1) + (-2 : ℝ) * (v 2 * (v 3) ^ 2) + -(v 1 * h 0) + (4 : ℝ) * (v 1 * (v 3) ^ 2) + (-4 : ℝ) * (v 1 * v 2 * v 3) + (16 : ℝ) * ((v 1) ^ 2 * v 4) + -(v 0 * h 0) = 0 := by
      nlinarith [hc0]
    have g7 : (-4 : ℝ) * (v 4 * h 1) + v 3 * h 1 + v 3 * h 0 + (4 : ℝ) * ((v 3) ^ 2 * v 4) + (-2 : ℝ) * ((v 3) ^ 3) + -(v 2 * h 1) + (2 : ℝ) * (v 2 * (v 3) ^ 2) + (2 : ℝ) * (v 1 * h 0) + (-4 : ℝ) * (v 1 * (v 3) ^ 2) + (4 : ℝ) * (v 1 * v 2 * v 3) + (-16 : ℝ) * ((v 1) ^ 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork102, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -(v 1 * (v 3) ^ 2 * h 1) + v 1 * (v 3) ^ 2 * h 0 + v 1 * v 2 * v 3 * h 1 + (-8 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (2 : ℝ) * ((v 1) ^ 2 * v 3 * h 0) + v 0 * (v 3) ^ 2 * h 1 + -(v 0 * (v 3) ^ 2 * h 0) + -(v 0 * v 2 * v 3 * h 1) + (8 : ℝ) * (v 0 * v 1 * v 4 * h 1) + (-2 : ℝ) * (v 0 * v 1 * v 3 * h 0) = 0 := by
      linear_combination
        ((16 : ℝ) * ((v 4) ^ 2 * h 0) + (8 : ℝ) * (v 2 * v 4 * h 0) + ((10 : ℝ) / 3) * (v 2 * v 3 * h 0) + (8 : ℝ) * (v 1 * v 4 * h 0) + v 1 * v 3 * h 1 + ((28 : ℝ) / 3) * (v 1 * v 2 * h 0) + ((4 : ℝ) / 3) * ((v 1) ^ 2 * h 1) + (-8 : ℝ) * ((v 1) ^ 2 * h 0) + ((-56 : ℝ) / 3) * (v 0 * v 4 * h 1) + (2 : ℝ) * (v 0 * v 3 * h 1) + ((-8 : ℝ) / 3) * (v 0 * v 2 * h 1) + ((-4 : ℝ) / 3) * (v 0 * v 1 * h 1) + ((-20 : ℝ) / 3) * ((v 0) ^ 2 * h 1)) * g0 +
      (((16 : ℝ) / 3) * ((v 4) ^ 2 * h 0) + ((13 : ℝ) / 3) * (v 3 * v 4 * h 0) + ((1 : ℝ) / 2) * ((v 3) ^ 2 * h 0) + ((25 : ℝ) / 6) * (v 2 * v 3 * h 0) + ((-4 : ℝ) / 3) * (v 1 * v 4 * h 0) + v 1 * v 2 * h 1 + ((-13 : ℝ) / 3) * ((v 1) ^ 2 * h 1) + ((-14 : ℝ) / 3) * ((v 1) ^ 2 * h 0) + (4 : ℝ) * (v 0 * v 4 * h 0) + ((-19 : ℝ) / 3) * (v 0 * v 3 * h 1) + v 0 * v 3 * h 0 + ((14 : ℝ) / 3) * (v 0 * v 1 * h 0) + ((-25 : ℝ) / 3) * ((v 0) ^ 2 * h 1)) * g1 +
      (((-4 : ℝ) / 3) * (v 2 * v 3 * h 0) + ((32 : ℝ) / 3) * (v 1 * v 4 * h 0) + ((32 : ℝ) / 3) * ((v 1) ^ 2 * h 0) + ((17 : ℝ) / 3) * (v 0 * v 3 * h 1) + ((20 : ℝ) / 3) * ((v 0) ^ 2 * h 1)) * g2 +
      (((32 : ℝ) / 3) * ((v 4) ^ 2 * h 0) + ((10 : ℝ) / 3) * (v 3 * v 4 * h 0) + ((1 : ℝ) / 2) * ((v 3) ^ 2 * h 0) + ((17 : ℝ) / 3) * (v 2 * v 3 * h 0) + ((32 : ℝ) / 3) * (v 1 * v 4 * h 0) + (2 : ℝ) * (v 1 * v 2 * h 1) + ((2 : ℝ) / 3) * ((v 1) ^ 2 * h 1) + ((8 : ℝ) / 3) * ((v 1) ^ 2 * h 0) + ((7 : ℝ) / 3) * (v 0 * v 3 * h 1) + ((-2 : ℝ) / 3) * ((v 0) ^ 2 * h 1)) * g3 +
      (((-8 : ℝ) / 3) * (v 1)) * g5 +
      (((8 : ℝ) / 3) * ((v 1) ^ 2)) * g6 +
      (((8 : ℝ) / 3) * (v 0 * v 1)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork102, CodedBimolNetwork.toNetwork,
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
    have g0 : -(v 3) + -(v 1) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : (4 : ℝ) * (v 4) + -(v 3) + (2 : ℝ) * (v 2) = 0 := by
      nlinarith [hg1]
    have g2 : v 3 + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [hg2]
    have g3 : (2 : ℝ) * (v 4) + -(v 3) + (2 : ℝ) * (v 2) + -(v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g4 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork102, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -(v 2 * (v 3) ^ 2 * h 1) + v 2 * (v 3) ^ 2 * h 0 + (v 2) ^ 2 * v 3 * h 1 + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((-2 : ℝ) * (v 1 * v 2 * h 1)) * g0 +
      ((-2 : ℝ) * (v 1 * v 2 * h 1)) * g1 +
      (-(v 2 * v 3 * h 1) + v 2 * v 3 * h 0 + (v 2) ^ 2 * h 1 + (-2 : ℝ) * (v 1 * v 2 * h 1)) * g2 +
      ((2 : ℝ) * (v 1 * v 2 * h 1)) * g3 +
      ((2 : ℝ) * (v 1 * v 2 * h 1)) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork102_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork102.toNetwork := by
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
  simp [cubicResidualNetwork102, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork102_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork102.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork102_jacobianNonzero
    cubicResidualNetwork102_fourCharts

def cubicResidualNetwork103 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.y, .yy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork103_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork103.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork103, CodedBimolNetwork.toNetwork,
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
    have g0 : v 3 + -(v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g1 : (-2 : ℝ) * (v 4) + -(v 3) + v 2 + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [heq1]
    have g2 : (-4 : ℝ) * (v 3 * v 4) + v 2 * v 3 + (4 : ℝ) * (v 1 * v 4) + -(v 1 * v 3) + -(v 1 * v 2) + (4 : ℝ) * (v 0 * v 4) + v 0 * v 3 + -(v 0 * v 2) = 0 := by
      nlinarith [hdet]
    simp [-mul_eq_zero, cubicResidualNetwork103, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (-4 : ℝ) * ((v 3) ^ 2 * v 4 * h 1) + (8 : ℝ) * (v 1 * v 3 * v 4 * h 1) + v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + (-4 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (v 1) ^ 2 * v 3 * h 0 + (8 : ℝ) * (v 0 * v 3 * v 4 * h 1) + -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 + (-8 : ℝ) * (v 0 * v 1 * v 4 * h 1) + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) + -((v 0) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 3 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 4 * h 0) + v 1 * v 3 * h 1 + v 1 * v 2 * h 1 + -(v 1 * v 2 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * h 0) + -(v 0 * v 3 * h 1) + v 0 * v 3 * h 0 + v 0 * v 2 * h 1) * g0 +
      (v 1 * v 3 * h 0 + -((v 1) ^ 2 * h 0) + -(v 0 * v 1 * h 0)) * g1 +
      (-(v 1 * h 1) + -(v 0 * h 1)) * g2
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork103, CodedBimolNetwork.toNetwork,
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
    have g0 : v 3 + -(v 1) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : -(v 3) + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [hg1]
    have g2 : v 3 + -(v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g5 : (12 : ℝ) * ((v 3) ^ 3 * v 4) + (-2 : ℝ) * (v 2 * (v 3) ^ 3) + (-16 : ℝ) * (v 1 * (v 3) ^ 2 * v 4) + (2 : ℝ) * (v 1 * v 2 * (v 3) ^ 2) + (4 : ℝ) * ((v 1) ^ 2 * v 3 * v 4) + (-16 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (2 : ℝ) * (v 0 * v 2 * (v 3) ^ 2) + (8 : ℝ) * (v 0 * v 1 * v 3 * v 4) + (4 : ℝ) * ((v 0) ^ 2 * v 3 * v 4) = 0 := by
      nlinarith [hfold]
    have g6 : v 3 * h 1 + v 3 * h 0 + (-2 : ℝ) * ((v 3) ^ 3) + -(v 1 * h 0) + (2 : ℝ) * (v 1 * (v 3) ^ 2) + -(v 0 * h 0) + (2 : ℝ) * (v 0 * (v 3) ^ 2) = 0 := by
      nlinarith [hc0]
    simp [-mul_eq_zero, cubicResidualNetwork103, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (-8 : ℝ) * ((v 3) ^ 2 * v 4 * h 1) + (4 : ℝ) * ((v 3) ^ 2 * v 4 * h 0) + v 2 * (v 3) ^ 2 * h 1 + -(v 2 * (v 3) ^ 2 * h 0) + (4 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 3 * v 4 * h 0) + v 1 * v 2 * v 3 * h 0 + (4 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (-4 : ℝ) * (v 0 * v 3 * v 4 * h 0) + v 0 * v 2 * v 3 * h 0 = 0 := by
      linear_combination
        ((-2 : ℝ) * (v 0 * v 4 * h 0)) * g0 +
      ((2 : ℝ) * (v 3 * v 4 * h 1) + (-10 : ℝ) * (v 3 * v 4 * h 0) + (-2 : ℝ) * (v 1 * v 4 * h 1) + (10 : ℝ) * (v 1 * v 4 * h 0) + (-2 : ℝ) * (v 0 * v 4 * h 1) + (10 : ℝ) * (v 0 * v 4 * h 0)) * g1 +
      ((-2 : ℝ) * (v 2 * v 3 * h 0) + (-4 : ℝ) * (v 1 * v 4 * h 1) + (18 : ℝ) * (v 1 * v 4 * h 0)) * g2 +
      (-(v 3)) * g5 +
      ((-6 : ℝ) * (v 3 * v 4) + v 2 * v 3 + (2 : ℝ) * (v 1 * v 4) + (2 : ℝ) * (v 0 * v 4)) * g6
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork103, CodedBimolNetwork.toNetwork,
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
    have g0 : v 3 + -(v 1) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : v 3 = 0 := by
      nlinarith [hg1]
    have g2 : v 3 + -(v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : (-2 : ℝ) * (v 4) + -(v 3) + v 2 + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork103, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (4 : ℝ) * ((v 3) ^ 2 * v 4 * h 1) + (-16 : ℝ) * (v 1 * v 3 * v 4 * h 1) + -(v 1 * (v 3) ^ 2 * h 1) + v 1 * (v 3) ^ 2 * h 0 + v 1 * v 2 * v 3 * h 1 + (8 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (-2 : ℝ) * ((v 1) ^ 2 * v 3 * h 0) + v 0 * (v 3) ^ 2 * h 1 + -(v 0 * (v 3) ^ 2 * h 0) + -(v 0 * v 2 * v 3 * h 1) + (8 : ℝ) * (v 0 * v 1 * v 4 * h 1) + (2 : ℝ) * (v 0 * v 1 * v 3 * h 0) = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 1 * v 2 * h 1) + (-8 : ℝ) * ((v 1) ^ 2 * h 1) + (8 : ℝ) * (v 0 * v 1 * h 1)) * g0 +
      ((4 : ℝ) * (v 3 * v 4 * h 1) + (-16 : ℝ) * (v 1 * v 4 * h 1) + -(v 1 * v 3 * h 1) + v 1 * v 3 * h 0 + (5 : ℝ) * (v 1 * v 2 * h 1) + (4 : ℝ) * ((v 1) ^ 2 * h 1) + (-2 : ℝ) * ((v 1) ^ 2 * h 0) + (8 : ℝ) * (v 0 * v 4 * h 1) + v 0 * v 3 * h 1 + -(v 0 * v 3 * h 0) + (-5 : ℝ) * (v 0 * v 2 * h 1) + (-8 : ℝ) * (v 0 * v 1 * h 1) + (2 : ℝ) * (v 0 * v 1 * h 0) + (4 : ℝ) * ((v 0) ^ 2 * h 1)) * g1 +
      ((-8 : ℝ) * (v 0 * v 4 * h 1) + (4 : ℝ) * (v 0 * v 2 * h 1)) * g2 +
      ((-4 : ℝ) * ((v 1) ^ 2 * h 1) + (4 : ℝ) * ((v 0) ^ 2 * h 1)) * g3
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork103, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork103, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (16 : ℝ) * (v 3 * (v 4) ^ 2 * h 1) + (8 : ℝ) * ((v 3) ^ 2 * v 4 * h 1) + (-4 : ℝ) * ((v 3) ^ 2 * v 4 * h 0) + (-8 : ℝ) * (v 2 * v 3 * v 4 * h 1) + -(v 2 * (v 3) ^ 2 * h 1) + v 2 * (v 3) ^ 2 * h 0 + (v 2) ^ 2 * v 3 * h 1 + (-8 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (8 : ℝ) * (v 1 * v 3 * v 4 * h 0) + (-2 : ℝ) * (v 1 * v 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((16 : ℝ) * ((v 4) ^ 2 * h 1) + (8 : ℝ) * (v 3 * v 4 * h 1) + (-4 : ℝ) * (v 3 * v 4 * h 0) + (-8 : ℝ) * (v 2 * v 4 * h 1) + -(v 2 * v 3 * h 1) + v 2 * v 3 * h 0 + (v 2) ^ 2 * h 1 + (-8 : ℝ) * (v 1 * v 4 * h 1) + (8 : ℝ) * (v 1 * v 4 * h 0) + (-2 : ℝ) * (v 1 * v 2 * h 0)) * g1
    nlinarith [hcertificate]

theorem cubicResidualNetwork103_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork103.toNetwork := by
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
  simp [cubicResidualNetwork103, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork103_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork103.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork103_jacobianNonzero
    cubicResidualNetwork103_fourCharts

def cubicResidualNetwork104 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xx, .zero), (.xy, .y)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork104_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork104.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork104, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork104, CodedBimolNetwork.toNetwork,
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
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork104, CodedBimolNetwork.toNetwork,
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
    have g3 : v 2 + -(v 1) = 0 := by
      nlinarith [heq1]
    have g7 : v 2 * h 1 + -(v 1 * h 1) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork104, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 2 * (v 4) ^ 2 * h 1 + -(v 2 * (v 4) ^ 2 * h 0) + -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + -(v 1 * v 2 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (v 1) ^ 2 * v 4 * h 1 + (4 : ℝ) * ((v 1) ^ 2 * v 3 * h 0) + -(v 0 * v 2 * v 4 * h 0) + v 0 * v 1 * v 4 * h 0 = 0 := by
      linear_combination
        ((v 4) ^ 2 * h 1 + -((v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 1 * v 3 * h 0) + -(v 0 * v 4 * h 0)) * g3 +
      (-(v 1 * v 4)) * g7
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork104, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork104, CodedBimolNetwork.toNetwork,
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
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork104, CodedBimolNetwork.toNetwork,
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
    have g0 : -(v 4) + (-4 : ℝ) * (v 3) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : -(v 4) + v 1 = 0 := by
      nlinarith [hg1]
    have g7 : -(v 4 * h 1) + -(v 4 * h 0) + (-4 : ℝ) * (v 3 * h 0) + (-4 : ℝ) * ((v 2) ^ 2 * v 3) + v 1 * h 1 + (8 : ℝ) * (v 1 * v 2 * v 3) + (-4 : ℝ) * ((v 1) ^ 2 * v 3) + -(v 0 * h 0) = 0 := by
      nlinarith [hc0]
    have g8 : v 2 * h 1 + -(v 1 * h 1) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork104, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -((v 2) ^ 2 * v 4 * h 1) + (-4 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + (2 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (8 : ℝ) * (v 1 * v 2 * v 3 * h 0) + -((v 1) ^ 2 * v 4 * h 1) + (-4 : ℝ) * ((v 1) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        (-((h 0) ^ 2)) * g0 +
      (-(h 0 * h 1)) * g1 +
      (h 0) * g7 +
      (-(v 2 * v 4) + v 1 * v 4) * g8
    nlinarith [hcertificate]

theorem cubicResidualNetwork104_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork104.toNetwork := by
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
  simp [cubicResidualNetwork104, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork104_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork104.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork104_jacobianNonzero
    cubicResidualNetwork104_fourCharts

def cubicResidualNetwork105 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xx, .zero), (.xy, .y)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork105_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork105.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork105, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork105, CodedBimolNetwork.toNetwork,
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
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork105, CodedBimolNetwork.toNetwork,
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
    have g3 : v 2 + -(v 1) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork105, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 2 * (v 4) ^ 2 * h 1 + -(v 2 * (v 4) ^ 2 * h 0) + -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + (-2 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (2 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (8 : ℝ) * ((v 1) ^ 2 * v 3 * h 0) + -(v 0 * v 2 * v 4 * h 0) + v 0 * v 1 * v 4 * h 0 = 0 := by
      linear_combination
        ((v 4) ^ 2 * h 1 + -((v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 3 * h 0) + -(v 0 * v 4 * h 0)) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork105, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork105, CodedBimolNetwork.toNetwork,
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
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork105, CodedBimolNetwork.toNetwork,
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
    have g0 : -(v 4) + (-4 : ℝ) * (v 3) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : -(v 4) + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [hg1]
    have g7 : -(v 4 * h 1) + -(v 4 * h 0) + (-4 : ℝ) * (v 3 * h 0) + (-4 : ℝ) * ((v 2) ^ 2 * v 3) + (2 : ℝ) * (v 1 * h 1) + (8 : ℝ) * (v 1 * v 2 * v 3) + (-4 : ℝ) * ((v 1) ^ 2 * v 3) + -(v 0 * h 0) = 0 := by
      nlinarith [hc0]
    have g8 : v 2 * h 1 + -(v 1 * h 1) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork105, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -((v 2) ^ 2 * v 4 * h 1) + (-4 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + (2 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (8 : ℝ) * (v 1 * v 2 * v 3 * h 0) + -((v 1) ^ 2 * v 4 * h 1) + (-4 : ℝ) * ((v 1) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        (-((h 0) ^ 2)) * g0 +
      (-(h 0 * h 1)) * g1 +
      (h 0) * g7 +
      (-(v 2 * v 4) + v 1 * v 4) * g8
    nlinarith [hcertificate]

theorem cubicResidualNetwork105_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork105.toNetwork := by
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
  simp [cubicResidualNetwork105, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork105_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork105.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork105_jacobianNonzero
    cubicResidualNetwork105_fourCharts

end SmallCusp

import proofs.SmallCusp.Obstruction.CubicDegeneracy
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

def cubicResidualNetwork26 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.xy, .yy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork26_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork26.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork26, CodedBimolNetwork.toNetwork,
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
    have g0 : (2 : ℝ) * (v 4) + -(v 3) + (2 : ℝ) * (v 2) + -(v 1) + v 0 = 0 := by
      nlinarith [heq0]
    have g1 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) = 0 := by
      nlinarith [heq1]
    have g2 : -(v 2 * v 3) + (4 : ℝ) * (v 1 * v 4) + -(v 1 * v 3) + v 1 * v 2 = 0 := by
      nlinarith [hdet]
    have g3 : (4 : ℝ) * (v 1 * (v 3) ^ 2 * v 4) + (-2 : ℝ) * (v 1 * (v 3) ^ 3) + (4 : ℝ) * (v 1 * v 2 * (v 3) ^ 2) + (-2 : ℝ) * ((v 1) ^ 2 * (v 3) ^ 2) + (4 : ℝ) * ((v 1) ^ 2 * v 2 * v 3) + (-4 : ℝ) * ((v 1) ^ 3 * v 4) = 0 := by
      nlinarith [hfold]
    have g4 : (4 : ℝ) * (v 4 * h 1) + -(v 3 * h 1) + -(v 3 * h 0) + (-4 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + (2 : ℝ) * (v 2 * h 1) + (-4 : ℝ) * (v 2 * (v 3) ^ 2) + -(v 1 * h 0) + (2 : ℝ) * (v 1 * (v 3) ^ 2) + (-4 : ℝ) * (v 1 * v 2 * v 3) + (4 : ℝ) * ((v 1) ^ 2 * v 4) = 0 := by
      nlinarith [hc0]
    have g5 : (-4 : ℝ) * (v 4 * h 1) + v 3 * h 1 + v 3 * h 0 + (4 : ℝ) * ((v 3) ^ 2 * v 4) + (-2 : ℝ) * ((v 3) ^ 3) + -(v 2 * h 1) + (4 : ℝ) * (v 2 * (v 3) ^ 2) + (-2 : ℝ) * (v 1 * (v 3) ^ 2) + (4 : ℝ) * (v 1 * v 2 * v 3) + (-4 : ℝ) * ((v 1) ^ 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork26, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -(v 1 * (v 3) ^ 2 * h 1) + v 1 * (v 3) ^ 2 * h 0 + (2 : ℝ) * (v 1 * v 2 * v 3 * h 1) + (-4 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (v 1) ^ 2 * v 3 * h 0 = 0 := by
      linear_combination
        ((-8 : ℝ) * ((v 4) ^ 2 * h 1) + (4 : ℝ) * (v 3 * v 4 * h 1) + (-4 : ℝ) * (v 2 * v 4 * h 1) + -(v 2 * v 3 * h 0) + v 1 * v 3 * h 0 + -(v 1 * v 2 * h 0)) * g0 +
      ((-8 : ℝ) * ((v 4) ^ 2 * h 1) + (4 : ℝ) * (v 3 * v 4 * h 1) + (-8 : ℝ) * (v 2 * v 4 * h 1) + -(v 2 * v 3 * h 0) + -(v 1 * v 3 * h 1) + (2 : ℝ) * (v 1 * v 3 * h 0) + (-3 : ℝ) * (v 1 * v 2 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * h 1) + (v 1) ^ 2 * h 0 + (-4 : ℝ) * (v 0 * v 4 * h 1) + (-2 : ℝ) * (v 0 * v 1 * h 0)) * g1 +
      (-(v 2 * h 0) + -(v 1 * h 1) + -(v 0 * h 0)) * g2 +
      ((-2 : ℝ) * (v 4) + -(v 1)) * g3 +
      ((-2 : ℝ) * (v 1 * v 4)) * g4 +
      ((v 1) ^ 2) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork26, CodedBimolNetwork.toNetwork,
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
    have g0 : -(v 3) + -(v 1) = 0 := by
      nlinarith [hg0]
    have g1 : v 3 = 0 := by
      nlinarith [hg1]
    simp [-mul_eq_zero, cubicResidualNetwork26, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 2 * (v 3) ^ 2 * h 1 + -(v 2 * (v 3) ^ 2 * h 0) + (-2 : ℝ) * ((v 2) ^ 2 * v 3 * h 1) + (4 : ℝ) * (v 1 * v 2 * v 4 * h 1) + -(v 1 * v 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 2 * v 4 * h 1)) * g0 +
      ((-4 : ℝ) * (v 2 * v 4 * h 1) + v 2 * v 3 * h 1 + -(v 2 * v 3 * h 0) + (-2 : ℝ) * ((v 2) ^ 2 * h 1) + -(v 1 * v 2 * h 0)) * g1
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork26, CodedBimolNetwork.toNetwork,
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
    have g0 : -(v 3) + -(v 1) = 0 := by
      nlinarith [hg0]
    have g1 : (4 : ℝ) * (v 4) + -(v 3) + (2 : ℝ) * (v 2) = 0 := by
      nlinarith [hg1]
    have g3 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork26, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + -(v 1 * v 2 * v 3 * h 1) = 0 := by
      linear_combination
        ((2 : ℝ) * (v 3 * v 4 * h 1) + -((v 3) ^ 2 * h 1) + (v 3) ^ 2 * h 0 + v 2 * v 3 * h 1) * g0 +
      ((v 3) ^ 2 * h 0 + (2 : ℝ) * (v 1 * v 4 * h 1)) * g1 +
      (-((v 3) ^ 2 * h 1) + (2 : ℝ) * ((v 3) ^ 2 * h 0) + (4 : ℝ) * (v 1 * v 4 * h 1)) * g3
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork26, CodedBimolNetwork.toNetwork,
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
    have g2 : v 3 = 0 := by
      nlinarith [hg2]
    simp [-mul_eq_zero, cubicResidualNetwork26, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -(v 2 * (v 3) ^ 2 * h 1) + v 2 * (v 3) ^ 2 * h 0 + (v 2) ^ 2 * v 3 * h 1 = 0 := by
      linear_combination
        (-(v 2 * v 3 * h 1) + v 2 * v 3 * h 0 + (v 2) ^ 2 * h 1) * g2
    nlinarith [hcertificate]

theorem cubicResidualNetwork26_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork26.toNetwork := by
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
  simp [cubicResidualNetwork26, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork26_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork26.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork26_jacobianNonzero
    cubicResidualNetwork26_fourCharts

def cubicResidualNetwork27 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .xy), (.y, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork27_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork27.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork27, CodedBimolNetwork.toNetwork,
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
    have g0 : -(v 4) + v 2 + -(v 1) + v 0 = 0 := by
      nlinarith [heq0]
    have g1 : -(v 4) + v 3 = 0 := by
      nlinarith [heq1]
    have g2 : -(v 3 * v 4) + v 2 * v 4 + v 1 * v 4 + -(v 1 * v 3) = 0 := by
      nlinarith [hdet]
    have g3 : (2 : ℝ) * (v 1 * (v 4) ^ 3) + (-2 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 1) ^ 2 * (v 4) ^ 2) + (-2 : ℝ) * ((v 1) ^ 2 * v 2 * v 4) = 0 := by
      nlinarith [hfold]
    have g4 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + v 2 * h 1 + (-2 : ℝ) * (v 2 * (v 4) ^ 2) + -(v 1 * h 0) + (2 : ℝ) * (v 1 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * v 2 * v 4) = 0 := by
      nlinarith [hc0]
    simp [-mul_eq_zero, cubicResidualNetwork27, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + -(v 1 * v 2 * v 4 * h 1) + -((v 1) ^ 2 * v 4 * h 0) = 0 := by
      linear_combination
        ((-2 : ℝ) * (v 3 * v 4 * h 1) + (2 : ℝ) * (v 2 * v 3 * h 1)) * g0 +
      ((2 : ℝ) * (v 3 * v 4 * h 1) + (-2 : ℝ) * ((v 2) ^ 2 * h 1) + -(v 1 * v 4 * h 1) + v 1 * v 4 * h 0 + (2 : ℝ) * (v 1 * v 3 * h 1) + -(v 1 * v 2 * h 1) + (v 1) ^ 2 * h 0 + (-2 : ℝ) * (v 0 * v 2 * h 1) + (-2 : ℝ) * (v 0 * v 1 * h 1)) * g1 +
      ((2 : ℝ) * (v 3 * h 1) + (-2 : ℝ) * (v 2 * h 1) + (-2 : ℝ) * (v 0 * h 1)) * g2 +
      (-(v 3)) * g3 +
      (v 1 * v 3) * g4
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork27, CodedBimolNetwork.toNetwork,
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
    have g1 : -(v 4) = 0 := by
      nlinarith [hg1]
    simp [-mul_eq_zero, cubicResidualNetwork27, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 3 * (v 4) ^ 2 * h 1 + -(v 3 * (v 4) ^ 2 * h 0) + -(v 2 * (v 4) ^ 2 * h 1) + v 2 * (v 4) ^ 2 * h 0 + -(v 2 * v 3 * v 4 * h 1) + (v 2) ^ 2 * v 4 * h 1 + -(v 1 * v 3 * v 4 * h 0) + v 1 * v 2 * v 4 * h 0 = 0 := by
      linear_combination
        (-(v 3 * v 4 * h 1) + v 3 * v 4 * h 0 + v 2 * v 4 * h 1 + -(v 2 * v 4 * h 0) + v 2 * v 3 * h 1 + -((v 2) ^ 2 * h 1) + v 1 * v 3 * h 0 + -(v 1 * v 2 * h 0)) * g1
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork27, CodedBimolNetwork.toNetwork,
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
    have g0 : -(v 4) + -(v 1) = 0 := by
      nlinarith [hg0]
    have g1 : -(v 4) + v 2 = 0 := by
      nlinarith [hg1]
    have g2 : -(v 4) + v 2 + -(v 1) + v 0 = 0 := by
      nlinarith [heq0]
    have g3 : -(v 4) + v 3 = 0 := by
      nlinarith [heq1]
    have g6 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + v 2 * h 1 + -(v 1 * h 0) = 0 := by
      nlinarith [hc0]
    have g7 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + v 3 * h 1 + (-2 : ℝ) * (v 3 * (v 4) ^ 2) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork27, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + -(v 1 * v 3 * v 4 * h 1) = 0 := by
      linear_combination
        (v 3 * v 4 * h 0 + (v 3) ^ 2 * h 1 + -((v 3) ^ 2 * h 0) + -((v 2) ^ 2 * h 1) + v 1 * v 4 * h 0 + -(v 1 * v 3 * h 0) + -(v 1 * v 2 * h 1) + (v 1) ^ 2 * h 1 + v 0 * v 3 * h 1 + -(v 0 * v 1 * h 1)) * g0 +
      ((-2 : ℝ) * (v 3 * v 4 * h 1) + -(v 3 * v 4 * h 0) + (v 3) ^ 2 * h 0 + -(v 2 * v 3 * h 1) + -((v 2) ^ 2 * h 1) + -(v 1 * v 4 * h 1) + -(v 0 * v 3 * h 1) + -(v 0 * v 2 * h 1)) * g1 +
      ((v 2) ^ 2 * h 1 + -((v 1) ^ 2 * h 1)) * g2 +
      ((2 : ℝ) * (v 3 * v 4 * h 1) + (v 3) ^ 2 * h 1 + -(v 2 * v 3 * h 1) + -(v 2 * v 3 * h 0) + (v 2) ^ 2 * h 1 + v 1 * v 3 * h 1 + -((v 1) ^ 2 * h 0) + v 0 * v 2 * h 1 + v 0 * v 1 * h 1) * g3 +
      ((v 3) ^ 2) * g6 +
      (-((v 3) ^ 2)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork27, CodedBimolNetwork.toNetwork,
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
    have g2 : -(v 4) = 0 := by
      nlinarith [hg2]
    simp [-mul_eq_zero, cubicResidualNetwork27, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 3 * (v 4) ^ 2 * h 1 + -(v 3 * (v 4) ^ 2 * h 0) + -((v 3) ^ 2 * v 4 * h 1) + -(v 2 * (v 4) ^ 2 * h 1) + v 2 * (v 4) ^ 2 * h 0 + v 2 * v 3 * v 4 * h 1 = 0 := by
      linear_combination
        (-(v 3 * v 4 * h 1) + v 3 * v 4 * h 0 + (v 3) ^ 2 * h 1 + v 2 * v 4 * h 1 + -(v 2 * v 4 * h 0) + -(v 2 * v 3 * h 1)) * g2
    nlinarith [hcertificate]

theorem cubicResidualNetwork27_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork27.toNetwork := by
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
  simp [cubicResidualNetwork27, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork27_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork27.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork27_jacobianNonzero
    cubicResidualNetwork27_fourCharts

def cubicResidualNetwork28 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .xy), (.xy, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork28_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork28.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork28, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork28, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + v 1 * v 2 * v 4 * h 1 + -(v 1 * v 2 * v 3 * h 1) + (v 1) ^ 2 * v 4 * h 0 + -((v 1) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        (-(v 1 * v 4 * h 1) + v 1 * v 4 * h 0 + -(v 1 * v 3 * h 1) + v 1 * v 3 * h 0 + v 1 * v 2 * h 1 + (v 1) ^ 2 * h 0) * g1
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork28, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork28, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 2 * (v 4) ^ 2 * h 1 + -(v 2 * (v 4) ^ 2 * h 0) + -(v 2 * (v 3) ^ 2 * h 1) + v 2 * (v 3) ^ 2 * h 0 + -((v 2) ^ 2 * v 4 * h 1) + (v 2) ^ 2 * v 3 * h 1 + -(v 1 * v 2 * v 4 * h 0) + v 1 * v 2 * v 3 * h 0 = 0 := by
      linear_combination
        (v 2 * v 4 * h 1 + -(v 2 * v 4 * h 0) + v 2 * v 3 * h 1 + -(v 2 * v 3 * h 0) + -((v 2) ^ 2 * h 1) + -(v 1 * v 2 * h 0)) * g1
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork28, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork28, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 3 * v 4 * h 0) + v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) = 0 := by
      linear_combination
        (v 1 * v 4 * h 1 + -(v 1 * v 4 * h 0) + -(v 1 * v 3 * h 1) + v 1 * v 3 * h 0) * g3
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork28, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork28, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -(v 2 * (v 4) ^ 2 * h 1) + v 2 * (v 4) ^ 2 * h 0 + (2 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (-2 : ℝ) * (v 2 * v 3 * v 4 * h 0) + -(v 2 * (v 3) ^ 2 * h 1) + v 2 * (v 3) ^ 2 * h 0 = 0 := by
      linear_combination
        (-(v 2 * v 4 * h 1) + v 2 * v 3 * h 1 + -(v 2 * v 3 * h 0)) * g2 +
      (v 2 * v 4 * h 0) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork28_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork28.toNetwork := by
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
  simp [cubicResidualNetwork28, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork28_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork28.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork28_jacobianNonzero
    cubicResidualNetwork28_fourCharts

def cubicResidualNetwork29 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .xy), (.xy, .x), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork29_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork29.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork29, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork29, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + v 1 * v 3 * v 4 * h 1 + -(v 1 * v 3 * v 4 * h 0) + v 1 * v 2 * v 4 * h 1 + -(v 1 * v 2 * v 3 * h 1) + (v 1) ^ 2 * v 4 * h 0 + -((v 1) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        (-(v 1 * v 4 * h 1) + v 1 * v 4 * h 0 + v 1 * v 2 * h 1 + (v 1) ^ 2 * h 0) * g1
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork29, CodedBimolNetwork.toNetwork,
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
    have g0 : -(v 4) + -(v 1) = 0 := by
      nlinarith [hg0]
    have g3 : v 4 + -(v 3) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork29, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 2 * (v 4) ^ 2 * h 1 + -(v 2 * (v 4) ^ 2 * h 0) + -(v 2 * v 3 * v 4 * h 1) + v 2 * v 3 * v 4 * h 0 + -((v 2) ^ 2 * v 4 * h 1) + (v 2) ^ 2 * v 3 * h 1 + -(v 1 * v 2 * v 4 * h 0) + v 1 * v 2 * v 3 * h 0 = 0 := by
      linear_combination
        (v 2 * v 4 * h 0 + -(v 2 * v 3 * h 0)) * g0 +
      (v 2 * v 4 * h 1 + -((v 2) ^ 2 * h 1)) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork29, CodedBimolNetwork.toNetwork,
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
    have g0 : -(v 4) + -(v 1) = 0 := by
      nlinarith [hg0]
    have g1 : -(v 4) + v 2 = 0 := by
      nlinarith [hg1]
    have g3 : v 4 + -(v 3) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork29, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 3 * v 4 * h 0) + v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) = 0 := by
      linear_combination
        ((-2 : ℝ) * (v 3 * v 4 * h 0) + -((v 3) ^ 2 * h 1) + (v 3) ^ 2 * h 0 + v 2 * v 3 * h 1 + -(v 2 * v 3 * h 0) + (2 : ℝ) * ((v 2) ^ 2 * h 0) + v 1 * v 4 * h 0 + v 1 * v 3 * h 1 + -(v 1 * v 2 * h 1) + -(v 1 * v 2 * h 0)) * g0 +
      ((v 4) ^ 2 * h 1 + (2 : ℝ) * ((v 4) ^ 2 * h 0) + -((v 3) ^ 2 * h 0) + (2 : ℝ) * (v 2 * v 4 * h 0) + (2 : ℝ) * (v 1 * v 2 * h 0) + -((v 1) ^ 2 * h 1) + -((v 1) ^ 2 * h 0)) * g1 +
      ((v 4) ^ 2 * h 1 + (2 : ℝ) * ((v 4) ^ 2 * h 0) + v 3 * v 4 * h 1 + -(v 2 * v 4 * h 1) + -(v 2 * v 3 * h 0) + v 1 * v 4 * h 1 + -(v 1 * v 2 * h 1) + v 1 * v 2 * h 0 + -((v 1) ^ 2 * h 1)) * g3
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork29, CodedBimolNetwork.toNetwork,
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
    have g0 : -(v 4) + -(v 1) = 0 := by
      nlinarith [hg0]
    have g1 : -(v 4) + v 2 = 0 := by
      nlinarith [hg1]
    have g2 : v 4 + -(v 3) = 0 := by
      nlinarith [hg2]
    have g3 : -(v 4) + v 2 + -(v 1) + v 0 = 0 := by
      nlinarith [heq0]
    have g4 : v 4 + -(v 3) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork29, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -(v 2 * (v 4) ^ 2 * h 1) + v 2 * (v 4) ^ 2 * h 0 + (2 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (-2 : ℝ) * (v 2 * v 3 * v 4 * h 0) + -(v 2 * (v 3) ^ 2 * h 1) + v 2 * (v 3) ^ 2 * h 0 = 0 := by
      linear_combination
        ((v 4) ^ 2 * h 1 + (-2 : ℝ) * (v 2 * v 3 * h 1) + (2 : ℝ) * (v 2 * v 3 * h 0) + (v 2) ^ 2 * h 1 + (-2 : ℝ) * ((v 2) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 4 * h 0) + v 1 * v 3 * h 1 + -(v 1 * v 2 * h 1) + (2 : ℝ) * (v 1 * v 2 * h 0)) * g0 +
      (-((v 4) ^ 2 * h 0) + (v 3) ^ 2 * h 0 + (-2 : ℝ) * (v 2 * v 4 * h 0) + -(v 1 * v 3 * h 1) + (2 : ℝ) * (v 1 * v 3 * h 0) + v 1 * v 2 * h 1 + (-2 : ℝ) * (v 1 * v 2 * h 0) + -((v 1) ^ 2 * h 1) + (2 : ℝ) * ((v 1) ^ 2 * h 0) + -(v 0 * v 4 * h 1)) * g1 +
      (v 2 * v 3 * h 1 + (v 2) ^ 2 * h 1 + (-2 : ℝ) * (v 1 * v 4 * h 0)) * g2 +
      (-((v 4) ^ 2 * h 1) + v 2 * v 3 * h 1) * g3 +
      (-((v 4) ^ 2 * h 0) + -(v 3 * v 4 * h 0) + -((v 1) ^ 2 * h 1) + v 0 * v 2 * h 1) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork29_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork29.toNetwork := by
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
  simp [cubicResidualNetwork29, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork29_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork29.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork29_jacobianNonzero
    cubicResidualNetwork29_fourCharts

def cubicResidualNetwork30 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .xy), (.xy, .xx), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork30_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork30.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork30, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork30, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + (2 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (-2 : ℝ) * (v 1 * v 3 * v 4 * h 0) + -(v 1 * (v 3) ^ 2 * h 1) + v 1 * (v 3) ^ 2 * h 0 + v 1 * v 2 * v 4 * h 1 + -(v 1 * v 2 * v 3 * h 1) + (v 1) ^ 2 * v 4 * h 0 + -((v 1) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        (-(v 1 * v 4 * h 1) + v 1 * v 4 * h 0 + v 1 * v 3 * h 1 + -(v 1 * v 3 * h 0) + v 1 * v 2 * h 1 + (v 1) ^ 2 * h 0) * g1
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork30, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork30, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 2 * (v 4) ^ 2 * h 1 + -(v 2 * (v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (2 : ℝ) * (v 2 * v 3 * v 4 * h 0) + v 2 * (v 3) ^ 2 * h 1 + -(v 2 * (v 3) ^ 2 * h 0) + -((v 2) ^ 2 * v 4 * h 1) + (v 2) ^ 2 * v 3 * h 1 + -(v 1 * v 2 * v 4 * h 0) + v 1 * v 2 * v 3 * h 0 = 0 := by
      linear_combination
        (-(v 2 * v 4 * h 0) + -(v 1 * v 2 * h 0)) * g1 +
      (v 2 * v 4 * h 1 + -(v 2 * v 3 * h 1) + v 2 * v 3 * h 0 + -((v 2) ^ 2 * h 1)) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork30, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork30, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 3 * v 4 * h 0) + v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) = 0 := by
      linear_combination
        (v 1 * v 4 * h 1 + -(v 1 * v 4 * h 0) + -(v 1 * v 3 * h 1) + v 1 * v 3 * h 0) * g3
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork30, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork30, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -(v 2 * (v 4) ^ 2 * h 1) + v 2 * (v 4) ^ 2 * h 0 + (2 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (-2 : ℝ) * (v 2 * v 3 * v 4 * h 0) + -(v 2 * (v 3) ^ 2 * h 1) + v 2 * (v 3) ^ 2 * h 0 = 0 := by
      linear_combination
        (-(v 2 * v 4 * h 1) + v 2 * v 4 * h 0 + v 2 * v 3 * h 1 + -(v 2 * v 3 * h 0)) * g2
    nlinarith [hcertificate]

theorem cubicResidualNetwork30_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork30.toNetwork := by
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
  simp [cubicResidualNetwork30, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork30_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork30.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork30_jacobianNonzero
    cubicResidualNetwork30_fourCharts

def cubicResidualNetwork31 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xy, .zero), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork31_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork31.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork31, CodedBimolNetwork.toNetwork,
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
    have g0 : v 4 + -(v 3) + -(v 1) + v 0 = 0 := by
      nlinarith [heq0]
    have g1 : -(v 4) + -(v 3) + v 2 = 0 := by
      nlinarith [heq1]
    have g2 : v 2 * v 4 + -(v 2 * v 3) + v 1 * v 4 + v 1 * v 3 + -(v 1 * v 2) = 0 := by
      nlinarith [hdet]
    have g3 : (2 : ℝ) * (v 1 * (v 4) ^ 3) + (-2 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * (v 3) ^ 2 * v 4) + (2 : ℝ) * (v 1 * (v 3) ^ 3) + (-2 : ℝ) * ((v 1) ^ 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 1) ^ 2 * (v 3) ^ 2) = 0 := by
      nlinarith [hfold]
    have g5 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + -(v 3 * h 1) + -(v 3 * h 0) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + (-2 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + v 2 * h 1 + (-2 : ℝ) * (v 1 * (v 4) ^ 2) + (2 : ℝ) * (v 1 * (v 3) ^ 2) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork31, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + -((v 1) ^ 2 * v 4 * h 0) + -((v 1) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((2 : ℝ) * (v 2 * v 4 * h 1) + -((v 2) ^ 2 * h 1) + v 1 * v 2 * h 0) * g0 +
      (-(v 1 * v 4 * h 1) + -(v 1 * v 4 * h 0) + -(v 1 * v 3 * h 1) + v 1 * v 3 * h 0 + (v 1) ^ 2 * h 0 + v 0 * v 2 * h 1 + (-2 : ℝ) * (v 0 * v 1 * h 1) + -(v 0 * v 1 * h 0)) * g1 +
      ((-2 : ℝ) * (v 4 * h 1) + v 2 * h 1 + -(v 0 * h 1)) * g2 +
      (-(v 0)) * g3 +
      (v 0 * v 1) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork31, CodedBimolNetwork.toNetwork,
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
    have g0 : v 4 + -(v 3) + -(v 1) = 0 := by
      nlinarith [hg0]
    have g1 : -(v 4) + -(v 3) = 0 := by
      nlinarith [hg1]
    have g3 : -(v 4) + -(v 3) + v 2 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork31, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 2 * (v 4) ^ 2 * h 1 + -(v 2 * (v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (2 : ℝ) * (v 2 * v 3 * v 4 * h 0) + v 2 * (v 3) ^ 2 * h 1 + -(v 2 * (v 3) ^ 2 * h 0) + v 1 * v 2 * v 4 * h 0 + -(v 1 * v 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((-2 : ℝ) * (v 2 * v 4 * h 0) + (-2 : ℝ) * (v 2 * v 3 * h 1) + v 1 * v 2 * h 1) * g0 +
      (-(v 2 * v 4 * h 1) + -(v 2 * v 4 * h 0) + v 2 * v 3 * h 1 + v 2 * v 3 * h 0 + v 1 * v 2 * h 1 + v 1 * v 2 * h 0 + -((v 1) ^ 2 * h 1)) * g1 +
      ((v 1) ^ 2 * h 1) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork31, CodedBimolNetwork.toNetwork,
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
    have g0 : v 4 + -(v 3) + -(v 1) = 0 := by
      nlinarith [hg0]
    have g1 : v 4 + -(v 3) = 0 := by
      nlinarith [hg1]
    have g3 : -(v 4) + -(v 3) + v 2 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork31, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + (2 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (-2 : ℝ) * (v 1 * v 3 * v 4 * h 0) + v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + -(v 1 * v 2 * v 4 * h 1) + -(v 1 * v 2 * v 3 * h 1) = 0 := by
      linear_combination
        ((v 2) ^ 2 * h 0) * g0 +
      (-((v 2) ^ 2 * h 0) + v 1 * v 4 * h 1 + v 1 * v 4 * h 0 + v 1 * v 3 * h 1 + v 1 * v 3 * h 0 + -(v 1 * v 2 * h 1) + -(v 1 * v 2 * h 0)) * g1 +
      ((2 : ℝ) * (v 1 * v 4 * h 0) + (-2 : ℝ) * (v 1 * v 3 * h 1) + v 1 * v 2 * h 0) * g3
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork31, CodedBimolNetwork.toNetwork,
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
    have g1 : v 4 + -(v 3) = 0 := by
      nlinarith [hg1]
    have g2 : -(v 4) + -(v 3) = 0 := by
      nlinarith [hg2]
    have g4 : -(v 4) + -(v 3) + v 2 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork31, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -(v 2 * (v 4) ^ 2 * h 1) + v 2 * (v 4) ^ 2 * h 0 + v 2 * (v 3) ^ 2 * h 1 + -(v 2 * (v 3) ^ 2 * h 0) + (v 2) ^ 2 * v 4 * h 1 + -((v 2) ^ 2 * v 3 * h 1) = 0 := by
      linear_combination
        (-(v 2 * v 4 * h 1) + -(v 2 * v 3 * h 1)) * g1 +
      (-(v 2 * v 4 * h 0) + (2 : ℝ) * (v 2 * v 3 * h 1) + v 2 * v 3 * h 0 + -((v 2) ^ 2 * h 1)) * g2 +
      ((-2 : ℝ) * (v 2 * v 3 * h 1)) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork31_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork31.toNetwork := by
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
  simp [cubicResidualNetwork31, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork31_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork31.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork31_jacobianNonzero
    cubicResidualNetwork31_fourCharts

def cubicResidualNetwork32 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xy, .y), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork32_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork32.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork32, CodedBimolNetwork.toNetwork,
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
    have g0 : v 4 + -(v 3) + -(v 1) + v 0 = 0 := by
      nlinarith [heq0]
    have g1 : -(v 4) + v 2 = 0 := by
      nlinarith [heq1]
    have g2 : v 2 * v 4 + -(v 2 * v 3) + v 1 * v 4 + -(v 1 * v 2) = 0 := by
      nlinarith [hdet]
    have g3 : (2 : ℝ) * (v 1 * (v 4) ^ 3) + (-4 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (2 : ℝ) * (v 1 * (v 3) ^ 2 * v 4) + (-2 : ℝ) * ((v 1) ^ 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 1) ^ 2 * v 3 * v 4) = 0 := by
      nlinarith [hfold]
    have g5 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (-4 : ℝ) * (v 3 * (v 4) ^ 2) + (2 : ℝ) * ((v 3) ^ 2 * v 4) + v 2 * h 1 + (-2 : ℝ) * (v 1 * (v 4) ^ 2) + (2 : ℝ) * (v 1 * v 3 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork32, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + v 1 * v 3 * v 4 * h 1 + -(v 1 * v 3 * v 4 * h 0) + -((v 1) ^ 2 * v 4 * h 0) = 0 := by
      linear_combination
        (-(v 2 * v 3 * h 1) + (v 2) ^ 2 * h 1 + v 1 * v 2 * h 0) * g0 +
      (-(v 2 * v 4 * h 1) + v 2 * v 3 * h 1 + -(v 1 * v 4 * h 0) + v 1 * v 3 * h 0 + v 1 * v 2 * h 1 + (v 1) ^ 2 * h 0 + -(v 0 * v 2 * h 1) + (-2 : ℝ) * (v 0 * v 1 * h 1) + -(v 0 * v 1 * h 0)) * g1 +
      (-(v 4 * h 1) + v 3 * h 1 + -(v 0 * h 1)) * g2 +
      (-(v 0)) * g3 +
      (v 0 * v 1) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork32, CodedBimolNetwork.toNetwork,
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
    have g1 : -(v 4) = 0 := by
      nlinarith [hg1]
    have g3 : -(v 4) + v 2 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork32, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 2 * (v 4) ^ 2 * h 1 + -(v 2 * (v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (2 : ℝ) * (v 2 * v 3 * v 4 * h 0) + v 2 * (v 3) ^ 2 * h 1 + -(v 2 * (v 3) ^ 2 * h 0) + v 1 * v 2 * v 4 * h 0 + -(v 1 * v 2 * v 3 * h 0) = 0 := by
      linear_combination
        (-((v 3) ^ 2 * h 1) + (v 3) ^ 2 * h 0 + -(v 2 * v 4 * h 1) + v 2 * v 4 * h 0 + (2 : ℝ) * (v 2 * v 3 * h 1) + (-2 : ℝ) * (v 2 * v 3 * h 0) + v 1 * v 3 * h 0 + -(v 1 * v 2 * h 0)) * g1 +
      ((v 3) ^ 2 * h 1 + -((v 3) ^ 2 * h 0) + -(v 1 * v 3 * h 0)) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork32, CodedBimolNetwork.toNetwork,
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
    have g0 : v 4 + -(v 3) + -(v 1) = 0 := by
      nlinarith [hg0]
    have g1 : v 4 + -(v 3) = 0 := by
      nlinarith [hg1]
    have g3 : -(v 4) + v 2 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork32, CodedBimolNetwork.toNetwork,
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
    have hcertificate : v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + -(v 1 * v 2 * v 4 * h 1) = 0 := by
      linear_combination
        ((v 2) ^ 2 * h 0) * g0 +
      (-(v 2 * v 4 * h 0)) * g1 +
      (-(v 2 * v 4 * h 0) + v 2 * v 3 * h 0 + -(v 1 * v 4 * h 1) + v 1 * v 4 * h 0 + v 1 * v 2 * h 0) * g3
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork32, CodedBimolNetwork.toNetwork,
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
    have g1 : v 4 + -(v 3) = 0 := by
      nlinarith [hg1]
    have g2 : -(v 4) = 0 := by
      nlinarith [hg2]
    simp [-mul_eq_zero, cubicResidualNetwork32, CodedBimolNetwork.toNetwork,
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
    have hcertificate : -(v 2 * (v 4) ^ 2 * h 1) + v 2 * (v 4) ^ 2 * h 0 + v 2 * v 3 * v 4 * h 1 + -(v 2 * v 3 * v 4 * h 0) + (v 2) ^ 2 * v 4 * h 1 + -((v 2) ^ 2 * v 3 * h 1) = 0 := by
      linear_combination
        ((v 2) ^ 2 * h 1) * g1 +
      (v 2 * v 4 * h 1 + -(v 2 * v 4 * h 0) + -(v 2 * v 3 * h 1) + v 2 * v 3 * h 0) * g2
    nlinarith [hcertificate]

theorem cubicResidualNetwork32_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork32.toNetwork := by
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
  simp [cubicResidualNetwork32, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork32_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork32.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork32_jacobianNonzero
    cubicResidualNetwork32_fourCharts

def cubicResidualNetwork33 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.y, .yy), (.xx, .zero)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork33_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork33.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork33, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork33, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork33, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork33, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork33, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork33, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork33, CodedBimolNetwork.toNetwork,
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
    have g0 : (-4 : ℝ) * (v 4) + v 1 = 0 := by
      nlinarith [hg0]
    have g7 : (-4 : ℝ) * (v 4 * h 0) + (-4 : ℝ) * ((v 3) ^ 2 * v 4) + (8 : ℝ) * (v 2 * v 3 * v 4) + (-4 : ℝ) * ((v 2) ^ 2 * v 4) + v 1 * h 0 = 0 := by
      nlinarith [hc0]
    simp [-mul_eq_zero, cubicResidualNetwork33, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (-4 : ℝ) * ((v 3) ^ 2 * v 4 * h 0) + (8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (-4 : ℝ) * ((v 2) ^ 2 * v 4 * h 0) = 0 := by
      linear_combination
        (-((h 0) ^ 2)) * g0 +
      (h 0) * g7
    nlinarith [hcertificate]

theorem cubicResidualNetwork33_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork33.toNetwork := by
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
  simp [cubicResidualNetwork33, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork33_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork33.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork33_jacobianNonzero
    cubicResidualNetwork33_fourCharts

def cubicResidualNetwork34 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xx), (.y, .x), (.y, .yy), (.xx, .zero)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork34_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork34.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork34, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork34, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork34, CodedBimolNetwork.toNetwork,
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
    have g0 : (-4 : ℝ) * (v 4) + v 1 = 0 := by
      nlinarith [hg0]
    have g3 : v 3 + -(v 2) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork34, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (-4 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (4 : ℝ) * ((v 2) ^ 2 * v 4 * h 0) = 0 := by
      linear_combination
        ((v 3) ^ 2 * h 0 + -((v 2) ^ 2 * h 0)) * g0 +
      ((4 : ℝ) * (v 3 * v 4 * h 0) + -(v 1 * v 3 * h 0) + -(v 1 * v 2 * h 0)) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork34, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork34, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork34, CodedBimolNetwork.toNetwork,
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
    have g0 : (-4 : ℝ) * (v 4) + v 1 = 0 := by
      nlinarith [hg0]
    have g1 : v 2 = 0 := by
      nlinarith [hg1]
    have g7 : (-4 : ℝ) * (v 4 * h 0) + (-4 : ℝ) * ((v 3) ^ 2 * v 4) + v 2 * h 1 + (8 : ℝ) * (v 2 * v 3 * v 4) + (-4 : ℝ) * ((v 2) ^ 2 * v 4) + v 1 * h 0 = 0 := by
      nlinarith [hc0]
    simp [-mul_eq_zero, cubicResidualNetwork34, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (-4 : ℝ) * ((v 3) ^ 2 * v 4 * h 0) + (8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (-4 : ℝ) * ((v 2) ^ 2 * v 4 * h 0) = 0 := by
      linear_combination
        (-((h 0) ^ 2)) * g0 +
      (-(h 0 * h 1)) * g1 +
      (h 0) * g7
    nlinarith [hcertificate]

theorem cubicResidualNetwork34_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork34.toNetwork := by
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
  simp [cubicResidualNetwork34, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork34_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork34.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork34_jacobianNonzero
    cubicResidualNetwork34_fourCharts

def cubicResidualNetwork35 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xx), (.y, .x), (.xx, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork35_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork35.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork35, CodedBimolNetwork.toNetwork,
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
    have g0 : -(v 4) + (-2 : ℝ) * (v 3) + v 2 + v 1 + v 0 = 0 := by
      nlinarith [heq0]
    have g1 : v 4 + -(v 2) = 0 := by
      nlinarith [heq1]
    have g2 : (-4 : ℝ) * (v 3 * v 4) + (4 : ℝ) * (v 2 * v 3) + v 1 * v 4 + -(v 1 * v 2) = 0 := by
      nlinarith [hdet]
    have g5 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + (-8 : ℝ) * (v 3 * (v 4) ^ 2) + -(v 2 * h 1) + (2 : ℝ) * (v 2 * (v 4) ^ 2) + (8 : ℝ) * (v 2 * v 3 * v 4) + (2 : ℝ) * (v 1 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * v 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork35, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (-4 : ℝ) * (v 3 * (v 4) ^ 2 * h 1) + (8 : ℝ) * (v 3 * (v 4) ^ 2 * h 0) + (16 : ℝ) * ((v 3) ^ 2 * v 4 * h 0) + (4 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (-4 : ℝ) * (v 2 * v 3 * v 4 * h 0) + v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + (-8 : ℝ) * (v 1 * v 3 * v 4 * h 0) + -(v 1 * v 2 * v 4 * h 1) + (v 1) ^ 2 * v 4 * h 0 = 0 := by
      linear_combination
        (((-16 : ℝ) / 3) * (v 3 * v 4 * h 0) + ((4 : ℝ) / 3) * (v 1 * v 4 * h 0)) * g0 +
      ((-8 : ℝ) * (v 3 * v 4 * h 1) + ((-4 : ℝ) / 3) * (v 3 * v 4 * h 0) + ((-16 : ℝ) / 3) * ((v 3) ^ 2 * h 1) + (2 : ℝ) * (v 1 * v 4 * h 1) + ((4 : ℝ) / 3) * (v 1 * v 4 * h 0) + ((1 : ℝ) / 3) * ((v 1) ^ 2 * h 1) + ((-16 : ℝ) / 3) * (v 0 * v 3 * h 1) + ((4 : ℝ) / 3) * (v 0 * v 1 * h 1)) * g1 +
      ((-2 : ℝ) * ((v 4) ^ 3) + ((-32 : ℝ) / 3) * (v 3 * (v 4) ^ 2) + ((-32 : ℝ) / 3) * ((v 3) ^ 2 * v 4) + ((4 : ℝ) / 3) * (v 1 * (v 4) ^ 2) + ((2 : ℝ) / 3) * ((v 1) ^ 2 * v 4) + ((-8 : ℝ) / 3) * (v 0 * (v 4) ^ 2) + ((-32 : ℝ) / 3) * (v 0 * v 3 * v 4) + ((8 : ℝ) / 3) * (v 0 * v 1 * v 4)) * g2 +
      ((4 : ℝ) * (v 3 * v 4) + ((16 : ℝ) / 3) * ((v 3) ^ 2) + -(v 1 * v 4) + ((-1 : ℝ) / 3) * ((v 1) ^ 2) + ((16 : ℝ) / 3) * (v 0 * v 3) + ((-4 : ℝ) / 3) * (v 0 * v 1)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork35, CodedBimolNetwork.toNetwork,
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
    have g0 : -(v 4) + (-4 : ℝ) * (v 3) + v 1 = 0 := by
      nlinarith [hg0]
    have g1 : v 4 = 0 := by
      nlinarith [hg1]
    have g6 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (-4 : ℝ) * (v 3 * h 0) + (4 : ℝ) * (v 3 * (v 4) ^ 2) + v 2 * h 1 + (-2 : ℝ) * (v 2 * (v 4) ^ 2) + (-4 : ℝ) * ((v 2) ^ 2 * v 3) + v 1 * h 0 + (-2 : ℝ) * (v 1 * (v 4) ^ 2) + (2 : ℝ) * (v 1 * v 2 * v 4) = 0 := by
      nlinarith [hc0]
    have g7 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + (-8 : ℝ) * (v 3 * (v 4) ^ 2) + -(v 2 * h 1) + (2 : ℝ) * (v 2 * (v 4) ^ 2) + (8 : ℝ) * (v 2 * v 3 * v 4) + (2 : ℝ) * (v 1 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * v 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork35, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (4 : ℝ) * (v 3 * (v 4) ^ 2 * h 0) + (-8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (4 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((h 0) ^ 2) * g0 +
      ((h 0) ^ 2) * g1 +
      (-(h 0)) * g6 +
      (-(h 0)) * g7
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork35, CodedBimolNetwork.toNetwork,
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
    have g1 : -(v 4) + v 2 = 0 := by
      nlinarith [hg1]
    have g3 : v 4 + -(v 2) = 0 := by
      nlinarith [heq1]
    have g5 : (-12 : ℝ) * (v 3 * (v 4) ^ 3) + (16 : ℝ) * (v 2 * v 3 * (v 4) ^ 2) + (-4 : ℝ) * ((v 2) ^ 2 * v 3 * v 4) + (2 : ℝ) * (v 1 * (v 4) ^ 3) + (-2 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) = 0 := by
      nlinarith [hfold]
    have g7 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + -(v 2 * h 1) + (2 : ℝ) * (v 2 * (v 4) ^ 2) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork35, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (4 : ℝ) * (v 3 * (v 4) ^ 2 * h 1) + (-8 : ℝ) * (v 3 * (v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (4 : ℝ) * (v 2 * v 3 * v 4 * h 0) + -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + v 1 * v 2 * v 4 * h 1 = 0 := by
      linear_combination
        ((2 : ℝ) * (v 3 * v 4 * h 0)) * g1 +
      ((10 : ℝ) * (v 3 * v 4 * h 1) + (-2 : ℝ) * (v 2 * v 3 * h 1) + (-2 : ℝ) * (v 1 * v 4 * h 1)) * g3 +
      (v 4) * g5 +
      ((-6 : ℝ) * (v 3 * v 4) + (2 : ℝ) * (v 2 * v 3) + v 1 * v 4) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork35, CodedBimolNetwork.toNetwork,
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
    have g0 : -(v 4) + (-4 : ℝ) * (v 3) + v 1 = 0 := by
      nlinarith [hg0]
    have g2 : v 4 = 0 := by
      nlinarith [hg2]
    have g7 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (-4 : ℝ) * (v 3 * h 0) + (-4 : ℝ) * (v 3 * (v 4) ^ 2) + v 2 * h 1 + (-2 : ℝ) * (v 2 * (v 4) ^ 2) + (8 : ℝ) * (v 2 * v 3 * v 4) + (-4 : ℝ) * ((v 2) ^ 2 * v 3) + v 1 * h 0 = 0 := by
      nlinarith [hc0]
    have g8 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + -(v 2 * h 1) + (2 : ℝ) * (v 2 * (v 4) ^ 2) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork35, CodedBimolNetwork.toNetwork,
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
    have hcertificate : (-4 : ℝ) * (v 3 * (v 4) ^ 2 * h 0) + (8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (-4 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        (-((h 0) ^ 2)) * g0 +
      (-((h 0) ^ 2)) * g2 +
      (h 0) * g7 +
      (h 0) * g8
    nlinarith [hcertificate]

theorem cubicResidualNetwork35_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork35.toNetwork := by
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
  simp [cubicResidualNetwork35, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork35_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork35.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork35_jacobianNonzero
    cubicResidualNetwork35_fourCharts

end SmallCusp

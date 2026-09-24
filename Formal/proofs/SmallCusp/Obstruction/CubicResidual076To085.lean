import proofs.SmallCusp.Obstruction.CubicDegeneracy
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

def cubicResidualNetwork76 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xx), (.y, .xy), (.xy, .yy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork76_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork76.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork76, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : (2 : ℝ) * (v 4) + -(v 3) + v 2 + v 1 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g1 : (-2 : ℝ) * (v 4) + v 3 = 0 := by
      nlinarith [heq1]
    have g2 : -(v 2 * v 3) + (-4 : ℝ) * (v 1 * v 4) + v 1 * v 3 + (4 : ℝ) * (v 0 * v 4) + -(v 0 * v 3) = 0 := by
      nlinarith [hdet]
    have g3 : (-4 : ℝ) * (v 1 * (v 3) ^ 2 * v 4) + (2 : ℝ) * (v 1 * (v 3) ^ 3) + (-2 : ℝ) * (v 1 * v 2 * (v 3) ^ 2) + (-2 : ℝ) * ((v 1) ^ 2 * (v 3) ^ 2) + (2 : ℝ) * ((v 1) ^ 2 * v 2 * v 3) + (4 : ℝ) * ((v 1) ^ 3 * v 4) + (4 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (-2 : ℝ) * (v 0 * (v 3) ^ 3) + (2 : ℝ) * (v 0 * v 2 * (v 3) ^ 2) + (4 : ℝ) * (v 0 * v 1 * (v 3) ^ 2) + (-4 : ℝ) * (v 0 * v 1 * v 2 * v 3) + (-12 : ℝ) * (v 0 * (v 1) ^ 2 * v 4) + (-2 : ℝ) * ((v 0) ^ 2 * (v 3) ^ 2) + (2 : ℝ) * ((v 0) ^ 2 * v 2 * v 3) + (12 : ℝ) * ((v 0) ^ 2 * v 1 * v 4) + (-4 : ℝ) * ((v 0) ^ 3 * v 4) = 0 := by
      nlinarith [hfold]
    have g5 : (-4 : ℝ) * (v 4 * h 1) + v 3 * h 1 + v 3 * h 0 + (4 : ℝ) * ((v 3) ^ 2 * v 4) + (-2 : ℝ) * ((v 3) ^ 3) + (2 : ℝ) * (v 2 * (v 3) ^ 2) + (2 : ℝ) * (v 1 * (v 3) ^ 2) + (-2 : ℝ) * (v 1 * v 2 * v 3) + (-4 : ℝ) * ((v 1) ^ 2 * v 4) + (-2 : ℝ) * (v 0 * (v 3) ^ 2) + (2 : ℝ) * (v 0 * v 2 * v 3) + (8 : ℝ) * (v 0 * v 1 * v 4) + (-4 : ℝ) * ((v 0) ^ 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork76, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + -(v 1 * v 2 * v 3 * h 1) + (-4 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (v 1) ^ 2 * v 3 * h 0 + -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 + v 0 * v 2 * v 3 * h 1 + (8 : ℝ) * (v 0 * v 1 * v 4 * h 1) + (-2 : ℝ) * (v 0 * v 1 * v 3 * h 0) + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) + (v 0) ^ 2 * v 3 * h 0 = 0 := by
      linear_combination
        ((2 : ℝ) * (v 1 * v 4 * h 0) + (2 : ℝ) * (v 0 * v 3 * h 1) + -(v 0 * v 3 * h 0)) * g0 +
      (-(v 2 * v 3 * h 1) + -(v 2 * v 3 * h 0) + (4 : ℝ) * (v 1 * v 4 * h 1) + (-2 : ℝ) * (v 1 * v 4 * h 0) + v 1 * v 3 * h 1 + -(v 1 * v 3 * h 0) + (2 : ℝ) * (v 1 * v 2 * h 1) + v 1 * v 2 * h 0 + (-2 : ℝ) * ((v 1) ^ 2 * h 1) + (v 1) ^ 2 * h 0 + (-4 : ℝ) * (v 0 * v 4 * h 1) + (4 : ℝ) * (v 0 * v 4 * h 0) + v 0 * v 3 * h 1 + (-2 : ℝ) * (v 0 * v 2 * h 1) + -(v 0 * v 1 * h 0) + (2 : ℝ) * ((v 0) ^ 2 * h 1)) * g1 +
      ((-2 : ℝ) * (v 4 * h 1) + (2 : ℝ) * (v 4 * h 0) + (2 : ℝ) * (v 1 * h 1) + (4 : ℝ) * ((v 3) ^ 2 * v 4) + (-2 : ℝ) * ((v 3) ^ 3) + (2 : ℝ) * (v 2 * (v 3) ^ 2) + (2 : ℝ) * (v 1 * (v 3) ^ 2) + (-2 : ℝ) * (v 1 * v 2 * v 3) + (-4 : ℝ) * ((v 1) ^ 2 * v 4) + (-2 : ℝ) * (v 0 * (v 3) ^ 2) + (2 : ℝ) * (v 0 * v 2 * v 3) + (8 : ℝ) * (v 0 * v 1 * v 4) + (-4 : ℝ) * ((v 0) ^ 2 * v 4)) * g2 +
      ((-4 : ℝ) * (v 4) + v 3 + -(v 2)) * g3 +
      (v 2 * v 3 + -(v 1 * v 2) + v 0 * v 2) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork76, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : v 3 = 0 := by
      nlinarith [hg1]
    have g3 : (-2 : ℝ) * (v 4) + v 3 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork76, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 2 * (v 3) ^ 2 * h 1 + -(v 2 * (v 3) ^ 2 * h 0) + -((v 2) ^ 2 * v 3 * h 1) + (-4 : ℝ) * (v 1 * v 2 * v 4 * h 1) + v 1 * v 2 * v 3 * h 0 + (4 : ℝ) * (v 0 * v 2 * v 4 * h 1) + -(v 0 * v 2 * v 3 * h 0) = 0 := by
      linear_combination
        (v 2 * v 3 * h 1 + -(v 2 * v 3 * h 0) + -((v 2) ^ 2 * h 1) + (-2 : ℝ) * (v 1 * v 2 * h 1) + v 1 * v 2 * h 0 + (2 : ℝ) * (v 0 * v 2 * h 1) + -(v 0 * v 2 * h 0)) * g1 +
      ((2 : ℝ) * (v 1 * v 2 * h 1) + (-2 : ℝ) * (v 0 * v 2 * h 1)) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork76, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : (4 : ℝ) * (v 4) + -(v 3) + v 2 = 0 := by
      nlinarith [hg1]
    have g2 : (2 : ℝ) * (v 4) + -(v 3) + v 2 + v 1 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : (-2 : ℝ) * (v 4) + v 3 = 0 := by
      nlinarith [heq1]
    have g6 : (4 : ℝ) * (v 4 * h 1) + -(v 3 * h 1) + -(v 3 * h 0) + (-4 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + v 2 * h 1 + v 1 * h 0 + -(v 0 * h 0) = 0 := by
      nlinarith [hc0]
    have g7 : (-4 : ℝ) * (v 4 * h 1) + v 3 * h 1 + v 3 * h 0 + (4 : ℝ) * ((v 3) ^ 2 * v 4) + (-2 : ℝ) * ((v 3) ^ 3) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork76, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -(v 1 * (v 3) ^ 2 * h 1) + v 1 * (v 3) ^ 2 * h 0 + v 0 * (v 3) ^ 2 * h 1 + -(v 0 * (v 3) ^ 2 * h 0) = 0 := by
      linear_combination
        ((2 : ℝ) * (v 2 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 4 * h 0) + (-2 : ℝ) * (v 0 * v 4 * h 0)) * g1 +
      (-((v 3) ^ 2 * h 1)) * g2 +
      (-((v 3) ^ 2 * h 1) + (4 : ℝ) * (v 2 * v 4 * h 1) + v 2 * v 3 * h 1 + (4 : ℝ) * (v 1 * v 4 * h 0) + v 1 * v 3 * h 0 + (-4 : ℝ) * (v 0 * v 4 * h 0) + -(v 0 * v 3 * h 0)) * g3 +
      ((-2 : ℝ) * (v 2 * v 4)) * g6 +
      ((-2 : ℝ) * (v 2 * v 4)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork76, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork76, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -(v 2 * (v 3) ^ 2 * h 1) + v 2 * (v 3) ^ 2 * h 0 = 0 := by
      linear_combination
        (-(v 2 * v 3 * h 1) + v 2 * v 3 * h 0) * g2
    nlinarith [hcertificate]

theorem cubicResidualNetwork76_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork76.toNetwork := by
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
  simp [cubicResidualNetwork76, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork76_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork76.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork76_jacobianNonzero
    cubicResidualNetwork76_fourCharts

def cubicResidualNetwork77 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xx), (.y, .yy), (.xy, .x), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork77_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork77.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork77, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : v 1 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g4 : v 1 * h 0 + -(v 0 * h 0) = 0 := by
      nlinarith [hc0]
    simp [-mul_eq_zero, cubicResidualNetwork77, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + -((v 1) ^ 2 * v 3 * h 0) + (8 : ℝ) * (v 0 * v 1 * v 4 * h 1) + (2 : ℝ) * (v 0 * v 1 * v 3 * h 0) + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) + -((v 0) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 1 * v 4 * h 1) + (4 : ℝ) * (v 0 * v 4 * h 1)) * g0 +
      (-(v 1 * v 3) + v 0 * v 3) * g4
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork77, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork77, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork77, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : v 1 + -(v 0) = 0 := by
      nlinarith [hg0]
    have g2 : v 1 + -(v 0) = 0 := by
      nlinarith [heq0]
    simp [-mul_eq_zero, cubicResidualNetwork77, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -(v 1 * (v 3) ^ 2 * h 1) + v 1 * (v 3) ^ 2 * h 0 + v 1 * v 2 * v 3 * h 1 + v 0 * (v 3) ^ 2 * h 1 + -(v 0 * (v 3) ^ 2 * h 0) + -(v 0 * v 2 * v 3 * h 1) = 0 := by
      linear_combination
        (-((v 3) ^ 2 * h 1) + (v 3) ^ 2 * h 0) * g0 +
      (v 2 * v 3 * h 1) * g2
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork77, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork77, CodedBimolNetwork.toNetwork,
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

theorem cubicResidualNetwork77_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork77.toNetwork := by
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
  simp [cubicResidualNetwork77, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork77_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork77.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork77_jacobianNonzero
    cubicResidualNetwork77_fourCharts

def cubicResidualNetwork78 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xx), (.y, .yy), (.xy, .y), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork78_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork78.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork78, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 3) + v 1 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g1 : (-2 : ℝ) * (v 4) + v 2 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork78, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * ((v 3) ^ 2 * v 4 * h 1) + (8 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (-4 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (-8 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (8 : ℝ) * (v 0 * v 1 * v 4 * h 1) + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) = 0 := by
      linear_combination
        ((2 : ℝ) * (v 2 * v 3 * h 1) + (-2 : ℝ) * (v 1 * v 2 * h 1) + (2 : ℝ) * (v 0 * v 2 * h 1)) * g0 +
      ((2 : ℝ) * ((v 3) ^ 2 * h 1) + (-4 : ℝ) * (v 1 * v 3 * h 1) + (2 : ℝ) * ((v 1) ^ 2 * h 1) + (4 : ℝ) * (v 0 * v 3 * h 1) + (-4 : ℝ) * (v 0 * v 1 * h 1) + (2 : ℝ) * ((v 0) ^ 2 * h 1)) * g1
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork78, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 3) + v 1 + -(v 0) = 0 := by
      nlinarith [hg0]
    have g2 : -(v 3) + v 1 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : (-2 : ℝ) * (v 4) + v 2 = 0 := by
      nlinarith [heq1]
    have g4 : (4 : ℝ) * (v 3 * v 4) + -(v 2 * v 3) + (-4 : ℝ) * (v 1 * v 4) + v 1 * v 2 + (4 : ℝ) * (v 0 * v 4) + -(v 0 * v 2) = 0 := by
      nlinarith [hdet]
    have g5 : (-12 : ℝ) * ((v 3) ^ 3 * v 4) + (2 : ℝ) * (v 2 * (v 3) ^ 3) + (16 : ℝ) * (v 1 * (v 3) ^ 2 * v 4) + (-2 : ℝ) * (v 1 * v 2 * (v 3) ^ 2) + (-4 : ℝ) * ((v 1) ^ 2 * v 3 * v 4) + (-16 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (2 : ℝ) * (v 0 * v 2 * (v 3) ^ 2) + (8 : ℝ) * (v 0 * v 1 * v 3 * v 4) + (-4 : ℝ) * ((v 0) ^ 2 * v 3 * v 4) = 0 := by
      nlinarith [hfold]
    have g7 : (-4 : ℝ) * (v 4 * h 1) + (-4 : ℝ) * ((v 3) ^ 2 * v 4) + v 2 * h 1 + (8 : ℝ) * (v 1 * v 3 * v 4) + (-4 : ℝ) * ((v 1) ^ 2 * v 4) + (-8 : ℝ) * (v 0 * v 3 * v 4) + (8 : ℝ) * (v 0 * v 1 * v 4) + (-4 : ℝ) * ((v 0) ^ 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork78, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-8 : ℝ) * ((v 3) ^ 2 * v 4 * h 1) + (4 : ℝ) * ((v 3) ^ 2 * v 4 * h 0) + v 2 * (v 3) ^ 2 * h 1 + -(v 2 * (v 3) ^ 2 * h 0) + (4 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 3 * v 4 * h 0) + v 1 * v 2 * v 3 * h 0 + (-4 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (4 : ℝ) * (v 0 * v 3 * v 4 * h 0) + -(v 0 * v 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((-2 : ℝ) * (v 3 * v 4 * h 0)) * g0 +
      ((4 : ℝ) * (v 3 * v 4 * h 1)) * g2 +
      (-((v 3) ^ 2 * h 0) + v 1 * v 3 * h 0 + -(v 0 * v 3 * h 0)) * g3 +
      ((-2 : ℝ) * ((v 3) ^ 3)) * g4 +
      (-(v 3)) * g5 +
      ((v 3) ^ 2) * g7
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork78, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork78, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork78, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g8 : (-4 : ℝ) * (v 4 * h 1) + v 2 * h 1 = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork78, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-16 : ℝ) * (v 3 * (v 4) ^ 2 * h 1) + (8 : ℝ) * (v 2 * v 3 * v 4 * h 1) + -((v 2) ^ 2 * v 3 * h 1) = 0 := by
      linear_combination
        ((4 : ℝ) * (v 3 * v 4) + -(v 2 * v 3)) * g8
    nlinarith [hcertificate]

theorem cubicResidualNetwork78_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork78.toNetwork := by
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
  simp [cubicResidualNetwork78, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork78_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork78.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork78_jacobianNonzero
    cubicResidualNetwork78_fourCharts

def cubicResidualNetwork79 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xx, .xy), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork79_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork79.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork79, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : -(v 4) + v 3 + -(v 2) + v 1 = 0 := by
      nlinarith [heq1]
    have g2 : v 2 * v 4 + (-2 : ℝ) * (v 2 * v 3) + -(v 1 * v 2) + v 0 * v 4 + v 0 * v 2 = 0 := by
      nlinarith [hdet]
    have g3 : (2 : ℝ) * (v 0 * (v 4) ^ 3) + (-2 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (4 : ℝ) * (v 0 * v 2 * (v 4) ^ 2) + (8 : ℝ) * (v 0 * (v 2) ^ 2 * v 3) + (-2 : ℝ) * (v 0 * v 1 * (v 4) ^ 2) + (-4 : ℝ) * (v 0 * v 1 * v 2 * v 4) + (-2 : ℝ) * ((v 0) ^ 2 * (v 4) ^ 2) + (-4 : ℝ) * ((v 0) ^ 2 * v 2 * v 4) = 0 := by
      nlinarith [hfold]
    have g4 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + (-2 : ℝ) * (v 3 * h 0) + (2 : ℝ) * (v 3 * (v 4) ^ 2) + (2 : ℝ) * (v 2 * h 1) + (-4 : ℝ) * (v 2 * (v 4) ^ 2) + (-8 : ℝ) * ((v 2) ^ 2 * v 3) + -(v 1 * h 0) + (2 : ℝ) * (v 1 * (v 4) ^ 2) + (4 : ℝ) * (v 1 * v 2 * v 4) + -(v 0 * h 0) + (2 : ℝ) * (v 0 * (v 4) ^ 2) + (4 : ℝ) * (v 0 * v 2 * v 4) = 0 := by
      nlinarith [hc0]
    have g5 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (2 : ℝ) * (v 3 * h 0) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + -(v 2 * h 1) + (4 : ℝ) * (v 2 * (v 4) ^ 2) + (8 : ℝ) * ((v 2) ^ 2 * v 3) + v 1 * h 0 + (-2 : ℝ) * (v 1 * (v 4) ^ 2) + (-4 : ℝ) * (v 1 * v 2 * v 4) + (-2 : ℝ) * (v 0 * (v 4) ^ 2) + (-4 : ℝ) * (v 0 * v 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork79, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -(v 0 * (v 4) ^ 2 * h 1) + v 0 * (v 4) ^ 2 * h 0 + (-2 : ℝ) * (v 0 * v 2 * v 4 * h 1) + (4 : ℝ) * (v 0 * v 2 * v 3 * h 0) + -(v 0 * v 1 * v 4 * h 0) + -((v 0) ^ 2 * v 4 * h 0) = 0 := by
      linear_combination
        ((2 : ℝ) * ((v 4) ^ 2 * h 1) + (-2 : ℝ) * (v 3 * v 4 * h 1) + (-4 : ℝ) * ((v 2) ^ 2 * h 1) + (-2 : ℝ) * (v 1 * v 4 * h 1)) * g0 +
      ((2 : ℝ) * ((v 4) ^ 2 * h 1) + (-2 : ℝ) * (v 3 * v 4 * h 1) + (2 : ℝ) * (v 2 * v 4 * h 1) + (-8 : ℝ) * ((v 2) ^ 2 * h 1) + (-2 : ℝ) * (v 1 * v 4 * h 1) + (-4 : ℝ) * (v 0 * v 3 * h 0) + (2 : ℝ) * (v 0 * v 2 * h 1) + (-2 : ℝ) * (v 0 * v 1 * h 0)) * g1 +
      ((-2 : ℝ) * (v 2 * h 1)) * g2 +
      (v 4 + (-2 : ℝ) * (v 3) + (-2 : ℝ) * (v 1)) * g3 +
      ((2 : ℝ) * (v 1 * v 2) + v 0 * v 4) * g4 +
      ((2 : ℝ) * (v 1 * v 2) + (2 : ℝ) * (v 0 * v 3) + (2 : ℝ) * (v 0 * v 1)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork79, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : -(v 4) + (2 : ℝ) * (v 3) + v 1 = 0 := by
      nlinarith [hg1]
    have g2 : v 4 + -(v 3) + (2 : ℝ) * (v 2) + -(v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : -(v 4) + v 3 + -(v 2) + v 1 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork79, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
        (-((v 4) ^ 2 * h 1) + (2 : ℝ) * (v 3 * v 4 * h 1) + (-3 : ℝ) * (v 2 * v 4 * h 0) + (-4 : ℝ) * ((v 2) ^ 2 * h 0)) * g0 +
      (v 3 * v 4 * h 1 + (3 : ℝ) * (v 2 * v 4 * h 1) + (-4 : ℝ) * (v 2 * v 4 * h 0) + (-8 : ℝ) * ((v 2) ^ 2 * h 0) + -(v 1 * v 3 * h 1) + v 1 * v 2 * h 1 + -((v 1) ^ 2 * h 1)) * g1 +
      ((v 4) ^ 2 * h 1 + (-2 : ℝ) * (v 3 * v 4 * h 1) + (2 : ℝ) * (v 2 * v 4 * h 0) + (4 : ℝ) * ((v 2) ^ 2 * h 0)) * g2 +
      ((-2 : ℝ) * (v 2 * v 4 * h 1) + (4 : ℝ) * (v 2 * v 4 * h 0) + (8 : ℝ) * ((v 2) ^ 2 * h 0) + (2 : ℝ) * (v 1 * v 3 * h 1) + (v 1) ^ 2 * h 1) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork79, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g3 : -(v 4) + v 3 + -(v 2) + v 1 = 0 := by
      nlinarith [heq1]
    have g5 : (2 : ℝ) * (v 0 * (v 4) ^ 3) + (-2 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * v 2 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * (v 2) ^ 2 * v 3) + (-2 : ℝ) * (v 0 * v 1 * (v 4) ^ 2) + (-2 : ℝ) * (v 0 * v 1 * v 2 * v 4) = 0 := by
      nlinarith [hfold]
    have g7 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (2 : ℝ) * (v 3 * h 0) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + -(v 2 * h 1) + (2 : ℝ) * (v 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 2) ^ 2 * v 3) + v 1 * h 0 + (-2 : ℝ) * (v 1 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * v 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork79, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 0 * (v 4) ^ 2 * h 1 + -(v 0 * (v 4) ^ 2 * h 0) + v 0 * v 2 * v 4 * h 1 + (-2 : ℝ) * (v 0 * v 2 * v 3 * h 0) + v 0 * v 1 * v 4 * h 0 = 0 := by
      linear_combination
        (-(v 0 * v 4 * h 0)) * g0 +
      (-(v 0 * v 3 * h 0)) * g1 +
      (v 0 * v 4 * h 0) * g2 +
      ((2 : ℝ) * (v 0 * v 4 * h 0)) * g3 +
      (v 4) * g5 +
      (-(v 0 * v 4)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork79, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g2 : -(v 4) + (2 : ℝ) * (v 3) + v 1 = 0 := by
      nlinarith [hg2]
    have g3 : v 4 + -(v 3) + (2 : ℝ) * (v 2) + -(v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g4 : -(v 4) + v 3 + -(v 2) + v 1 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork79, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -(v 2 * (v 4) ^ 2 * h 1) + v 2 * (v 4) ^ 2 * h 0 + -((v 2) ^ 2 * v 4 * h 1) + (2 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + -(v 1 * v 2 * v 4 * h 0) = 0 := by
      linear_combination
        (((1 : ℝ) / 2) * ((v 4) ^ 2 * h 1) + ((-1 : ℝ) / 2) * ((v 4) ^ 2 * h 0)) * g0 +
      (((1 : ℝ) / 2) * ((v 4) ^ 2 * h 0) + ((-1 : ℝ) / 2) * (v 3 * v 4 * h 0) + ((-1 : ℝ) / 2) * (v 2 * v 4 * h 1) + v 2 * v 3 * h 0 + ((-1 : ℝ) / 2) * (v 1 * v 4 * h 0)) * g1 +
      (((1 : ℝ) / 2) * ((v 4) ^ 2 * h 1) + ((-1 : ℝ) / 2) * ((v 4) ^ 2 * h 0)) * g2 +
      (((-1 : ℝ) / 2) * ((v 4) ^ 2 * h 1) + ((1 : ℝ) / 2) * ((v 4) ^ 2 * h 0)) * g3 +
      (((-1 : ℝ) / 2) * ((v 4) ^ 2 * h 1) + (v 4) ^ 2 * h 0) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork79_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork79.toNetwork := by
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
  simp [cubicResidualNetwork79, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork79_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork79.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork79_jacobianNonzero
    cubicResidualNetwork79_fourCharts

def cubicResidualNetwork80 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xx, .xy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork80_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork80.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork80, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) + v 1 = 0 := by
      nlinarith [heq1]
    have g2 : (-2 : ℝ) * (v 2 * v 3) + -(v 1 * v 2) + (4 : ℝ) * (v 0 * v 4) + v 0 * v 2 = 0 := by
      nlinarith [hdet]
    have g3 : (32 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (-16 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (32 : ℝ) * (v 0 * v 2 * v 3 * v 4) + (8 : ℝ) * (v 0 * (v 2) ^ 2 * v 3) + (-16 : ℝ) * (v 0 * v 1 * v 3 * v 4) + (-4 : ℝ) * (v 0 * (v 1) ^ 2 * v 4) + (-16 : ℝ) * ((v 0) ^ 2 * v 3 * v 4) + (-8 : ℝ) * ((v 0) ^ 2 * v 1 * v 4) + (-4 : ℝ) * ((v 0) ^ 3 * v 4) = 0 := by
      nlinarith [hfold]
    have g4 : (4 : ℝ) * (v 4 * h 1) + (-2 : ℝ) * (v 3 * h 0) + (-32 : ℝ) * (v 3 * (v 4) ^ 2) + (16 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * (v 2 * h 1) + (-32 : ℝ) * (v 2 * v 3 * v 4) + (-8 : ℝ) * ((v 2) ^ 2 * v 3) + -(v 1 * h 0) + (16 : ℝ) * (v 1 * v 3 * v 4) + (4 : ℝ) * ((v 1) ^ 2 * v 4) + -(v 0 * h 0) + (16 : ℝ) * (v 0 * v 3 * v 4) + (8 : ℝ) * (v 0 * v 1 * v 4) + (4 : ℝ) * ((v 0) ^ 2 * v 4) = 0 := by
      nlinarith [hc0]
    have g5 : (-4 : ℝ) * (v 4 * h 1) + (2 : ℝ) * (v 3 * h 0) + (32 : ℝ) * (v 3 * (v 4) ^ 2) + (-16 : ℝ) * ((v 3) ^ 2 * v 4) + -(v 2 * h 1) + (32 : ℝ) * (v 2 * v 3 * v 4) + (8 : ℝ) * ((v 2) ^ 2 * v 3) + v 1 * h 0 + (-16 : ℝ) * (v 1 * v 3 * v 4) + (-4 : ℝ) * ((v 1) ^ 2 * v 4) + (-16 : ℝ) * (v 0 * v 3 * v 4) + (-8 : ℝ) * (v 0 * v 1 * v 4) + (-4 : ℝ) * ((v 0) ^ 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork80, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-8 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (8 : ℝ) * (v 0 * v 3 * v 4 * h 0) + (4 : ℝ) * (v 0 * v 2 * v 3 * h 0) + (-4 : ℝ) * (v 0 * v 1 * v 4 * h 1) + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) = 0 := by
      linear_combination
        ((-32 : ℝ) * ((v 4) ^ 2 * h 0) + (8 : ℝ) * (v 3 * v 4 * h 1) + (4 : ℝ) * ((v 3) ^ 2 * h 1) + (-16 : ℝ) * (v 2 * v 4 * h 0) + (-8 : ℝ) * (v 2 * v 3 * h 0) + (4 : ℝ) * (v 1 * v 4 * h 1) + (4 : ℝ) * (v 1 * v 3 * h 1) + (8 : ℝ) * (v 1 * v 3 * h 0) + (-8 : ℝ) * (v 1 * v 2 * h 0) + (6 : ℝ) * ((v 1) ^ 2 * h 0) + (-4 : ℝ) * (v 0 * v 4 * h 1) + (-2 : ℝ) * (v 0 * v 2 * h 1)) * g0 +
      ((-32 : ℝ) * ((v 4) ^ 2 * h 0) + (8 : ℝ) * (v 3 * v 4 * h 1) + (4 : ℝ) * ((v 3) ^ 2 * h 1) + (-32 : ℝ) * (v 2 * v 4 * h 0) + (-8 : ℝ) * (v 2 * v 3 * h 0) + (4 : ℝ) * (v 1 * v 4 * h 1) + (4 : ℝ) * (v 1 * v 3 * h 1) + (8 : ℝ) * (v 1 * v 3 * h 0) + (-12 : ℝ) * (v 1 * v 2 * h 0) + (6 : ℝ) * ((v 1) ^ 2 * h 0) + (-4 : ℝ) * (v 0 * v 4 * h 1) + (4 : ℝ) * (v 0 * v 3 * h 1) + (-4 : ℝ) * (v 0 * v 2 * h 1) + (-4 : ℝ) * (v 0 * v 2 * h 0) + (6 : ℝ) * (v 0 * v 1 * h 0)) * g1 +
      ((4 : ℝ) * (v 4 * h 1) + (-8 : ℝ) * (v 4 * h 0) + (2 : ℝ) * (v 3 * h 1) + (-4 : ℝ) * (v 2 * h 0) + (2 : ℝ) * (v 1 * h 0) + (-2 : ℝ) * (v 0 * h 1)) * g2 +
      ((-4 : ℝ) * (v 4)) * g3 +
      ((-2 : ℝ) * (v 1 * v 3)) * g4 +
      ((-2 : ℝ) * (v 1 * v 3) + (4 : ℝ) * (v 0 * v 4)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork80, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : (2 : ℝ) * (v 3) + v 1 = 0 := by
      nlinarith [hg1]
    have g2 : (2 : ℝ) * (v 4) + -(v 3) + (2 : ℝ) * (v 2) + -(v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) + v 1 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork80, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
        ((-4 : ℝ) * (v 2 * v 4 * h 1) + -((v 1) ^ 2 * h 0)) * g0 +
      ((-4 : ℝ) * (v 2 * v 4 * h 0) + (-2 : ℝ) * (v 2 * v 3 * h 0) + (-2 : ℝ) * ((v 2) ^ 2 * h 0) + (2 : ℝ) * (v 1 * v 2 * h 0) + -((v 1) ^ 2 * h 0) + (2 : ℝ) * (v 0 * v 3 * h 0) + -(v 0 * v 1 * h 0)) * g1 +
      ((4 : ℝ) * ((v 3) ^ 2 * h 0)) * g2 +
      ((4 : ℝ) * ((v 3) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 2 * h 0)) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork80, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g3 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) + v 1 = 0 := by
      nlinarith [heq1]
    have g6 : (4 : ℝ) * (v 4 * h 1) + (-2 : ℝ) * (v 3 * h 0) + (-32 : ℝ) * (v 3 * (v 4) ^ 2) + (16 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * (v 2 * h 1) + (-16 : ℝ) * (v 2 * v 3 * v 4) + (-2 : ℝ) * ((v 2) ^ 2 * v 3) + -(v 1 * h 0) + (16 : ℝ) * (v 1 * v 3 * v 4) + (4 : ℝ) * ((v 1) ^ 2 * v 4) + -(v 0 * h 0) = 0 := by
      nlinarith [hc0]
    have g7 : (-4 : ℝ) * (v 4 * h 1) + (2 : ℝ) * (v 3 * h 0) + (32 : ℝ) * (v 3 * (v 4) ^ 2) + (-16 : ℝ) * ((v 3) ^ 2 * v 4) + -(v 2 * h 1) + (16 : ℝ) * (v 2 * v 3 * v 4) + (2 : ℝ) * ((v 2) ^ 2 * v 3) + v 1 * h 0 + (-16 : ℝ) * (v 1 * v 3 * v 4) + (-4 : ℝ) * ((v 1) ^ 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork80, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (8 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (-8 : ℝ) * (v 0 * v 3 * v 4 * h 0) + (-2 : ℝ) * (v 0 * v 2 * v 3 * h 0) + (4 : ℝ) * (v 0 * v 1 * v 4 * h 1) = 0 := by
      linear_combination
        (v 0 * v 2 * h 1 + -((v 0) ^ 2 * h 1)) * g0 +
      (-(v 2 * v 3 * h 1) + (2 : ℝ) * (v 0 * v 3 * h 1) + -(v 0 * v 3 * h 0) + v 0 * v 1 * h 1 + -((v 0) ^ 2 * h 1)) * g1 +
      ((2 : ℝ) * (v 2 * v 3 * h 1) + -(v 0 * v 1 * h 1) + (v 0) ^ 2 * h 1) * g2 +
      ((2 : ℝ) * (v 2 * v 3 * h 1) + -(v 0 * v 1 * h 1) + -((v 0) ^ 2 * h 1)) * g3 +
      ((4 : ℝ) * (v 3 * v 4)) * g6 +
      ((4 : ℝ) * (v 3 * v 4)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork80, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g2 : (2 : ℝ) * (v 3) + v 1 = 0 := by
      nlinarith [hg2]
    have g4 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) + v 1 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork80, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
        ((4 : ℝ) * ((v 4) ^ 2 * h 0) + (4 : ℝ) * (v 3 * v 4 * h 0) + v 1 * v 4 * h 0 + ((-1 : ℝ) / 2) * (v 1 * v 2 * h 0)) * g1 +
      ((-12 : ℝ) * ((v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 2 * v 4 * h 1) + (v 2) ^ 2 * h 0) * g2 +
      ((8 : ℝ) * ((v 4) ^ 2 * h 0)) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork80_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork80.toNetwork := by
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
  simp [cubicResidualNetwork80, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork80_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork80.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork80_jacobianNonzero
    cubicResidualNetwork80_fourCharts

def cubicResidualNetwork81 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xy, .yy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork81_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork81.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork81, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) + v 1 = 0 := by
      nlinarith [heq1]
    have g2 : -(v 2 * v 3) + -(v 1 * v 2) + (4 : ℝ) * (v 0 * v 4) + -(v 0 * v 3) + v 0 * v 2 = 0 := by
      nlinarith [hdet]
    have g3 : (4 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (-2 : ℝ) * (v 0 * (v 3) ^ 3) + (4 : ℝ) * (v 0 * v 2 * (v 3) ^ 2) + (-2 : ℝ) * (v 0 * v 1 * (v 3) ^ 2) + (4 : ℝ) * (v 0 * v 1 * v 2 * v 3) + (-4 : ℝ) * (v 0 * (v 1) ^ 2 * v 4) + (-2 : ℝ) * ((v 0) ^ 2 * (v 3) ^ 2) + (4 : ℝ) * ((v 0) ^ 2 * v 2 * v 3) + (-8 : ℝ) * ((v 0) ^ 2 * v 1 * v 4) + (-4 : ℝ) * ((v 0) ^ 3 * v 4) = 0 := by
      nlinarith [hfold]
    have g4 : (4 : ℝ) * (v 4 * h 1) + -(v 3 * h 1) + -(v 3 * h 0) + (-4 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + (2 : ℝ) * (v 2 * h 1) + (-4 : ℝ) * (v 2 * (v 3) ^ 2) + -(v 1 * h 0) + (2 : ℝ) * (v 1 * (v 3) ^ 2) + (-4 : ℝ) * (v 1 * v 2 * v 3) + (4 : ℝ) * ((v 1) ^ 2 * v 4) + -(v 0 * h 0) + (2 : ℝ) * (v 0 * (v 3) ^ 2) + (-4 : ℝ) * (v 0 * v 2 * v 3) + (8 : ℝ) * (v 0 * v 1 * v 4) + (4 : ℝ) * ((v 0) ^ 2 * v 4) = 0 := by
      nlinarith [hc0]
    have g5 : (-4 : ℝ) * (v 4 * h 1) + v 3 * h 1 + v 3 * h 0 + (4 : ℝ) * ((v 3) ^ 2 * v 4) + (-2 : ℝ) * ((v 3) ^ 3) + -(v 2 * h 1) + (4 : ℝ) * (v 2 * (v 3) ^ 2) + v 1 * h 0 + (-2 : ℝ) * (v 1 * (v 3) ^ 2) + (4 : ℝ) * (v 1 * v 2 * v 3) + (-4 : ℝ) * ((v 1) ^ 2 * v 4) + (-2 : ℝ) * (v 0 * (v 3) ^ 2) + (4 : ℝ) * (v 0 * v 2 * v 3) + (-8 : ℝ) * (v 0 * v 1 * v 4) + (-4 : ℝ) * ((v 0) ^ 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork81, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 + (2 : ℝ) * (v 0 * v 2 * v 3 * h 1) + (-4 : ℝ) * (v 0 * v 1 * v 4 * h 1) + v 0 * v 1 * v 3 * h 0 + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) + (v 0) ^ 2 * v 3 * h 0 = 0 := by
      linear_combination
        ((-8 : ℝ) * ((v 4) ^ 2 * h 1) + (4 : ℝ) * (v 3 * v 4 * h 1) + v 2 * v 3 * h 1 + (-4 : ℝ) * (v 0 * v 4 * h 1) + (-4 : ℝ) * (v 0 * v 4 * h 0) + (2 : ℝ) * (v 0 * v 3 * h 1) + -(v 0 * v 3 * h 0) + (-2 : ℝ) * (v 0 * v 2 * h 1) + (-2 : ℝ) * (v 0 * v 1 * h 0)) * g0 +
      ((-8 : ℝ) * ((v 4) ^ 2 * h 1) + (4 : ℝ) * (v 3 * v 4 * h 1) + (-4 : ℝ) * (v 2 * v 4 * h 1) + (3 : ℝ) * (v 2 * v 3 * h 1) + (-16 : ℝ) * (v 0 * v 4 * h 1) + (-4 : ℝ) * (v 0 * v 4 * h 0) + (4 : ℝ) * (v 0 * v 3 * h 1) + v 0 * v 3 * h 0 + (-6 : ℝ) * (v 0 * v 2 * h 1) + (-2 : ℝ) * ((v 0) ^ 2 * h 0)) * g1 +
      ((-8 : ℝ) * (v 4 * h 1) + (3 : ℝ) * (v 3 * h 1) + v 3 * h 0 + (-2 : ℝ) * (v 2 * h 1) + v 1 * h 0 + (-2 : ℝ) * (v 0 * h 1) + (-2 : ℝ) * (v 0 * h 0) + (4 : ℝ) * ((v 3) ^ 2 * v 4) + (-2 : ℝ) * ((v 3) ^ 3) + (4 : ℝ) * (v 2 * (v 3) ^ 2) + (-2 : ℝ) * (v 1 * (v 3) ^ 2) + (4 : ℝ) * (v 1 * v 2 * v 3) + (-4 : ℝ) * ((v 1) ^ 2 * v 4) + (-2 : ℝ) * (v 0 * (v 3) ^ 2) + (4 : ℝ) * (v 0 * v 2 * v 3) + (-8 : ℝ) * (v 0 * v 1 * v 4) + (-4 : ℝ) * ((v 0) ^ 2 * v 4)) * g2 +
      ((-4 : ℝ) * (v 4) + v 3 + -(v 2) + (2 : ℝ) * (v 1)) * g3 +
      ((-4 : ℝ) * (v 2 * v 4) + -(v 1 * v 2)) * g4 +
      ((-4 : ℝ) * (v 2 * v 4) + v 2 * v 3 + (-2 : ℝ) * (v 0 * v 1)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork81, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : v 3 + v 1 = 0 := by
      nlinarith [hg1]
    have g2 : (2 : ℝ) * (v 4) + -(v 3) + (2 : ℝ) * (v 2) + -(v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) + v 1 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork81, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
        ((-4 : ℝ) * (v 2 * v 4 * h 1) + v 2 * v 3 * h 0 + -((v 1) ^ 2 * h 1)) * g0 +
      ((-4 : ℝ) * (v 2 * v 4 * h 1) + v 2 * v 3 * h 1 + (-2 : ℝ) * ((v 2) ^ 2 * h 1) + v 1 * v 2 * h 1 + -((v 1) ^ 2 * h 1)) * g1 +
      ((v 1) ^ 2 * h 1) * g2 +
      ((-2 : ℝ) * (v 1 * v 2 * h 1) + (v 1) ^ 2 * h 1) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork81, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g3 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) + v 1 = 0 := by
      nlinarith [heq1]
    have g6 : (4 : ℝ) * (v 4 * h 1) + -(v 3 * h 1) + -(v 3 * h 0) + (-4 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + (2 : ℝ) * (v 2 * h 1) + (-2 : ℝ) * (v 2 * (v 3) ^ 2) + -(v 1 * h 0) + (2 : ℝ) * (v 1 * (v 3) ^ 2) + (-2 : ℝ) * (v 1 * v 2 * v 3) + (4 : ℝ) * ((v 1) ^ 2 * v 4) + -(v 0 * h 0) = 0 := by
      nlinarith [hc0]
    have g7 : (-4 : ℝ) * (v 4 * h 1) + v 3 * h 1 + v 3 * h 0 + (4 : ℝ) * ((v 3) ^ 2 * v 4) + (-2 : ℝ) * ((v 3) ^ 3) + -(v 2 * h 1) + (2 : ℝ) * (v 2 * (v 3) ^ 2) + v 1 * h 0 + (-2 : ℝ) * (v 1 * (v 3) ^ 2) + (2 : ℝ) * (v 1 * v 2 * v 3) + (-4 : ℝ) * ((v 1) ^ 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork81, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 0 * (v 3) ^ 2 * h 1 + -(v 0 * (v 3) ^ 2 * h 0) + -(v 0 * v 2 * v 3 * h 1) + (4 : ℝ) * (v 0 * v 1 * v 4 * h 1) + -(v 0 * v 1 * v 3 * h 0) = 0 := by
      linear_combination
        ((2 : ℝ) * ((v 4) ^ 2 * h 1) + -(v 3 * v 4 * h 1) + (-2 : ℝ) * (v 1 * v 4 * h 0) + ((-3 : ℝ) / 2) * (v 1 * v 3 * h 1) + ((1 : ℝ) / 2) * (v 1 * v 3 * h 0) + (2 : ℝ) * (v 1 * v 2 * h 1) + -(v 1 * v 2 * h 0) + ((-5 : ℝ) / 2) * ((v 1) ^ 2 * h 1) + (-5 : ℝ) * (v 0 * v 4 * h 1) + (3 : ℝ) * (v 0 * v 4 * h 0) + ((3 : ℝ) / 2) * (v 0 * v 3 * h 1) + (-3 : ℝ) * (v 0 * v 2 * h 1) + v 0 * v 2 * h 0 + ((1 : ℝ) / 2) * ((v 0) ^ 2 * h 1)) * g0 +
      (-(v 2 * v 3 * h 1) + -(v 1 * v 3 * h 1) + ((-1 : ℝ) / 2) * (v 1 * v 3 * h 0) + -(v 1 * v 2 * h 1) + -((v 1) ^ 2 * h 1) + ((-1 : ℝ) / 2) * ((v 1) ^ 2 * h 0) + v 0 * v 4 * h 0 + ((1 : ℝ) / 2) * (v 0 * v 3 * h 0) + -((v 0) ^ 2 * h 1) + ((1 : ℝ) / 2) * ((v 0) ^ 2 * h 0)) * g1 +
      ((-2 : ℝ) * ((v 4) ^ 2 * h 1) + v 3 * v 4 * h 1 + v 2 * v 3 * h 1 + v 1 * v 4 * h 1 + ((5 : ℝ) / 2) * (v 1 * v 3 * h 1) + v 1 * v 2 * h 1 + ((5 : ℝ) / 2) * ((v 1) ^ 2 * h 1) + -(v 0 * v 4 * h 0) + ((-1 : ℝ) / 2) * (v 0 * v 3 * h 1) + ((-1 : ℝ) / 2) * (v 0 * v 3 * h 0) + ((-1 : ℝ) / 2) * ((v 0) ^ 2 * h 1)) * g2 +
      ((-2 : ℝ) * ((v 4) ^ 2 * h 1) + (2 : ℝ) * (v 0 * v 3 * h 1) + -(v 0 * v 3 * h 0)) * g3 +
      ((2 : ℝ) * ((v 4) ^ 2)) * g6 +
      ((2 : ℝ) * ((v 4) ^ 2)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork81, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g2 : v 3 + v 1 = 0 := by
      nlinarith [hg2]
    have g3 : (2 : ℝ) * (v 4) + -(v 3) + (2 : ℝ) * (v 2) + -(v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g4 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) + v 1 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork81, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
        ((-2 : ℝ) * (v 3 * v 4 * h 1) + (v 1) ^ 2 * h 1) * g0 +
      ((-2 : ℝ) * (v 3 * v 4 * h 1) + (-4 : ℝ) * (v 2 * v 4 * h 1) + v 2 * v 3 * h 0 + v 1 * v 2 * h 1 + (v 1) ^ 2 * h 1) * g2 +
      ((2 : ℝ) * (v 3 * v 4 * h 1) + -((v 1) ^ 2 * h 1)) * g3 +
      ((2 : ℝ) * (v 3 * v 4 * h 1) + -(v 2 * v 3 * h 1) + -((v 1) ^ 2 * h 1)) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork81_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork81.toNetwork := by
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
  simp [cubicResidualNetwork81, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork81_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork81.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork81_jacobianNonzero
    cubicResidualNetwork81_fourCharts

def cubicResidualNetwork82 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xx, .xy), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork82_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork82.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork82, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g3 : (-2 : ℝ) * (v 1 * (v 4) ^ 3) + (2 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * (v 2) ^ 2 * v 3) + (2 : ℝ) * (v 0 * (v 4) ^ 3) + (-2 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * v 2 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * (v 2) ^ 2 * v 3) + (2 : ℝ) * (v 0 * v 1 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * v 1 * v 2 * v 4) + (-2 : ℝ) * ((v 0) ^ 2 * (v 4) ^ 2) + (-2 : ℝ) * ((v 0) ^ 2 * v 2 * v 4) = 0 := by
      nlinarith [hfold]
    have g4 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + (-2 : ℝ) * (v 3 * h 0) + (2 : ℝ) * (v 3 * (v 4) ^ 2) + v 2 * h 1 + (-2 : ℝ) * (v 2 * (v 4) ^ 2) + (-2 : ℝ) * ((v 2) ^ 2 * v 3) + -(v 0 * h 0) + (2 : ℝ) * (v 0 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * v 2 * v 4) = 0 := by
      nlinarith [hc0]
    simp [-mul_eq_zero, cubicResidualNetwork82, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + v 1 * v 2 * v 4 * h 1 + (-2 : ℝ) * (v 1 * v 2 * v 3 * h 0) + -(v 0 * (v 4) ^ 2 * h 1) + v 0 * (v 4) ^ 2 * h 0 + -(v 0 * v 2 * v 4 * h 1) + (2 : ℝ) * (v 0 * v 2 * v 3 * h 0) + v 0 * v 1 * v 4 * h 0 + -((v 0) ^ 2 * v 4 * h 0) = 0 := by
      linear_combination
        (-(v 4 * h 1) + v 4 * h 0 + v 2 * h 1 + -(v 0 * h 0)) * g2 +
      (-(v 2)) * g3 +
      (v 1 * v 2 + -(v 0 * v 2)) * g4
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork82, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork82, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork82, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g5 : (-2 : ℝ) * (v 1 * (v 4) ^ 3) + (2 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * (v 2) ^ 2 * v 3) + (2 : ℝ) * ((v 1) ^ 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 1) ^ 2 * v 2 * v 4) + (2 : ℝ) * (v 0 * (v 4) ^ 3) + (-2 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * v 2 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * (v 2) ^ 2 * v 3) + (-2 : ℝ) * (v 0 * v 1 * (v 4) ^ 2) + (-2 : ℝ) * (v 0 * v 1 * v 2 * v 4) = 0 := by
      nlinarith [hfold]
    have g7 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (2 : ℝ) * (v 3 * h 0) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + -(v 2 * h 1) + (2 : ℝ) * (v 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 2) ^ 2 * v 3) + v 1 * h 0 + (-2 : ℝ) * (v 1 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * v 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork82, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + -(v 1 * v 2 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 2 * v 3 * h 0) + -((v 1) ^ 2 * v 4 * h 0) + v 0 * (v 4) ^ 2 * h 1 + -(v 0 * (v 4) ^ 2 * h 0) + v 0 * v 2 * v 4 * h 1 + (-2 : ℝ) * (v 0 * v 2 * v 3 * h 0) + v 0 * v 1 * v 4 * h 0 = 0 := by
      linear_combination
        (v 4 * h 1 + -(v 4 * h 0) + -(v 2 * h 1) + v 1 * h 0) * g4 +
      (v 2) * g5 +
      (v 1 * v 2 + -(v 0 * v 2)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork82, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork82, CodedBimolNetwork.toNetwork,
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

theorem cubicResidualNetwork82_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork82.toNetwork := by
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
  simp [cubicResidualNetwork82, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork82_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork82.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork82_jacobianNonzero
    cubicResidualNetwork82_fourCharts

def cubicResidualNetwork83 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xx, .xy), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork83_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork83.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork83, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g3 : (2 : ℝ) * (v 1 * (v 4) ^ 3) + (2 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * (v 2) ^ 2 * v 3) + (-2 : ℝ) * (v 0 * (v 4) ^ 3) + (-2 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * v 2 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * (v 2) ^ 2 * v 3) + (2 : ℝ) * (v 0 * v 1 * (v 4) ^ 2) + (-2 : ℝ) * (v 0 * v 1 * v 2 * v 4) + (-2 : ℝ) * ((v 0) ^ 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 0) ^ 2 * v 2 * v 4) = 0 := by
      nlinarith [hfold]
    have g4 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (-2 : ℝ) * (v 3 * h 0) + (2 : ℝ) * (v 3 * (v 4) ^ 2) + v 2 * h 1 + (-2 : ℝ) * (v 2 * (v 4) ^ 2) + (-2 : ℝ) * ((v 2) ^ 2 * v 3) + -(v 0 * h 0) + (2 : ℝ) * (v 0 * (v 4) ^ 2) + (-2 : ℝ) * (v 0 * v 2 * v 4) = 0 := by
      nlinarith [hc0]
    have g5 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + (2 : ℝ) * (v 3 * h 0) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + -(v 2 * h 1) + (2 : ℝ) * (v 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 2) ^ 2 * v 3) + v 1 * h 0 + (-2 : ℝ) * (v 0 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * v 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork83, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + -(v 1 * v 2 * v 4 * h 1) + (-2 : ℝ) * (v 1 * v 2 * v 3 * h 0) + -(v 0 * (v 4) ^ 2 * h 1) + v 0 * (v 4) ^ 2 * h 0 + v 0 * v 2 * v 4 * h 1 + (2 : ℝ) * (v 0 * v 2 * v 3 * h 0) + -(v 0 * v 1 * v 4 * h 0) + (v 0) ^ 2 * v 4 * h 0 = 0 := by
      linear_combination
        (v 4 * h 1 + -(v 4 * h 0) + (2 : ℝ) * (v 3 * h 1) + (2 : ℝ) * (v 3 * h 0) + -(v 2 * h 0) + v 0 * h 1) * g2 +
      ((-2 : ℝ) * (v 3) + -(v 0)) * g3 +
      ((4 : ℝ) * ((v 3) ^ 2) + -((v 2) ^ 2) + (2 : ℝ) * (v 1 * v 3) + (2 : ℝ) * (v 0 * v 3) + v 0 * v 1) * g4 +
      ((4 : ℝ) * ((v 3) ^ 2) + -((v 2) ^ 2) + (4 : ℝ) * (v 0 * v 3) + (v 0) ^ 2) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork83, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork83, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork83, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g5 : (2 : ℝ) * (v 1 * (v 4) ^ 3) + (2 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * (v 2) ^ 2 * v 3) + (2 : ℝ) * ((v 1) ^ 2 * (v 4) ^ 2) + (-2 : ℝ) * ((v 1) ^ 2 * v 2 * v 4) + (-2 : ℝ) * (v 0 * (v 4) ^ 3) + (-2 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * v 2 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * (v 2) ^ 2 * v 3) + (-2 : ℝ) * (v 0 * v 1 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * v 1 * v 2 * v 4) = 0 := by
      nlinarith [hfold]
    have g7 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + (2 : ℝ) * (v 3 * h 0) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + -(v 2 * h 1) + (2 : ℝ) * (v 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 2) ^ 2 * v 3) + v 1 * h 0 + (-2 : ℝ) * (v 1 * (v 4) ^ 2) + (2 : ℝ) * (v 1 * v 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork83, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + v 1 * v 2 * v 4 * h 1 + (2 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (v 1) ^ 2 * v 4 * h 0 + v 0 * (v 4) ^ 2 * h 1 + -(v 0 * (v 4) ^ 2 * h 0) + -(v 0 * v 2 * v 4 * h 1) + (-2 : ℝ) * (v 0 * v 2 * v 3 * h 0) + -(v 0 * v 1 * v 4 * h 0) = 0 := by
      linear_combination
        (-(v 4 * h 1) + v 4 * h 0 + -(v 2 * h 1) + v 1 * h 0) * g4 +
      (v 2) * g5 +
      (v 1 * v 2 + -(v 0 * v 2)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork83, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork83, CodedBimolNetwork.toNetwork,
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

theorem cubicResidualNetwork83_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork83.toNetwork := by
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
  simp [cubicResidualNetwork83, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork83_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork83.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork83_jacobianNonzero
    cubicResidualNetwork83_fourCharts

def cubicResidualNetwork84 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xx, .xy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork84_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork84.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork84, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g2 : (-4 : ℝ) * (v 1 * v 4) + -(v 1 * v 2) + (4 : ℝ) * (v 0 * v 4) + v 0 * v 2 = 0 := by
      nlinarith [hdet]
    simp [-mul_eq_zero, cubicResidualNetwork84, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (8 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 3 * v 4 * h 0) + (-2 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (-8 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (8 : ℝ) * (v 0 * v 3 * v 4 * h 0) + (2 : ℝ) * (v 0 * v 2 * v 3 * h 0) + (4 : ℝ) * (v 0 * v 1 * v 4 * h 1) + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) = 0 := by
      linear_combination
        ((16 : ℝ) * ((v 4) ^ 2 * h 1) + (8 : ℝ) * (v 2 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 4 * h 1) + (8 : ℝ) * (v 0 * v 4 * h 1) + (2 : ℝ) * (v 0 * v 3 * h 1) + (2 : ℝ) * (v 0 * v 1 * h 1)) * g0 +
      ((16 : ℝ) * ((v 4) ^ 2 * h 1) + (8 : ℝ) * (v 2 * v 4 * h 1) + (2 : ℝ) * (v 0 * v 3 * h 1) + (2 : ℝ) * ((v 0) ^ 2 * h 1)) * g1 +
      ((2 : ℝ) * (v 3 * h 0) + (2 : ℝ) * (v 0 * h 1)) * g2
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork84, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork84, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork84, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : (4 : ℝ) * (v 4) + v 2 = 0 := by
      nlinarith [hg1]
    have g2 : (2 : ℝ) * (v 4) + -(v 3) + v 2 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) + v 1 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork84, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
        ((-4 : ℝ) * (v 1 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 4 * h 0) + (-4 : ℝ) * (v 1 * v 3 * h 1) + -(v 1 * v 2 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * h 1) + (4 : ℝ) * (v 0 * v 4 * h 0) + v 0 * v 2 * h 1 + v 0 * v 2 * h 0 + -(v 0 * v 1 * h 1) + -((v 0) ^ 2 * h 1)) * g0 +
      ((-8 : ℝ) * (v 1 * v 3 * h 1) + (-2 : ℝ) * ((v 1) ^ 2 * h 1) + (2 : ℝ) * (v 0 * v 3 * h 1) + -(v 0 * v 1 * h 0) + -((v 0) ^ 2 * h 1) + (v 0) ^ 2 * h 0) * g1 +
      ((6 : ℝ) * (v 1 * v 3 * h 1) + (2 : ℝ) * ((v 1) ^ 2 * h 1) + (v 0) ^ 2 * h 1) * g2 +
      ((-2 : ℝ) * (v 1 * v 3 * h 1) + -((v 0) ^ 2 * h 1)) * g3
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork84, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork84, CodedBimolNetwork.toNetwork,
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

theorem cubicResidualNetwork84_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork84.toNetwork := by
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
  simp [cubicResidualNetwork84, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork84_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork84.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork84_jacobianNonzero
    cubicResidualNetwork84_fourCharts

def cubicResidualNetwork85 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork85_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork85.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork85, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : v 4 + -(v 3) + (2 : ℝ) * (v 2) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g1 : -(v 4) + v 3 + -(v 2) + v 1 = 0 := by
      nlinarith [heq1]
    have g2 : v 2 * v 4 + (-2 : ℝ) * (v 2 * v 3) + -(v 1 * v 4) + (-2 : ℝ) * (v 1 * v 2) + v 0 * v 4 + v 0 * v 2 = 0 := by
      nlinarith [hdet]
    have g4 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + (-2 : ℝ) * (v 3 * h 0) + (2 : ℝ) * (v 3 * (v 4) ^ 2) + (2 : ℝ) * (v 2 * h 1) + (-4 : ℝ) * (v 2 * (v 4) ^ 2) + (-8 : ℝ) * ((v 2) ^ 2 * v 3) + -(v 0 * h 0) + (2 : ℝ) * (v 0 * (v 4) ^ 2) + (4 : ℝ) * (v 0 * v 2 * v 4) = 0 := by
      nlinarith [hc0]
    have g5 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (2 : ℝ) * (v 3 * h 0) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + -(v 2 * h 1) + (4 : ℝ) * (v 2 * (v 4) ^ 2) + (8 : ℝ) * ((v 2) ^ 2 * v 3) + v 1 * h 0 + (-2 : ℝ) * (v 0 * (v 4) ^ 2) + (-4 : ℝ) * (v 0 * v 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork85, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + (2 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 2 * v 3 * h 0) + -(v 0 * (v 4) ^ 2 * h 1) + v 0 * (v 4) ^ 2 * h 0 + (-2 : ℝ) * (v 0 * v 2 * v 4 * h 1) + (4 : ℝ) * (v 0 * v 2 * v 3 * h 0) + v 0 * v 1 * v 4 * h 0 + -((v 0) ^ 2 * v 4 * h 0) = 0 := by
      linear_combination
        ((3 : ℝ) * ((v 4) ^ 2 * h 0) + (5 : ℝ) * (v 3 * v 4 * h 1) + (-4 : ℝ) * (v 3 * v 4 * h 0) + (-4 : ℝ) * ((v 3) ^ 2 * h 1) + (4 : ℝ) * (v 2 * v 4 * h 1) + (-2 : ℝ) * (v 2 * v 4 * h 0) + (-8 : ℝ) * ((v 2) ^ 2 * h 0) + v 1 * v 4 * h 1 + (-5 : ℝ) * (v 1 * v 4 * h 0) + (-4 : ℝ) * (v 1 * v 3 * h 1) + (4 : ℝ) * ((v 1) ^ 2 * h 0) + -(v 0 * v 4 * h 1) + (-2 : ℝ) * (v 0 * v 4 * h 0) + v 0 * v 3 * h 1 + (4 : ℝ) * (v 0 * v 3 * h 0) + -(v 0 * v 2 * h 1) + v 0 * v 1 * h 1) * g0 +
      ((3 : ℝ) * ((v 4) ^ 2 * h 0) + (5 : ℝ) * (v 3 * v 4 * h 1) + (-4 : ℝ) * (v 3 * v 4 * h 0) + (-4 : ℝ) * ((v 3) ^ 2 * h 1) + (4 : ℝ) * (v 2 * v 4 * h 1) + (4 : ℝ) * (v 2 * v 3 * h 1) + (4 : ℝ) * ((v 2) ^ 2 * h 1) + (-16 : ℝ) * ((v 2) ^ 2 * h 0) + (4 : ℝ) * (v 1 * v 2 * h 1) + (-4 : ℝ) * (v 1 * v 2 * h 0) + (4 : ℝ) * ((v 1) ^ 2 * h 0) + (-7 : ℝ) * (v 0 * v 4 * h 0) + (-3 : ℝ) * (v 0 * v 3 * h 1) + (4 : ℝ) * (v 0 * v 3 * h 0) + (-2 : ℝ) * (v 0 * v 2 * h 1) + (v 0) ^ 2 * h 1) * g1 +
      (-(v 4 * h 0) + (-4 : ℝ) * (v 2 * h 0)) * g2 +
      (-(v 3 * v 4) + (4 : ℝ) * ((v 2) ^ 2) + (-4 : ℝ) * ((v 1) ^ 2) + (3 : ℝ) * (v 0 * v 4) + (-4 : ℝ) * (v 0 * v 3)) * g4 +
      (-(v 3 * v 4) + (4 : ℝ) * ((v 2) ^ 2) + (-4 : ℝ) * ((v 1) ^ 2) + (3 : ℝ) * (v 0 * v 4) + (-4 : ℝ) * (v 0 * v 3)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork85, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : -(v 4) + (2 : ℝ) * (v 3) + v 1 = 0 := by
      nlinarith [hg1]
    have g2 : v 4 + -(v 3) + (2 : ℝ) * (v 2) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : -(v 4) + v 3 + -(v 2) + v 1 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork85, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 2 * (v 4) ^ 2 * h 1 + -(v 2 * (v 4) ^ 2 * h 0) + (2 : ℝ) * ((v 2) ^ 2 * v 4 * h 1) + (-4 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + v 0 * v 2 * v 4 * h 0 = 0 := by
      linear_combination
        ((2 : ℝ) * (v 2 * v 4 * h 1) + (-3 : ℝ) * (v 2 * v 4 * h 0) + (-4 : ℝ) * (v 2 * v 3 * h 1) + (-4 : ℝ) * ((v 2) ^ 2 * h 0) + -((v 1) ^ 2 * h 1)) * g0 +
      ((5 : ℝ) * (v 2 * v 4 * h 1) + (-4 : ℝ) * (v 2 * v 4 * h 0) + (-6 : ℝ) * (v 2 * v 3 * h 1) + (-8 : ℝ) * ((v 2) ^ 2 * h 0) + -(v 1 * v 2 * h 1) + -((v 1) ^ 2 * h 1)) * g1 +
      ((-2 : ℝ) * (v 2 * v 4 * h 1) + (2 : ℝ) * (v 2 * v 4 * h 0) + (4 : ℝ) * (v 2 * v 3 * h 1) + (4 : ℝ) * ((v 2) ^ 2 * h 0) + (v 1) ^ 2 * h 1) * g2 +
      ((-6 : ℝ) * (v 2 * v 4 * h 1) + (4 : ℝ) * (v 2 * v 4 * h 0) + (8 : ℝ) * (v 2 * v 3 * h 1) + (8 : ℝ) * ((v 2) ^ 2 * h 0) + (v 1) ^ 2 * h 1) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork85, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : v 4 + (2 : ℝ) * (v 2) = 0 := by
      nlinarith [hg1]
    have g2 : v 4 + -(v 3) + (2 : ℝ) * (v 2) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : -(v 4) + v 3 + -(v 2) + v 1 = 0 := by
      nlinarith [heq1]
    have g6 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + (-2 : ℝ) * (v 3 * h 0) + (2 : ℝ) * (v 3 * (v 4) ^ 2) + (2 : ℝ) * (v 2 * h 1) + (-2 : ℝ) * (v 2 * (v 4) ^ 2) + (-2 : ℝ) * ((v 2) ^ 2 * v 3) + (2 : ℝ) * (v 1 * (v 4) ^ 2) + (2 : ℝ) * (v 1 * v 2 * v 4) + -(v 0 * h 0) = 0 := by
      nlinarith [hc0]
    have g7 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (2 : ℝ) * (v 3 * h 0) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + -(v 2 * h 1) + (2 : ℝ) * (v 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 2) ^ 2 * v 3) + v 1 * h 0 + (-2 : ℝ) * (v 1 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * v 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork85, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + -(v 1 * v 2 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 2 * v 3 * h 0) + -((v 1) ^ 2 * v 4 * h 0) + v 0 * (v 4) ^ 2 * h 1 + -(v 0 * (v 4) ^ 2 * h 0) + v 0 * v 2 * v 4 * h 1 + (-2 : ℝ) * (v 0 * v 2 * v 3 * h 0) + v 0 * v 1 * v 4 * h 0 = 0 := by
      linear_combination
        (((-1 : ℝ) / 2) * ((v 4) ^ 2 * h 1) + (-2 : ℝ) * (v 1 * v 2 * h 0) + -(v 0 * v 4 * h 0)) * g0 +
      (((-1 : ℝ) / 2) * ((v 4) ^ 2 * h 1) + v 1 * v 4 * h 0 + -(v 1 * v 2 * h 1) + (-2 : ℝ) * (v 1 * v 2 * h 0) + -((v 1) ^ 2 * h 0) + ((1 : ℝ) / 2) * (v 0 * v 4 * h 1) + -(v 0 * v 4 * h 0) + -(v 0 * v 3 * h 0) + v 0 * v 1 * h 0) * g1 +
      ((2 : ℝ) * (v 1 * v 2 * h 0) + v 0 * v 4 * h 0) * g2 +
      (-((v 4) ^ 2 * h 1)) * g3 +
      ((2 : ℝ) * (v 1 * v 2)) * g6 +
      ((2 : ℝ) * (v 1 * v 2)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork85, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : v 4 + (2 : ℝ) * (v 2) = 0 := by
      nlinarith [hg1]
    have g2 : -(v 4) + (2 : ℝ) * (v 3) + v 1 = 0 := by
      nlinarith [hg2]
    have g3 : v 4 + -(v 3) + (2 : ℝ) * (v 2) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g4 : -(v 4) + v 3 + -(v 2) + v 1 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork85, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -(v 2 * (v 4) ^ 2 * h 1) + v 2 * (v 4) ^ 2 * h 0 + -((v 2) ^ 2 * v 4 * h 1) + (2 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + -(v 1 * v 2 * v 4 * h 0) = 0 := by
      linear_combination
        (((1 : ℝ) / 2) * ((v 4) ^ 2 * h 1) + ((-1 : ℝ) / 2) * ((v 4) ^ 2 * h 0)) * g0 +
      (((-1 : ℝ) / 2) * ((v 4) ^ 2 * h 1) + ((1 : ℝ) / 2) * ((v 4) ^ 2 * h 0) + ((1 : ℝ) / 2) * (v 3 * v 4 * h 1) + ((-1 : ℝ) / 2) * (v 3 * v 4 * h 0) + ((-1 : ℝ) / 2) * (v 2 * v 4 * h 1) + -(v 2 * v 3 * h 1) + v 2 * v 3 * h 0 + (2 : ℝ) * ((v 2) ^ 2 * h 1) + ((-1 : ℝ) / 2) * (v 1 * v 4 * h 0) + ((1 : ℝ) / 2) * (v 0 * v 4 * h 1) + -(v 0 * v 2 * h 1)) * g1 +
      (((1 : ℝ) / 2) * ((v 4) ^ 2 * h 1) + ((-1 : ℝ) / 2) * ((v 4) ^ 2 * h 0)) * g2 +
      (((1 : ℝ) / 2) * ((v 4) ^ 2 * h 0) + (-2 : ℝ) * ((v 2) ^ 2 * h 1)) * g3 +
      (((-1 : ℝ) / 2) * ((v 4) ^ 2 * h 1) + (v 4) ^ 2 * h 0) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork85_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork85.toNetwork := by
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
  simp [cubicResidualNetwork85, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork85_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork85.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork85_jacobianNonzero
    cubicResidualNetwork85_fourCharts

end SmallCusp

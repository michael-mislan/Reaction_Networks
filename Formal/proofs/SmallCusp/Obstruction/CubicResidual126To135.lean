import proofs.SmallCusp.Obstruction.CubicDegeneracy
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

def cubicResidualNetwork126 : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.x, .yy), (.y, .yy), (.xy, .zero), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork126_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork126.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork126, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 3) + -(v 1) + v 0 = 0 := by
      nlinarith [heq0]
    have g1 : (-2 : ℝ) * (v 4) + -(v 3) + v 2 + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [heq1]
    have g2 : (4 : ℝ) * (v 3 * v 4) + -(v 2 * v 3) + (4 : ℝ) * (v 1 * v 4) + (3 : ℝ) * (v 1 * v 3) + -(v 1 * v 2) + (-4 : ℝ) * (v 0 * v 4) + -(v 0 * v 3) + v 0 * v 2 = 0 := by
      nlinarith [hdet]
    simp [-mul_eq_zero, cubicResidualNetwork126, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * ((v 3) ^ 2 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (3 : ℝ) * (v 1 * (v 3) ^ 2 * h 1) + (-3 : ℝ) * (v 1 * (v 3) ^ 2 * h 0) + (-4 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (-3 : ℝ) * ((v 1) ^ 2 * v 3 * h 0) + (8 : ℝ) * (v 0 * v 3 * v 4 * h 1) + -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 + (8 : ℝ) * (v 0 * v 1 * v 4 * h 1) + (4 : ℝ) * (v 0 * v 1 * v 3 * h 0) + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) + -((v 0) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((8 : ℝ) * (v 3 * v 4 * h 1) + (-4 : ℝ) * (v 3 * v 4 * h 0) + -(v 2 * v 3 * h 1) + v 2 * v 3 * h 0 + (-4 : ℝ) * (v 1 * v 4 * h 0) + (-2 : ℝ) * (v 1 * v 3 * h 1) + (2 : ℝ) * (v 1 * v 2 * h 1) + v 1 * v 2 * h 0 + (4 : ℝ) * ((v 1) ^ 2 * h 1) + (-8 : ℝ) * (v 0 * v 4 * h 1) + (4 : ℝ) * (v 0 * v 4 * h 0) + (-2 : ℝ) * (v 0 * v 3 * h 1) + (2 : ℝ) * (v 0 * v 2 * h 1) + -(v 0 * v 2 * h 0) + (4 : ℝ) * (v 0 * v 1 * h 1)) * g0 +
      ((2 : ℝ) * (v 1 * v 3 * h 1) + (2 : ℝ) * ((v 1) ^ 2 * h 1) + (2 : ℝ) * (v 0 * v 3 * h 1) + (-2 : ℝ) * ((v 0) ^ 2 * h 1)) * g1 +
      (v 3 * h 1 + -(v 3 * h 0) + -(v 1 * h 0) + v 0 * h 0) * g2
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork126, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 3) + -(v 1) + v 0 = 0 := by
      nlinarith [hg0]
    have g1 : -(v 3) + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [hg1]
    have g2 : -(v 3) + -(v 1) + v 0 = 0 := by
      nlinarith [heq0]
    have g6 : -(v 3 * h 1) + -(v 3 * h 0) + (2 : ℝ) * ((v 3) ^ 3) + -(v 1 * h 0) + (2 : ℝ) * (v 1 * (v 3) ^ 2) + v 0 * h 0 + (-2 : ℝ) * (v 0 * (v 3) ^ 2) = 0 := by
      nlinarith [hc0]
    have g7 : (-4 : ℝ) * (v 4 * h 1) + -(v 3 * h 1) + -(v 3 * h 0) + (-4 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + v 2 * h 1 + (2 : ℝ) * (v 1 * h 0) + (-8 : ℝ) * (v 1 * v 3 * v 4) + (2 : ℝ) * (v 1 * (v 3) ^ 2) + (-4 : ℝ) * ((v 1) ^ 2 * v 4) + (8 : ℝ) * (v 0 * v 3 * v 4) + (-2 : ℝ) * (v 0 * (v 3) ^ 2) + (8 : ℝ) * (v 0 * v 1 * v 4) + (-4 : ℝ) * ((v 0) ^ 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork126, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-8 : ℝ) * ((v 3) ^ 2 * v 4 * h 1) + (4 : ℝ) * ((v 3) ^ 2 * v 4 * h 0) + v 2 * (v 3) ^ 2 * h 1 + -(v 2 * (v 3) ^ 2 * h 0) + (-4 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (4 : ℝ) * (v 1 * v 3 * v 4 * h 0) + -(v 1 * v 2 * v 3 * h 0) + (4 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (-4 : ℝ) * (v 0 * v 3 * v 4 * h 0) + v 0 * v 2 * v 3 * h 0 = 0 := by
      linear_combination
        ((4 : ℝ) * (v 1 * v 4 * h 1)) * g0 +
      ((2 : ℝ) * (v 3 * v 4 * h 1) + (-6 : ℝ) * (v 3 * v 4 * h 0) + v 2 * v 3 * h 0 + (2 : ℝ) * (v 1 * v 4 * h 1) + (-6 : ℝ) * (v 1 * v 4 * h 0) + (3 : ℝ) * (v 1 * v 3 * h 0) + v 1 * v 2 * h 0 + (2 : ℝ) * ((v 1) ^ 2 * h 0) + (-2 : ℝ) * (v 0 * v 4 * h 1) + (6 : ℝ) * (v 0 * v 4 * h 0) + -(v 0 * v 3 * h 0) + -(v 0 * v 2 * h 0) + (-2 : ℝ) * (v 0 * v 1 * h 0)) * g1 +
      ((-14 : ℝ) * (v 1 * v 4 * h 0) + (2 : ℝ) * (v 1 * v 2 * h 0) + (4 : ℝ) * ((v 1) ^ 2 * h 0) + (2 : ℝ) * (v 0 * v 4 * h 0)) * g2 +
      ((2 : ℝ) * (v 3 * v 4) + -((v 3) ^ 2) + (2 : ℝ) * (v 1 * v 4) + (-2 : ℝ) * (v 0 * v 4)) * g6 +
      ((v 3) ^ 2) * g7
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork126, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 3) + -(v 1) + v 0 = 0 := by
      nlinarith [hg0]
    have g1 : -(v 3) = 0 := by
      nlinarith [hg1]
    simp [-mul_eq_zero, cubicResidualNetwork126, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * ((v 3) ^ 2 * v 4 * h 1) + (16 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (3 : ℝ) * (v 1 * (v 3) ^ 2 * h 1) + (-3 : ℝ) * (v 1 * (v 3) ^ 2 * h 0) + (-3 : ℝ) * (v 1 * v 2 * v 3 * h 1) + (8 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (6 : ℝ) * ((v 1) ^ 2 * v 3 * h 0) + -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 + v 0 * v 2 * v 3 * h 1 + (-8 : ℝ) * (v 0 * v 1 * v 4 * h 1) + (-2 : ℝ) * (v 0 * v 1 * v 3 * h 0) = 0 := by
      linear_combination
        ((-8 : ℝ) * (v 1 * v 4 * h 1)) * g0 +
      ((4 : ℝ) * (v 3 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 4 * h 1) + (-3 : ℝ) * (v 1 * v 3 * h 1) + (3 : ℝ) * (v 1 * v 3 * h 0) + (3 : ℝ) * (v 1 * v 2 * h 1) + (-6 : ℝ) * ((v 1) ^ 2 * h 0) + v 0 * v 3 * h 1 + -(v 0 * v 3 * h 0) + -(v 0 * v 2 * h 1) + (2 : ℝ) * (v 0 * v 1 * h 0)) * g1
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork126, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : -(v 3) = 0 := by
      nlinarith [hg1]
    simp [-mul_eq_zero, cubicResidualNetwork126, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-16 : ℝ) * (v 3 * (v 4) ^ 2 * h 1) + (-8 : ℝ) * ((v 3) ^ 2 * v 4 * h 1) + (4 : ℝ) * ((v 3) ^ 2 * v 4 * h 0) + (8 : ℝ) * (v 2 * v 3 * v 4 * h 1) + v 2 * (v 3) ^ 2 * h 1 + -(v 2 * (v 3) ^ 2 * h 0) + -((v 2) ^ 2 * v 3 * h 1) + (8 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 3 * v 4 * h 0) + (2 : ℝ) * (v 1 * v 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((16 : ℝ) * ((v 4) ^ 2 * h 1) + (8 : ℝ) * (v 3 * v 4 * h 1) + (-4 : ℝ) * (v 3 * v 4 * h 0) + (-8 : ℝ) * (v 2 * v 4 * h 1) + -(v 2 * v 3 * h 1) + v 2 * v 3 * h 0 + (v 2) ^ 2 * h 1 + (-8 : ℝ) * (v 1 * v 4 * h 1) + (8 : ℝ) * (v 1 * v 4 * h 0) + (-2 : ℝ) * (v 1 * v 2 * h 0)) * g1
    nlinarith [hcertificate]

theorem cubicResidualNetwork126_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork126.toNetwork := by
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
  simp [cubicResidualNetwork126, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork126_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork126.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork126_jacobianNonzero
    cubicResidualNetwork126_fourCharts

def cubicResidualNetwork127 : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.x, .yy), (.y, .yy), (.xy, .x), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork127_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork127.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork127, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 1) + v 0 = 0 := by
      nlinarith [heq0]
    have g4 : -(v 1 * h 0) + v 0 * h 0 = 0 := by
      nlinarith [hc0]
    simp [-mul_eq_zero, cubicResidualNetwork127, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
        ((4 : ℝ) * (v 1 * v 4 * h 1) + v 1 * v 3 * h 0 + (-4 : ℝ) * (v 0 * v 4 * h 1)) * g0 +
      (-(v 0 * v 3)) * g4
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork127, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork127, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork127, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 1) + v 0 = 0 := by
      nlinarith [hg0]
    have g2 : -(v 1) + v 0 = 0 := by
      nlinarith [heq0]
    simp [-mul_eq_zero, cubicResidualNetwork127, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + -(v 1 * v 2 * v 3 * h 1) + (8 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (2 : ℝ) * ((v 1) ^ 2 * v 3 * h 0) + -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 + v 0 * v 2 * v 3 * h 1 + (-8 : ℝ) * (v 0 * v 1 * v 4 * h 1) + (-2 : ℝ) * (v 0 * v 1 * v 3 * h 0) = 0 := by
      linear_combination
        ((v 3) ^ 2 * h 0 + v 2 * v 3 * h 1 + (-2 : ℝ) * (v 1 * v 3 * h 0)) * g0 +
      (-((v 3) ^ 2 * h 1) + (-8 : ℝ) * (v 1 * v 4 * h 1)) * g2
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork127, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork127, CodedBimolNetwork.toNetwork,
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

theorem cubicResidualNetwork127_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork127.toNetwork := by
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
  simp [cubicResidualNetwork127, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork127_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork127.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork127_jacobianNonzero
    cubicResidualNetwork127_fourCharts

def cubicResidualNetwork128 : CodedBimolNetwork where
  reaction := ![(.x, .y), (.y, .yy), (.xy, .xx), (.yy, .zero), (.yy, .y)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork128_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork128.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork128, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : v 2 + -(v 0) = 0 := by
      nlinarith [heq0]
    simp [-mul_eq_zero, cubicResidualNetwork128, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-2 : ℝ) * ((v 2) ^ 2 * v 4 * h 1) + (-4 : ℝ) * ((v 2) ^ 2 * v 3 * h 1) + (4 : ℝ) * (v 0 * v 2 * v 4 * h 1) + (8 : ℝ) * (v 0 * v 2 * v 3 * h 1) + (-2 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) + (-4 : ℝ) * ((v 0) ^ 2 * v 3 * h 1) = 0 := by
      linear_combination
        ((-2 : ℝ) * (v 2 * v 4 * h 1) + (-4 : ℝ) * (v 2 * v 3 * h 1) + (2 : ℝ) * (v 0 * v 4 * h 1) + (4 : ℝ) * (v 0 * v 3 * h 1)) * g0
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork128, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : v 2 + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : -(v 2) + v 0 = 0 := by
      nlinarith [hg1]
    have g2 : v 2 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g4 : (-2 : ℝ) * (v 2 * v 4) + (-4 : ℝ) * (v 2 * v 3) + v 1 * v 2 + (2 : ℝ) * (v 0 * v 4) + (4 : ℝ) * (v 0 * v 3) + -(v 0 * v 1) = 0 := by
      nlinarith [hdet]
    have g6 : v 2 * h 1 + v 2 * h 0 + (-2 : ℝ) * ((v 2) ^ 3) + -(v 0 * h 0) + (2 : ℝ) * (v 0 * (v 2) ^ 2) = 0 := by
      nlinarith [hc0]
    simp [-mul_eq_zero, cubicResidualNetwork128, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * ((v 2) ^ 2 * v 4 * h 1) + (2 : ℝ) * ((v 2) ^ 2 * v 4 * h 0) + (-8 : ℝ) * ((v 2) ^ 2 * v 3 * h 1) + (4 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + v 1 * (v 2) ^ 2 * h 1 + -(v 1 * (v 2) ^ 2 * h 0) + (2 : ℝ) * (v 0 * v 2 * v 4 * h 1) + (-2 : ℝ) * (v 0 * v 2 * v 4 * h 0) + (4 : ℝ) * (v 0 * v 2 * v 3 * h 1) + (-4 : ℝ) * (v 0 * v 2 * v 3 * h 0) + v 0 * v 1 * v 2 * h 0 = 0 := by
      linear_combination
        ((4 : ℝ) * (v 0 * v 3 * h 0)) * g0 +
      ((8 : ℝ) * (v 2 * v 3 * h 1) + v 1 * v 2 * h 0 + (-2 : ℝ) * (v 0 * v 4 * h 0)) * g1 +
      ((-4 : ℝ) * (v 2 * v 4 * h 1) + (2 : ℝ) * (v 2 * v 4 * h 0) + (4 : ℝ) * (v 2 * v 3 * h 0) + v 1 * v 2 * h 1 + -(v 0 * v 1 * h 0)) * g2 +
      ((2 : ℝ) * (v 0 * (v 2) ^ 2)) * g4 +
      ((-2 : ℝ) * (v 0 * v 4) + (-4 : ℝ) * (v 0 * v 3) + v 0 * v 1) * g6
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork128, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : v 2 + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : v 2 = 0 := by
      nlinarith [hg1]
    simp [-mul_eq_zero, cubicResidualNetwork128, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (2 : ℝ) * ((v 2) ^ 2 * v 4 * h 1) + (4 : ℝ) * ((v 2) ^ 2 * v 3 * h 1) + (-4 : ℝ) * (v 0 * v 2 * v 4 * h 1) + (-8 : ℝ) * (v 0 * v 2 * v 3 * h 1) + (2 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) + (4 : ℝ) * ((v 0) ^ 2 * v 3 * h 1) = 0 := by
      linear_combination
        ((-2 : ℝ) * (v 0 * v 4 * h 1) + (-4 : ℝ) * (v 0 * v 3 * h 1)) * g0 +
      ((2 : ℝ) * (v 2 * v 4 * h 1) + (4 : ℝ) * (v 2 * v 3 * h 1) + (-2 : ℝ) * (v 0 * v 4 * h 1) + (-4 : ℝ) * (v 0 * v 3 * h 1)) * g1
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork128, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : v 2 = 0 := by
      nlinarith [hg1]
    simp [-mul_eq_zero, cubicResidualNetwork128, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (16 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (16 : ℝ) * (v 2 * (v 3) ^ 2 * h 1) + (4 : ℝ) * ((v 2) ^ 2 * v 4 * h 1) + (-2 : ℝ) * ((v 2) ^ 2 * v 4 * h 0) + (8 : ℝ) * ((v 2) ^ 2 * v 3 * h 1) + (-4 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + (-4 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 2 * v 3 * h 1) + -(v 1 * (v 2) ^ 2 * h 1) + v 1 * (v 2) ^ 2 * h 0 + (v 1) ^ 2 * v 2 * h 1 + (-2 : ℝ) * (v 0 * v 2 * v 4 * h 1) + (2 : ℝ) * (v 0 * v 2 * v 4 * h 0) + (-4 : ℝ) * (v 0 * v 2 * v 3 * h 1) + (4 : ℝ) * (v 0 * v 2 * v 3 * h 0) + -(v 0 * v 1 * v 2 * h 0) = 0 := by
      linear_combination
        ((4 : ℝ) * ((v 4) ^ 2 * h 1) + (16 : ℝ) * (v 3 * v 4 * h 1) + (16 : ℝ) * ((v 3) ^ 2 * h 1) + (4 : ℝ) * (v 2 * v 4 * h 1) + (-2 : ℝ) * (v 2 * v 4 * h 0) + (8 : ℝ) * (v 2 * v 3 * h 1) + (-4 : ℝ) * (v 2 * v 3 * h 0) + (-4 : ℝ) * (v 1 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 3 * h 1) + -(v 1 * v 2 * h 1) + v 1 * v 2 * h 0 + (v 1) ^ 2 * h 1 + (-2 : ℝ) * (v 0 * v 4 * h 1) + (2 : ℝ) * (v 0 * v 4 * h 0) + (-4 : ℝ) * (v 0 * v 3 * h 1) + (4 : ℝ) * (v 0 * v 3 * h 0) + -(v 0 * v 1 * h 0)) * g1
    nlinarith [hcertificate]

theorem cubicResidualNetwork128_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork128.toNetwork := by
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
  simp [cubicResidualNetwork128, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork128_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork128.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork128_jacobianNonzero
    cubicResidualNetwork128_fourCharts

def cubicResidualNetwork129 : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xx, .x), (.xy, .x)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork129_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork129.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork129, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g2 : (2 : ℝ) * (v 3 * v 4) + (4 : ℝ) * (v 2 * v 4) + (-2 : ℝ) * (v 1 * v 3) + (-4 : ℝ) * (v 1 * v 2) + -(v 0 * v 4) + v 0 * v 1 = 0 := by
      nlinarith [hdet]
    have g4 : (-2 : ℝ) * (v 3 * h 0) + (-4 : ℝ) * (v 2 * h 0) + v 0 * h 0 = 0 := by
      nlinarith [hc0]
    have g5 : -(v 4 * h 1) + -(v 4 * h 0) + v 1 * h 1 = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork129, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * ((v 3) ^ 2 * v 4 * h 0) + (-16 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (-16 : ℝ) * ((v 2) ^ 2 * v 4 * h 0) + (4 : ℝ) * (v 0 * v 3 * v 4 * h 0) + (8 : ℝ) * (v 0 * v 2 * v 4 * h 0) + -((v 0) ^ 2 * v 4 * h 0) = 0 := by
      linear_combination
        ((2 : ℝ) * (v 3 * h 1) + -(v 0 * h 1)) * g2 +
      ((4 : ℝ) * (v 2 * v 4)) * g4 +
      ((4 : ℝ) * ((v 3) ^ 2) + (8 : ℝ) * (v 2 * v 3) + (-4 : ℝ) * (v 0 * v 3) + (-4 : ℝ) * (v 0 * v 2) + (v 0) ^ 2) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork129, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork129, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork129, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : (-2 : ℝ) * (v 3) + (-4 : ℝ) * (v 2) + v 0 = 0 := by
      nlinarith [hg0]
    have g3 : -(v 4) + v 1 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork129, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (2 : ℝ) * (v 3 * (v 4) ^ 2 * h 1) + (-4 : ℝ) * (v 3 * (v 4) ^ 2 * h 0) + (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 3 * v 4 * h 0) + (-4 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (4 : ℝ) * (v 1 * v 2 * v 4 * h 0) + -(v 0 * (v 4) ^ 2 * h 1) + v 0 * (v 4) ^ 2 * h 0 + v 0 * v 1 * v 4 * h 1 = 0 := by
      linear_combination
        ((v 1) ^ 2 * h 0) * g0 +
      ((-2 : ℝ) * (v 3 * v 4 * h 1) + (4 : ℝ) * (v 3 * v 4 * h 0) + (-4 : ℝ) * (v 2 * v 4 * h 1) + (8 : ℝ) * (v 2 * v 4 * h 0) + (2 : ℝ) * (v 1 * v 3 * h 0) + (4 : ℝ) * (v 1 * v 2 * h 0) + v 0 * v 4 * h 1 + -(v 0 * v 4 * h 0) + -(v 0 * v 1 * h 0)) * g3
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork129, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : (-2 : ℝ) * (v 3) + (-4 : ℝ) * (v 2) + v 0 = 0 := by
      nlinarith [hg0]
    have g7 : (-2 : ℝ) * (v 3 * h 0) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + (-4 : ℝ) * (v 2 * h 0) + (-4 : ℝ) * (v 2 * (v 4) ^ 2) + (4 : ℝ) * (v 1 * v 3 * v 4) + (8 : ℝ) * (v 1 * v 2 * v 4) + (-2 : ℝ) * ((v 1) ^ 2 * v 3) + (-4 : ℝ) * ((v 1) ^ 2 * v 2) + v 0 * h 0 = 0 := by
      nlinarith [hc0]
    simp [-mul_eq_zero, cubicResidualNetwork129, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-2 : ℝ) * (v 3 * (v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (4 : ℝ) * (v 1 * v 3 * v 4 * h 0) + (8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * v 3 * h 0) + (-4 : ℝ) * ((v 1) ^ 2 * v 2 * h 0) = 0 := by
      linear_combination
        (-((h 0) ^ 2)) * g0 +
      (h 0) * g7
    nlinarith [hcertificate]

theorem cubicResidualNetwork129_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork129.toNetwork := by
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
  simp [cubicResidualNetwork129, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork129_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork129.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork129_jacobianNonzero
    cubicResidualNetwork129_fourCharts

def cubicResidualNetwork130 : CodedBimolNetwork where
  reaction := ![(.x, .y), (.y, .yy), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork130_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork130.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork130, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 3) + v 2 + -(v 0) = 0 := by
      nlinarith [heq0]
    simp [-mul_eq_zero, cubicResidualNetwork130, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * ((v 3) ^ 2 * v 4 * h 1) + (8 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (-4 : ℝ) * ((v 2) ^ 2 * v 4 * h 1) + (-8 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (8 : ℝ) * (v 0 * v 2 * v 4 * h 1) + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) = 0 := by
      linear_combination
        ((4 : ℝ) * (v 3 * v 4 * h 1) + (-4 : ℝ) * (v 2 * v 4 * h 1) + (4 : ℝ) * (v 0 * v 4 * h 1)) * g0
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork130, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 3) + v 2 + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : v 3 + -(v 2) + v 0 = 0 := by
      nlinarith [hg1]
    have g2 : -(v 3) + v 2 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g4 : (4 : ℝ) * (v 3 * v 4) + (-4 : ℝ) * (v 2 * v 4) + -(v 1 * v 3) + v 1 * v 2 + (4 : ℝ) * (v 0 * v 4) + -(v 0 * v 1) = 0 := by
      nlinarith [hdet]
    have g6 : -(v 3 * h 1) + -(v 3 * h 0) + (2 : ℝ) * ((v 3) ^ 3) + v 2 * h 1 + v 2 * h 0 + (-6 : ℝ) * (v 2 * (v 3) ^ 2) + (6 : ℝ) * ((v 2) ^ 2 * v 3) + (-2 : ℝ) * ((v 2) ^ 3) + -(v 0 * h 0) + (2 : ℝ) * (v 0 * (v 3) ^ 2) + (-4 : ℝ) * (v 0 * v 2 * v 3) + (2 : ℝ) * (v 0 * (v 2) ^ 2) = 0 := by
      nlinarith [hc0]
    simp [-mul_eq_zero, cubicResidualNetwork130, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-8 : ℝ) * ((v 3) ^ 2 * v 4 * h 1) + (4 : ℝ) * ((v 3) ^ 2 * v 4 * h 0) + (16 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (-8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (-8 : ℝ) * ((v 2) ^ 2 * v 4 * h 1) + (4 : ℝ) * ((v 2) ^ 2 * v 4 * h 0) + v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 2 * v 3 * h 1) + (2 : ℝ) * (v 1 * v 2 * v 3 * h 0) + v 1 * (v 2) ^ 2 * h 1 + -(v 1 * (v 2) ^ 2 * h 0) + (-4 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (4 : ℝ) * (v 0 * v 3 * v 4 * h 0) + (4 : ℝ) * (v 0 * v 2 * v 4 * h 1) + (-4 : ℝ) * (v 0 * v 2 * v 4 * h 0) + -(v 0 * v 1 * v 3 * h 0) + v 0 * v 1 * v 2 * h 0 = 0 := by
      linear_combination
        ((4 : ℝ) * (v 3 * v 4 * h 1) + (-8 : ℝ) * (v 3 * v 4 * h 0) + (-2 : ℝ) * (v 1 * v 2 * h 0)) * g0 +
      ((4 : ℝ) * (v 2 * v 4 * h 1) + (-2 : ℝ) * (v 1 * v 3 * h 0)) * g1 +
      ((8 : ℝ) * (v 2 * v 4 * h 0)) * g2 +
      ((-2 : ℝ) * ((v 3) ^ 3) + (6 : ℝ) * (v 2 * (v 3) ^ 2) + (-6 : ℝ) * ((v 2) ^ 2 * v 3) + (2 : ℝ) * ((v 2) ^ 3)) * g4 +
      ((4 : ℝ) * (v 3 * v 4) + (-4 : ℝ) * (v 2 * v 4) + -(v 1 * v 3) + v 1 * v 2) * g6
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork130, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 3) + v 2 + -(v 0) = 0 := by
      nlinarith [hg0]
    have g2 : -(v 3) + v 2 + -(v 0) = 0 := by
      nlinarith [heq0]
    simp [-mul_eq_zero, cubicResidualNetwork130, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * ((v 3) ^ 2 * v 4 * h 1) + (-8 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (4 : ℝ) * ((v 2) ^ 2 * v 4 * h 1) + (8 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (-8 : ℝ) * (v 0 * v 2 * v 4 * h 1) + (4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 3 * v 4 * h 1)) * g0 +
      ((4 : ℝ) * (v 2 * v 4 * h 1) + (-4 : ℝ) * (v 0 * v 4 * h 1)) * g2
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork130, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 3) + v 2 + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : -(v 3) + v 2 = 0 := by
      nlinarith [hg1]
    have g2 : v 3 + -(v 2) + v 0 = 0 := by
      nlinarith [hg2]
    simp [-mul_eq_zero, cubicResidualNetwork130, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-16 : ℝ) * (v 3 * (v 4) ^ 2 * h 1) + (8 : ℝ) * ((v 3) ^ 2 * v 4 * h 1) + (-4 : ℝ) * ((v 3) ^ 2 * v 4 * h 0) + (16 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (-16 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (8 : ℝ) * ((v 2) ^ 2 * v 4 * h 1) + (-4 : ℝ) * ((v 2) ^ 2 * v 4 * h 0) + (8 : ℝ) * (v 1 * v 3 * v 4 * h 1) + -(v 1 * (v 3) ^ 2 * h 1) + v 1 * (v 3) ^ 2 * h 0 + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 2 * v 3 * h 1) + (-2 : ℝ) * (v 1 * v 2 * v 3 * h 0) + -(v 1 * (v 2) ^ 2 * h 1) + v 1 * (v 2) ^ 2 * h 0 + -((v 1) ^ 2 * v 3 * h 1) + (v 1) ^ 2 * v 2 * h 1 + (4 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (-4 : ℝ) * (v 0 * v 3 * v 4 * h 0) + (-4 : ℝ) * (v 0 * v 2 * v 4 * h 1) + (4 : ℝ) * (v 0 * v 2 * v 4 * h 0) + v 0 * v 1 * v 3 * h 0 + -(v 0 * v 1 * v 2 * h 0) = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 3 * v 4 * h 1)) * g0 +
      ((16 : ℝ) * ((v 4) ^ 2 * h 1) + (-4 : ℝ) * (v 3 * v 4 * h 1) + (4 : ℝ) * (v 2 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 4 * h 1) + v 1 * v 3 * h 1 + -(v 1 * v 3 * h 0) + -(v 1 * v 2 * h 1) + v 1 * v 2 * h 0 + (v 1) ^ 2 * h 1 + -(v 0 * v 1 * h 0)) * g1 +
      ((-4 : ℝ) * (v 3 * v 4 * h 0) + (-4 : ℝ) * (v 2 * v 4 * h 1) + (4 : ℝ) * (v 2 * v 4 * h 0)) * g2
    nlinarith [hcertificate]

theorem cubicResidualNetwork130_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork130.toNetwork := by
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
  simp [cubicResidualNetwork130, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork130_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork130.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork130_jacobianNonzero
    cubicResidualNetwork130_fourCharts

def cubicResidualNetwork131 : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .xx), (.xx, .zero), (.xy, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork131_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork131.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork131, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : v 4 + -(v 3) + -(v 1) = 0 := by
      nlinarith [heq1]
    have g2 : (-4 : ℝ) * (v 2 * v 4) + (4 : ℝ) * (v 2 * v 3) + -(v 1 * v 4) + (3 : ℝ) * (v 1 * v 3) + (4 : ℝ) * (v 1 * v 2) + v 0 * v 4 + -(v 0 * v 3) + -(v 0 * v 1) = 0 := by
      nlinarith [hdet]
    have g3 : (-12 : ℝ) * (v 2 * (v 4) ^ 3) + (-12 : ℝ) * (v 2 * v 3 * (v 4) ^ 2) + (12 : ℝ) * (v 2 * (v 3) ^ 2 * v 4) + (12 : ℝ) * (v 2 * (v 3) ^ 3) + (-32 : ℝ) * ((v 2) ^ 2 * (v 4) ^ 2) + (32 : ℝ) * ((v 2) ^ 2 * (v 3) ^ 2) + (32 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (-32 : ℝ) * (v 1 * v 2 * (v 3) ^ 2) + (64 : ℝ) * (v 1 * (v 2) ^ 2 * v 4) + (-64 : ℝ) * (v 1 * (v 2) ^ 2 * v 3) + (-16 : ℝ) * ((v 1) ^ 2 * v 2 * v 4) + (16 : ℝ) * ((v 1) ^ 2 * v 2 * v 3) + (2 : ℝ) * (v 0 * (v 4) ^ 3) + (2 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (-2 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (-2 : ℝ) * (v 0 * (v 3) ^ 3) + (16 : ℝ) * (v 0 * v 2 * (v 4) ^ 2) + (-16 : ℝ) * (v 0 * v 2 * (v 3) ^ 2) + (-4 : ℝ) * (v 0 * v 1 * (v 4) ^ 2) + (4 : ℝ) * (v 0 * v 1 * (v 3) ^ 2) + (-32 : ℝ) * (v 0 * v 1 * v 2 * v 4) + (32 : ℝ) * (v 0 * v 1 * v 2 * v 3) + (-2 : ℝ) * ((v 0) ^ 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 0) ^ 2 * (v 3) ^ 2) + (4 : ℝ) * ((v 0) ^ 2 * v 1 * v 4) + (-4 : ℝ) * ((v 0) ^ 2 * v 1 * v 3) = 0 := by
      nlinarith [hfold]
    have g4 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + -(v 3 * h 1) + -(v 3 * h 0) + (6 : ℝ) * (v 3 * (v 4) ^ 2) + (6 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + (-4 : ℝ) * (v 2 * h 0) + (4 : ℝ) * (v 2 * (v 4) ^ 2) + (8 : ℝ) * (v 2 * v 3 * v 4) + (4 : ℝ) * (v 2 * (v 3) ^ 2) + (2 : ℝ) * (v 1 * h 1) + (-4 : ℝ) * (v 1 * (v 4) ^ 2) + (-8 : ℝ) * (v 1 * v 3 * v 4) + (-4 : ℝ) * (v 1 * (v 3) ^ 2) + (-16 : ℝ) * ((v 1) ^ 2 * v 2) + v 0 * h 0 + (-2 : ℝ) * (v 0 * (v 4) ^ 2) + (-4 : ℝ) * (v 0 * v 3 * v 4) + (-2 : ℝ) * (v 0 * (v 3) ^ 2) + (4 : ℝ) * (v 0 * v 1 * v 4) + (4 : ℝ) * (v 0 * v 1 * v 3) = 0 := by
      nlinarith [hc0]
    have g5 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + -(v 3 * h 1) + -(v 3 * h 0) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + (2 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + (-8 : ℝ) * (v 2 * (v 4) ^ 2) + (8 : ℝ) * (v 2 * (v 3) ^ 2) + -(v 1 * h 1) + (4 : ℝ) * (v 1 * (v 4) ^ 2) + (-4 : ℝ) * (v 1 * (v 3) ^ 2) + (16 : ℝ) * (v 1 * v 2 * v 4) + (-16 : ℝ) * (v 1 * v 2 * v 3) + (2 : ℝ) * (v 0 * (v 4) ^ 2) + (-2 : ℝ) * (v 0 * (v 3) ^ 2) + (-4 : ℝ) * (v 0 * v 1 * v 4) + (4 : ℝ) * (v 0 * v 1 * v 3) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork131, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (4 : ℝ) * (v 2 * (v 3) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + (16 : ℝ) * ((v 2) ^ 2 * v 4 * h 0) + (-16 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + (8 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (-8 : ℝ) * (v 1 * v 2 * v 3 * h 1) + (8 : ℝ) * (v 1 * v 2 * v 3 * h 0) + v 0 * (v 4) ^ 2 * h 1 + -(v 0 * (v 4) ^ 2 * h 0) + -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 + (-8 : ℝ) * (v 0 * v 2 * v 4 * h 0) + (8 : ℝ) * (v 0 * v 2 * v 3 * h 0) + (-2 : ℝ) * (v 0 * v 1 * v 4 * h 1) + (2 : ℝ) * (v 0 * v 1 * v 3 * h 1) + (v 0) ^ 2 * v 4 * h 0 + -((v 0) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((-10 : ℝ) * (v 2 * v 4 * h 1) + (2 : ℝ) * (v 2 * v 4 * h 0) + (-10 : ℝ) * (v 2 * v 3 * h 1) + (2 : ℝ) * (v 2 * v 3 * h 0) + (-32 : ℝ) * ((v 2) ^ 2 * h 1) + (8 : ℝ) * ((v 2) ^ 2 * h 0) + (4 : ℝ) * (v 1 * v 2 * h 1) + (2 : ℝ) * (v 0 * v 4 * h 1) + (2 : ℝ) * (v 0 * v 3 * h 1) + (16 : ℝ) * (v 0 * v 2 * h 1) + (-2 : ℝ) * (v 0 * v 2 * h 0) + (-2 : ℝ) * ((v 0) ^ 2 * h 1)) * g1 +
      ((-8 : ℝ) * (v 2 * h 1) + (2 : ℝ) * (v 2 * h 0) + (2 : ℝ) * (v 0 * h 1)) * g2 +
      (-(v 4) + -(v 3)) * g3 +
      ((-4 : ℝ) * (v 2 * v 4) + (4 : ℝ) * (v 2 * v 3) + v 0 * v 4 + -(v 0 * v 3)) * g4 +
      ((2 : ℝ) * (v 2 * v 4) + (2 : ℝ) * (v 2 * v 3) + (-4 : ℝ) * (v 1 * v 2)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork131, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g3 : v 4 + -(v 3) + -(v 1) = 0 := by
      nlinarith [heq1]
    have g4 : (-4 : ℝ) * (v 2 * v 4) + (4 : ℝ) * (v 2 * v 3) + -(v 1 * v 4) + (3 : ℝ) * (v 1 * v 3) + (4 : ℝ) * (v 1 * v 2) + v 0 * v 4 + -(v 0 * v 3) + -(v 0 * v 1) = 0 := by
      nlinarith [hdet]
    simp [-mul_eq_zero, cubicResidualNetwork131, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 3 * v 4 * h 0) + (-3 : ℝ) * (v 1 * (v 3) ^ 2 * h 1) + (3 : ℝ) * (v 1 * (v 3) ^ 2 * h 0) + (-16 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (16 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (6 : ℝ) * ((v 1) ^ 2 * v 3 * h 1) + (8 : ℝ) * ((v 1) ^ 2 * v 2 * h 0) + v 0 * v 1 * v 4 * h 0 + (-3 : ℝ) * (v 0 * v 1 * v 3 * h 0) = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 3 * v 4 * h 1) + (-4 : ℝ) * (v 2 * v 4 * h 0) + (12 : ℝ) * (v 2 * v 3 * h 0) + (5 : ℝ) * (v 1 * v 4 * h 1) + -(v 1 * v 4 * h 0) + (3 : ℝ) * (v 1 * v 3 * h 1) + (3 : ℝ) * (v 1 * v 3 * h 0) + (-6 : ℝ) * ((v 1) ^ 2 * h 1) + (-2 : ℝ) * (v 0 * v 3 * h 0) + v 0 * v 1 * h 0) * g1 +
      ((4 : ℝ) * (v 3 * v 4 * h 1) + (8 : ℝ) * (v 2 * v 4 * h 0) + (-4 : ℝ) * (v 1 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 2 * h 0)) * g3 +
      ((2 : ℝ) * (v 3 * h 0)) * g4
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork131, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : -(v 4) + -(v 3) + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [hg1]
    have g3 : v 4 + -(v 3) + -(v 1) = 0 := by
      nlinarith [heq1]
    have g5 : (-12 : ℝ) * (v 2 * (v 4) ^ 3) + (36 : ℝ) * (v 2 * v 3 * (v 4) ^ 2) + (-36 : ℝ) * (v 2 * (v 3) ^ 2 * v 4) + (12 : ℝ) * (v 2 * (v 3) ^ 3) + (16 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (-32 : ℝ) * (v 1 * v 2 * v 3 * v 4) + (16 : ℝ) * (v 1 * v 2 * (v 3) ^ 2) + (-4 : ℝ) * ((v 1) ^ 2 * v 2 * v 4) + (4 : ℝ) * ((v 1) ^ 2 * v 2 * v 3) + (2 : ℝ) * (v 0 * (v 4) ^ 3) + (-6 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (6 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (-2 : ℝ) * (v 0 * (v 3) ^ 3) + (-2 : ℝ) * (v 0 * v 1 * (v 4) ^ 2) + (4 : ℝ) * (v 0 * v 1 * v 3 * v 4) + (-2 : ℝ) * (v 0 * v 1 * (v 3) ^ 2) = 0 := by
      nlinarith [hfold]
    have g7 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + -(v 3 * h 1) + -(v 3 * h 0) + (6 : ℝ) * (v 3 * (v 4) ^ 2) + (-6 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + -(v 1 * h 1) + (2 : ℝ) * (v 1 * (v 4) ^ 2) + (-4 : ℝ) * (v 1 * v 3 * v 4) + (2 : ℝ) * (v 1 * (v 3) ^ 2) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork131, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-8 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (16 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (4 : ℝ) * (v 2 * (v 3) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + (-4 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (4 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (4 : ℝ) * (v 1 * v 2 * v 3 * h 1) + (-4 : ℝ) * (v 1 * v 2 * v 3 * h 0) + -(v 0 * (v 4) ^ 2 * h 1) + v 0 * (v 4) ^ 2 * h 0 + (2 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (-2 : ℝ) * (v 0 * v 3 * v 4 * h 0) + -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 + v 0 * v 1 * v 4 * h 1 + -(v 0 * v 1 * v 3 * h 1) = 0 := by
      linear_combination
        ((2 : ℝ) * (v 0 * v 4 * h 1) + (-2 : ℝ) * (v 0 * v 3 * h 1) + (-2 : ℝ) * (v 0 * v 1 * h 1)) * g1 +
      ((10 : ℝ) * (v 2 * v 4 * h 1) + (-2 : ℝ) * (v 2 * v 4 * h 0) + (-10 : ℝ) * (v 2 * v 3 * h 1) + (2 : ℝ) * (v 2 * v 3 * h 0) + (-2 : ℝ) * (v 1 * v 2 * h 1) + (4 : ℝ) * (v 0 * v 3 * h 1) + (-4 : ℝ) * (v 0 * v 1 * h 1)) * g3 +
      (v 4 + -(v 3)) * g5 +
      ((-6 : ℝ) * (v 2 * v 4) + (6 : ℝ) * (v 2 * v 3) + (2 : ℝ) * (v 1 * v 2) + v 0 * v 4 + -(v 0 * v 3)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork131, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : -(v 4) + -(v 3) + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [hg1]
    have g2 : v 4 + -(v 3) = 0 := by
      nlinarith [hg2]
    have g4 : v 4 + -(v 3) + -(v 1) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork131, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (-4 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + (4 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 3 * v 4 * h 0) + (-3 : ℝ) * (v 1 * (v 3) ^ 2 * h 1) + (3 : ℝ) * (v 1 * (v 3) ^ 2 * h 0) + (8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (-8 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (v 1) ^ 2 * v 4 * h 1 + (-3 : ℝ) * ((v 1) ^ 2 * v 3 * h 1) + (-4 : ℝ) * ((v 1) ^ 2 * v 2 * h 0) = 0 := by
      linear_combination
        (((-1 : ℝ) / 2) * ((v 1) ^ 2 * h 1)) * g1 +
      ((-4 : ℝ) * (v 2 * v 4 * h 0) + (4 : ℝ) * (v 2 * v 3 * h 0) + -(v 1 * v 4 * h 1) + v 1 * v 4 * h 0 + (-3 : ℝ) * (v 1 * v 3 * h 0) + (4 : ℝ) * (v 1 * v 2 * h 0) + ((3 : ℝ) / 2) * ((v 1) ^ 2 * h 1)) * g2 +
      ((3 : ℝ) * (v 1 * v 3 * h 1) + (4 : ℝ) * (v 1 * v 2 * h 0) + -((v 1) ^ 2 * h 1)) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork131_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork131.toNetwork := by
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
  simp [cubicResidualNetwork131, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork131_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork131.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork131_jacobianNonzero
    cubicResidualNetwork131_fourCharts

def cubicResidualNetwork132 : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .xx), (.xx, .zero), (.xy, .x), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork132_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork132.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork132, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + (-2 : ℝ) * (v 2) + (2 : ℝ) * (v 1) + v 0 = 0 := by
      nlinarith [heq0]
    have g1 : v 4 + -(v 3) + -(v 1) = 0 := by
      nlinarith [heq1]
    have g2 : (-4 : ℝ) * (v 2 * v 4) + (4 : ℝ) * (v 2 * v 3) + -(v 1 * v 4) + (2 : ℝ) * (v 1 * v 3) + (4 : ℝ) * (v 1 * v 2) + v 0 * v 4 + -(v 0 * v 3) + -(v 0 * v 1) = 0 := by
      nlinarith [hdet]
    have g3 : (-12 : ℝ) * (v 2 * (v 4) ^ 3) + (12 : ℝ) * (v 2 * v 3 * (v 4) ^ 2) + (-32 : ℝ) * ((v 2) ^ 2 * (v 4) ^ 2) + (32 : ℝ) * ((v 2) ^ 2 * v 3 * v 4) + (32 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (-32 : ℝ) * (v 1 * v 2 * v 3 * v 4) + (64 : ℝ) * (v 1 * (v 2) ^ 2 * v 4) + (-64 : ℝ) * (v 1 * (v 2) ^ 2 * v 3) + (-16 : ℝ) * ((v 1) ^ 2 * v 2 * v 4) + (16 : ℝ) * ((v 1) ^ 2 * v 2 * v 3) + (2 : ℝ) * (v 0 * (v 4) ^ 3) + (-2 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (16 : ℝ) * (v 0 * v 2 * (v 4) ^ 2) + (-16 : ℝ) * (v 0 * v 2 * v 3 * v 4) + (-4 : ℝ) * (v 0 * v 1 * (v 4) ^ 2) + (4 : ℝ) * (v 0 * v 1 * v 3 * v 4) + (-32 : ℝ) * (v 0 * v 1 * v 2 * v 4) + (32 : ℝ) * (v 0 * v 1 * v 2 * v 3) + (-2 : ℝ) * ((v 0) ^ 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 0) ^ 2 * v 3 * v 4) + (4 : ℝ) * ((v 0) ^ 2 * v 1 * v 4) + (-4 : ℝ) * ((v 0) ^ 2 * v 1 * v 3) = 0 := by
      nlinarith [hfold]
    have g4 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (-4 : ℝ) * (v 2 * h 0) + (4 : ℝ) * (v 2 * (v 4) ^ 2) + (2 : ℝ) * (v 1 * h 1) + (-4 : ℝ) * (v 1 * (v 4) ^ 2) + (-16 : ℝ) * ((v 1) ^ 2 * v 2) + v 0 * h 0 + (-2 : ℝ) * (v 0 * (v 4) ^ 2) + (4 : ℝ) * (v 0 * v 1 * v 4) = 0 := by
      nlinarith [hc0]
    have g5 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + -(v 3 * h 1) + -(v 3 * h 0) + (2 : ℝ) * (v 3 * (v 4) ^ 2) + (-8 : ℝ) * (v 2 * (v 4) ^ 2) + (8 : ℝ) * (v 2 * v 3 * v 4) + -(v 1 * h 1) + (4 : ℝ) * (v 1 * (v 4) ^ 2) + (-4 : ℝ) * (v 1 * v 3 * v 4) + (16 : ℝ) * (v 1 * v 2 * v 4) + (-16 : ℝ) * (v 1 * v 2 * v 3) + (2 : ℝ) * (v 0 * (v 4) ^ 2) + (-2 : ℝ) * (v 0 * v 3 * v 4) + (-4 : ℝ) * (v 0 * v 1 * v 4) + (4 : ℝ) * (v 0 * v 1 * v 3) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork132, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (4 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (-8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (16 : ℝ) * ((v 2) ^ 2 * v 4 * h 0) + (-16 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + (8 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (-8 : ℝ) * (v 1 * v 2 * v 3 * h 1) + (8 : ℝ) * (v 1 * v 2 * v 3 * h 0) + v 0 * (v 4) ^ 2 * h 1 + -(v 0 * (v 4) ^ 2 * h 0) + -(v 0 * v 3 * v 4 * h 1) + v 0 * v 3 * v 4 * h 0 + (-8 : ℝ) * (v 0 * v 2 * v 4 * h 0) + (8 : ℝ) * (v 0 * v 2 * v 3 * h 0) + (-2 : ℝ) * (v 0 * v 1 * v 4 * h 1) + (2 : ℝ) * (v 0 * v 1 * v 3 * h 1) + (v 0) ^ 2 * v 4 * h 0 + -((v 0) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((2 : ℝ) * ((v 4) ^ 2 * h 1) + (-2 : ℝ) * ((v 3) ^ 2 * h 1) + (-6 : ℝ) * ((v 1) ^ 2 * h 1)) * g0 +
      ((2 : ℝ) * ((v 4) ^ 2 * h 1) + (2 : ℝ) * (v 3 * v 4 * h 1) + (-6 : ℝ) * (v 2 * v 4 * h 1) + (2 : ℝ) * (v 2 * v 4 * h 0) + (20 : ℝ) * (v 2 * v 3 * h 1) + (8 : ℝ) * ((v 2) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 4 * h 1) + (4 : ℝ) * (v 1 * v 3 * h 1) + (-12 : ℝ) * ((v 1) ^ 2 * h 1) + (-6 : ℝ) * (v 0 * v 3 * h 1) + (-8 : ℝ) * (v 0 * v 2 * h 1) + (-2 : ℝ) * (v 0 * v 2 * h 0) + (-2 : ℝ) * (v 0 * v 1 * h 1) + (2 : ℝ) * ((v 0) ^ 2 * h 1)) * g1 +
      ((4 : ℝ) * (v 3 * h 1) + (2 : ℝ) * (v 2 * h 0) + (-4 : ℝ) * (v 1 * h 1) + (-2 : ℝ) * (v 0 * h 1)) * g2 +
      (-(v 4)) * g3 +
      ((-4 : ℝ) * (v 2 * v 4) + (4 : ℝ) * (v 2 * v 3) + v 0 * v 4 + -(v 0 * v 3)) * g4 +
      ((2 : ℝ) * (v 2 * v 4) + (-4 : ℝ) * (v 1 * v 2)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork132, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + (-4 : ℝ) * (v 2) + v 0 = 0 := by
      nlinarith [hg0]
    have g1 : v 4 + -(v 3) = 0 := by
      nlinarith [hg1]
    have g3 : v 4 + -(v 3) + -(v 1) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork132, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 2 * v 3 * v 4 * h 0) + v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 3 * v 4 * h 0) + (-16 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (16 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (4 : ℝ) * ((v 1) ^ 2 * v 3 * h 1) + (8 : ℝ) * ((v 1) ^ 2 * v 2 * h 0) + v 0 * v 1 * v 4 * h 0 + (-2 : ℝ) * (v 0 * v 1 * v 3 * h 0) = 0 := by
      linear_combination
        (-(v 1 * v 3 * h 0)) * g0 +
      (-((v 3) ^ 2 * h 1) + (3 : ℝ) * (v 1 * v 4 * h 1) + -(v 1 * v 4 * h 0) + -(v 1 * v 3 * h 1) + (-4 : ℝ) * (v 1 * v 2 * h 0) + (-4 : ℝ) * ((v 1) ^ 2 * h 1) + v 0 * v 1 * h 0) * g1 +
      ((v 3) ^ 2 * h 1 + (4 : ℝ) * (v 2 * v 4 * h 0) + (-2 : ℝ) * (v 1 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 2 * h 0)) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork132, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + (-4 : ℝ) * (v 2) + v 0 = 0 := by
      nlinarith [hg0]
    have g1 : -(v 4) + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [hg1]
    have g2 : -(v 4) + (-2 : ℝ) * (v 2) + (2 : ℝ) * (v 1) + v 0 = 0 := by
      nlinarith [heq0]
    have g3 : v 4 + -(v 3) + -(v 1) = 0 := by
      nlinarith [heq1]
    have g4 : (-4 : ℝ) * (v 2 * v 4) + (4 : ℝ) * (v 2 * v 3) + -(v 1 * v 4) + (2 : ℝ) * (v 1 * v 3) + (4 : ℝ) * (v 1 * v 2) + v 0 * v 4 + -(v 0 * v 3) + -(v 0 * v 1) = 0 := by
      nlinarith [hdet]
    have g5 : (-12 : ℝ) * (v 2 * (v 4) ^ 3) + (36 : ℝ) * (v 2 * v 3 * (v 4) ^ 2) + (-36 : ℝ) * (v 2 * (v 3) ^ 2 * v 4) + (12 : ℝ) * (v 2 * (v 3) ^ 3) + (16 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (-32 : ℝ) * (v 1 * v 2 * v 3 * v 4) + (16 : ℝ) * (v 1 * v 2 * (v 3) ^ 2) + (-4 : ℝ) * ((v 1) ^ 2 * v 2 * v 4) + (4 : ℝ) * ((v 1) ^ 2 * v 2 * v 3) + (2 : ℝ) * (v 0 * (v 4) ^ 3) + (-6 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (6 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (-2 : ℝ) * (v 0 * (v 3) ^ 3) + (-2 : ℝ) * (v 0 * v 1 * (v 4) ^ 2) + (4 : ℝ) * (v 0 * v 1 * v 3 * v 4) + (-2 : ℝ) * (v 0 * v 1 * (v 3) ^ 2) = 0 := by
      nlinarith [hfold]
    have g6 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (-4 : ℝ) * (v 3 * (v 4) ^ 2) + (2 : ℝ) * ((v 3) ^ 2 * v 4) + (-4 : ℝ) * (v 2 * h 0) + (-4 : ℝ) * (v 2 * (v 4) ^ 2) + (8 : ℝ) * (v 2 * v 3 * v 4) + (-4 : ℝ) * (v 2 * (v 3) ^ 2) + (2 : ℝ) * (v 1 * h 1) + (-2 : ℝ) * (v 1 * (v 4) ^ 2) + (2 : ℝ) * (v 1 * v 3 * v 4) + (8 : ℝ) * (v 1 * v 2 * v 4) + (-8 : ℝ) * (v 1 * v 2 * v 3) + (-4 : ℝ) * ((v 1) ^ 2 * v 2) + v 0 * h 0 = 0 := by
      nlinarith [hc0]
    have g7 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + -(v 3 * h 1) + -(v 3 * h 0) + (6 : ℝ) * (v 3 * (v 4) ^ 2) + (-6 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + -(v 1 * h 1) + (2 : ℝ) * (v 1 * (v 4) ^ 2) + (-4 : ℝ) * (v 1 * v 3 * v 4) + (2 : ℝ) * (v 1 * (v 3) ^ 2) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork132, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-8 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (16 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (4 : ℝ) * (v 2 * (v 3) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + (-4 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (4 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (4 : ℝ) * (v 1 * v 2 * v 3 * h 1) + (-4 : ℝ) * (v 1 * v 2 * v 3 * h 0) + -(v 0 * (v 4) ^ 2 * h 1) + v 0 * (v 4) ^ 2 * h 0 + (2 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (-2 : ℝ) * (v 0 * v 3 * v 4 * h 0) + -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 + v 0 * v 1 * v 4 * h 1 + -(v 0 * v 1 * v 3 * h 1) = 0 := by
      linear_combination
        (-((v 3) ^ 2 * h 1) + (v 1) ^ 2 * h 1 + -(v 0 * v 3 * h 0)) * g0 +
      (((-3 : ℝ) / 2) * ((v 4) ^ 2 * h 1) + ((3 : ℝ) / 2) * (v 3 * v 4 * h 1) + (v 3) ^ 2 * h 1 + (4 : ℝ) * ((v 3) ^ 2 * h 0) + (-5 : ℝ) * (v 2 * v 4 * h 1) + (2 : ℝ) * (v 2 * v 4 * h 0) + (9 : ℝ) * (v 2 * v 3 * h 1) + (-2 : ℝ) * (v 2 * v 3 * h 0) + (-16 : ℝ) * ((v 2) ^ 2 * h 0) + ((1 : ℝ) / 2) * (v 1 * v 4 * h 1) + ((5 : ℝ) / 2) * (v 1 * v 3 * h 1) + (5 : ℝ) * (v 1 * v 2 * h 1) + (16 : ℝ) * (v 1 * v 2 * h 0) + ((1 : ℝ) / 2) * (v 0 * v 4 * h 1) + v 0 * v 4 * h 0 + ((-3 : ℝ) / 2) * (v 0 * v 3 * h 1) + (-6 : ℝ) * (v 0 * v 3 * h 0) + (8 : ℝ) * (v 0 * v 2 * h 0) + ((-1 : ℝ) / 2) * (v 0 * v 1 * h 1) + (-2 : ℝ) * (v 0 * v 1 * h 0) + (v 0) ^ 2 * h 0) * g1 +
      ((-4 : ℝ) * ((v 3) ^ 2 * h 0) + (8 : ℝ) * (v 2 * v 3 * h 0) + (-16 : ℝ) * (v 1 * v 2 * h 0) + (2 : ℝ) * (v 0 * v 3 * h 0)) * g2 +
      (((-3 : ℝ) / 2) * ((v 4) ^ 2 * h 1) + (3 : ℝ) * (v 2 * v 4 * h 1) + (6 : ℝ) * (v 2 * v 4 * h 0) + (10 : ℝ) * (v 2 * v 3 * h 0) + (5 : ℝ) * (v 1 * v 3 * h 1) + ((-1 : ℝ) / 2) * (v 0 * v 4 * h 1) + ((-1 : ℝ) / 2) * (v 0 * v 3 * h 1) + (-4 : ℝ) * (v 0 * v 3 * h 0) + (-4 : ℝ) * (v 0 * v 1 * h 0) + (2 : ℝ) * ((v 0) ^ 2 * h 0)) * g3 +
      ((-4 : ℝ) * (v 2 * (v 4) ^ 2) + (8 : ℝ) * (v 2 * v 3 * v 4) + (-4 : ℝ) * (v 2 * (v 3) ^ 2) + (4 : ℝ) * (v 1 * v 2 * v 4) + (-4 : ℝ) * (v 1 * v 2 * v 3)) * g4 +
      (((1 : ℝ) / 2) * (v 3)) * g5 +
      ((2 : ℝ) * ((v 4) ^ 2) + ((-7 : ℝ) / 2) * (v 3 * v 4) + ((3 : ℝ) / 2) * ((v 3) ^ 2) + (4 : ℝ) * (v 2 * v 4) + (-4 : ℝ) * (v 2 * v 3) + -(v 0 * v 4) + v 0 * v 3) * g6 +
      ((2 : ℝ) * ((v 4) ^ 2) + ((-3 : ℝ) / 2) * (v 3 * v 4) + (6 : ℝ) * (v 1 * v 2) + -(v 0 * v 4) + ((1 : ℝ) / 2) * (v 0 * v 3)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork132, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : -(v 4) + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [hg1]
    have g2 : v 4 + -(v 3) = 0 := by
      nlinarith [hg2]
    have g4 : v 4 + -(v 3) + -(v 1) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork132, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (-4 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + (3 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (-3 : ℝ) * (v 1 * v 3 * v 4 * h 0) + (-2 : ℝ) * (v 1 * (v 3) ^ 2 * h 1) + (2 : ℝ) * (v 1 * (v 3) ^ 2 * h 0) + (8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (-8 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (v 1) ^ 2 * v 4 * h 1 + (-2 : ℝ) * ((v 1) ^ 2 * v 3 * h 1) + (-4 : ℝ) * ((v 1) ^ 2 * v 2 * h 0) = 0 := by
      linear_combination
        ((4 : ℝ) * (v 2 * v 4 * h 0) + (-4 : ℝ) * (v 2 * v 3 * h 0) + (-2 : ℝ) * (v 1 * v 2 * h 0)) * g1 +
      ((-2 : ℝ) * (v 2 * v 4 * h 0) + (4 : ℝ) * (v 2 * v 3 * h 0) + v 1 * v 4 * h 0 + (-2 : ℝ) * (v 1 * v 3 * h 0)) * g2 +
      ((2 : ℝ) * (v 2 * v 4 * h 0) + -(v 1 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 3 * h 1)) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork132_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork132.toNetwork := by
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
  simp [cubicResidualNetwork132, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork132_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork132.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork132_jacobianNonzero
    cubicResidualNetwork132_fourCharts

def cubicResidualNetwork133 : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .xx), (.xx, .zero), (.xy, .y), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork133_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork133.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork133, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : v 4 + -(v 1) = 0 := by
      nlinarith [heq1]
    have g2 : (-4 : ℝ) * (v 2 * v 4) + -(v 1 * v 4) + v 1 * v 3 + (4 : ℝ) * (v 1 * v 2) + v 0 * v 4 + -(v 0 * v 1) = 0 := by
      nlinarith [hdet]
    have g3 : (-12 : ℝ) * (v 2 * (v 4) ^ 3) + (-24 : ℝ) * (v 2 * v 3 * (v 4) ^ 2) + (-12 : ℝ) * (v 2 * (v 3) ^ 2 * v 4) + (-32 : ℝ) * ((v 2) ^ 2 * (v 4) ^ 2) + (-32 : ℝ) * ((v 2) ^ 2 * v 3 * v 4) + (32 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (32 : ℝ) * (v 1 * v 2 * v 3 * v 4) + (64 : ℝ) * (v 1 * (v 2) ^ 2 * v 4) + (-16 : ℝ) * ((v 1) ^ 2 * v 2 * v 4) + (2 : ℝ) * (v 0 * (v 4) ^ 3) + (4 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (16 : ℝ) * (v 0 * v 2 * (v 4) ^ 2) + (16 : ℝ) * (v 0 * v 2 * v 3 * v 4) + (-4 : ℝ) * (v 0 * v 1 * (v 4) ^ 2) + (-4 : ℝ) * (v 0 * v 1 * v 3 * v 4) + (-32 : ℝ) * (v 0 * v 1 * v 2 * v 4) + (-2 : ℝ) * ((v 0) ^ 2 * (v 4) ^ 2) + (-2 : ℝ) * ((v 0) ^ 2 * v 3 * v 4) + (4 : ℝ) * ((v 0) ^ 2 * v 1 * v 4) = 0 := by
      nlinarith [hfold]
    have g4 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + -(v 3 * h 1) + -(v 3 * h 0) + (6 : ℝ) * (v 3 * (v 4) ^ 2) + (6 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + (-4 : ℝ) * (v 2 * h 0) + (4 : ℝ) * (v 2 * (v 4) ^ 2) + (8 : ℝ) * (v 2 * v 3 * v 4) + (4 : ℝ) * (v 2 * (v 3) ^ 2) + (2 : ℝ) * (v 1 * h 1) + (-4 : ℝ) * (v 1 * (v 4) ^ 2) + (-8 : ℝ) * (v 1 * v 3 * v 4) + (-4 : ℝ) * (v 1 * (v 3) ^ 2) + (-16 : ℝ) * ((v 1) ^ 2 * v 2) + v 0 * h 0 + (-2 : ℝ) * (v 0 * (v 4) ^ 2) + (-4 : ℝ) * (v 0 * v 3 * v 4) + (-2 : ℝ) * (v 0 * (v 3) ^ 2) + (4 : ℝ) * (v 0 * v 1 * v 4) + (4 : ℝ) * (v 0 * v 1 * v 3) = 0 := by
      nlinarith [hc0]
    have g5 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + (-4 : ℝ) * (v 3 * (v 4) ^ 2) + (-2 : ℝ) * ((v 3) ^ 2 * v 4) + (-8 : ℝ) * (v 2 * (v 4) ^ 2) + (-8 : ℝ) * (v 2 * v 3 * v 4) + -(v 1 * h 1) + (4 : ℝ) * (v 1 * (v 4) ^ 2) + (4 : ℝ) * (v 1 * v 3 * v 4) + (16 : ℝ) * (v 1 * v 2 * v 4) + (2 : ℝ) * (v 0 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * v 3 * v 4) + (-4 : ℝ) * (v 0 * v 1 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork133, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (16 : ℝ) * ((v 2) ^ 2 * v 4 * h 0) + (8 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + v 0 * (v 4) ^ 2 * h 1 + -(v 0 * (v 4) ^ 2 * h 0) + v 0 * v 3 * v 4 * h 1 + -(v 0 * v 3 * v 4 * h 0) + (-8 : ℝ) * (v 0 * v 2 * v 4 * h 0) + (-2 : ℝ) * (v 0 * v 1 * v 4 * h 1) + (v 0) ^ 2 * v 4 * h 0 = 0 := by
      linear_combination
        ((-6 : ℝ) * (v 2 * v 4 * h 1) + (2 : ℝ) * (v 2 * v 4 * h 0) + (-10 : ℝ) * (v 2 * v 3 * h 1) + (2 : ℝ) * (v 2 * v 3 * h 0) + (-32 : ℝ) * ((v 2) ^ 2 * h 1) + (8 : ℝ) * ((v 2) ^ 2 * h 0) + v 1 * v 4 * h 1 + -(v 1 * v 3 * h 1) + v 0 * v 4 * h 1 + (2 : ℝ) * (v 0 * v 3 * h 1) + (16 : ℝ) * (v 0 * v 2 * h 1) + (-2 : ℝ) * (v 0 * v 2 * h 0) + v 0 * v 1 * h 1 + (-2 : ℝ) * ((v 0) ^ 2 * h 1)) * g1 +
      (-(v 4 * h 0) + (-8 : ℝ) * (v 2 * h 1) + (2 : ℝ) * (v 2 * h 0) + (2 : ℝ) * (v 0 * h 1) + (2 : ℝ) * ((v 4) ^ 3) + (4 : ℝ) * (v 3 * (v 4) ^ 2) + (2 : ℝ) * ((v 3) ^ 2 * v 4) + (8 : ℝ) * (v 2 * (v 4) ^ 2) + (8 : ℝ) * (v 2 * v 3 * v 4) + (-4 : ℝ) * (v 1 * (v 4) ^ 2) + (-4 : ℝ) * (v 1 * v 3 * v 4) + (-16 : ℝ) * (v 1 * v 2 * v 4) + (-2 : ℝ) * (v 0 * (v 4) ^ 2) + (-2 : ℝ) * (v 0 * v 3 * v 4) + (4 : ℝ) * (v 0 * v 1 * v 4)) * g2 +
      (-(v 4) + -(v 3)) * g3 +
      ((-4 : ℝ) * (v 2 * v 4) + v 0 * v 4) * g4 +
      ((-2 : ℝ) * (v 2 * v 4) + (2 : ℝ) * (v 2 * v 3) + -(v 1 * v 4) + v 1 * v 3 + v 0 * v 4 + -(v 0 * v 1)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork133, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : v 4 = 0 := by
      nlinarith [hg1]
    have g3 : v 4 + -(v 1) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork133, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (4 : ℝ) * (v 2 * v 3 * v 4 * h 0) + v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + -(v 1 * (v 3) ^ 2 * h 1) + v 1 * (v 3) ^ 2 * h 0 + (-16 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (2 : ℝ) * ((v 1) ^ 2 * v 3 * h 1) + (8 : ℝ) * ((v 1) ^ 2 * v 2 * h 0) + v 0 * v 1 * v 4 * h 0 + -(v 0 * v 1 * v 3 * h 0) = 0 := by
      linear_combination
        (-((v 3) ^ 2 * h 1) + (v 3) ^ 2 * h 0 + (4 : ℝ) * (v 2 * v 4 * h 0) + (4 : ℝ) * (v 2 * v 3 * h 0) + v 1 * v 4 * h 1 + -(v 1 * v 4 * h 0) + (2 : ℝ) * (v 1 * v 3 * h 1) + (-8 : ℝ) * (v 1 * v 2 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * h 1) + -(v 0 * v 3 * h 0) + v 0 * v 1 * h 0) * g1 +
      ((v 3) ^ 2 * h 1 + -((v 3) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 3 * h 1) + (-8 : ℝ) * (v 1 * v 2 * h 0) + v 0 * v 3 * h 0) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork133, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g3 : v 4 + -(v 1) = 0 := by
      nlinarith [heq1]
    have g5 : (-12 : ℝ) * (v 2 * (v 4) ^ 3) + (16 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (-4 : ℝ) * ((v 1) ^ 2 * v 2 * v 4) + (2 : ℝ) * (v 0 * (v 4) ^ 3) + (-2 : ℝ) * (v 0 * v 1 * (v 4) ^ 2) = 0 := by
      nlinarith [hfold]
    have g7 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + -(v 1 * h 1) + (2 : ℝ) * (v 1 * (v 4) ^ 2) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork133, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (4 : ℝ) * (v 1 * v 2 * v 4 * h 0) + -(v 0 * (v 4) ^ 2 * h 1) + v 0 * (v 4) ^ 2 * h 0 + v 0 * v 1 * v 4 * h 1 = 0 := by
      linear_combination
        ((10 : ℝ) * (v 2 * v 4 * h 1) + (-2 : ℝ) * (v 2 * v 4 * h 0) + (-2 : ℝ) * (v 1 * v 2 * h 1) + (-2 : ℝ) * (v 0 * v 4 * h 1)) * g3 +
      (v 4) * g5 +
      ((-6 : ℝ) * (v 2 * v 4) + (2 : ℝ) * (v 1 * v 2) + v 0 * v 4) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork133, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g2 : v 4 = 0 := by
      nlinarith [hg2]
    have g4 : v 4 + -(v 1) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork133, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + v 1 * v 3 * v 4 * h 1 + -(v 1 * v 3 * v 4 * h 0) + (8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (v 1) ^ 2 * v 4 * h 1 + -((v 1) ^ 2 * v 3 * h 1) + (-4 : ℝ) * ((v 1) ^ 2 * v 2 * h 0) = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 2 * v 4 * h 0) + -(v 1 * v 4 * h 1) + v 1 * v 4 * h 0 + -(v 1 * v 3 * h 0) + (4 : ℝ) * (v 1 * v 2 * h 0) + (v 1) ^ 2 * h 1) * g2 +
      (v 1 * v 3 * h 1 + (4 : ℝ) * (v 1 * v 2 * h 0)) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork133_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork133.toNetwork := by
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
  simp [cubicResidualNetwork133, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork133_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork133.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork133_jacobianNonzero
    cubicResidualNetwork133_fourCharts

def cubicResidualNetwork134 : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .xy), (.xx, .zero), (.xy, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork134_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork134.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork134, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork134, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (4 : ℝ) * (v 2 * (v 3) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + (16 : ℝ) * ((v 2) ^ 2 * v 4 * h 0) + (-16 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + (4 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (-4 : ℝ) * (v 1 * v 2 * v 3 * h 1) + (4 : ℝ) * (v 1 * v 2 * v 3 * h 0) + v 0 * (v 4) ^ 2 * h 1 + -(v 0 * (v 4) ^ 2 * h 0) + -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 + (-8 : ℝ) * (v 0 * v 2 * v 4 * h 0) + (8 : ℝ) * (v 0 * v 2 * v 3 * h 0) + -(v 0 * v 1 * v 4 * h 1) + v 0 * v 1 * v 3 * h 1 + (v 0) ^ 2 * v 4 * h 0 + -((v 0) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 2 * v 4 * h 1) + (8 : ℝ) * (v 2 * v 4 * h 0) + (-4 : ℝ) * (v 2 * v 3 * h 1) + (8 : ℝ) * (v 2 * v 3 * h 0) + (16 : ℝ) * ((v 2) ^ 2 * h 0) + (4 : ℝ) * (v 1 * v 2 * h 1) + (-4 : ℝ) * (v 1 * v 2 * h 0) + v 0 * v 4 * h 1 + -(v 0 * v 4 * h 0) + v 0 * v 3 * h 1 + -(v 0 * v 3 * h 0) + (-8 : ℝ) * (v 0 * v 2 * h 0) + -(v 0 * v 1 * h 1) + (v 0) ^ 2 * h 0) * g1
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork134, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork134, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + -(v 1 * (v 3) ^ 2 * h 1) + v 1 * (v 3) ^ 2 * h 0 + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (8 : ℝ) * (v 1 * v 2 * v 3 * h 0) + -((v 1) ^ 2 * v 4 * h 1) + (v 1) ^ 2 * v 3 * h 1 + v 0 * v 1 * v 4 * h 0 + -(v 0 * v 1 * v 3 * h 0) = 0 := by
      linear_combination
        ((4 : ℝ) * (v 2 * v 4 * h 0) + (4 : ℝ) * (v 2 * v 3 * h 0) + -(v 1 * v 4 * h 0) + v 1 * v 3 * h 1 + -(v 1 * v 3 * h 0) + -((v 1) ^ 2 * h 1) + v 0 * v 1 * h 0) * g1 +
      (v 1 * v 4 * h 1 + (-8 : ℝ) * (v 1 * v 2 * h 0)) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork134, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork134, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-8 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (16 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (4 : ℝ) * (v 2 * (v 3) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + -(v 0 * (v 4) ^ 2 * h 1) + v 0 * (v 4) ^ 2 * h 0 + (2 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (-2 : ℝ) * (v 0 * v 3 * v 4 * h 0) + -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 = 0 := by
      linear_combination
        ((4 : ℝ) * (v 2 * v 4 * h 1) + (-8 : ℝ) * (v 2 * v 4 * h 0) + (-4 : ℝ) * (v 2 * v 3 * h 1) + (8 : ℝ) * (v 2 * v 3 * h 0) + -(v 0 * v 4 * h 1) + v 0 * v 4 * h 0 + v 0 * v 3 * h 1 + -(v 0 * v 3 * h 0)) * g3
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork134, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork134, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
        (v 1 * v 4 * h 0) * g2 +
      ((-4 : ℝ) * (v 2 * v 4 * h 0) + (4 : ℝ) * (v 2 * v 3 * h 0) + -(v 1 * v 4 * h 1) + v 1 * v 3 * h 1 + -(v 1 * v 3 * h 0)) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork134_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork134.toNetwork := by
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
  simp [cubicResidualNetwork134, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork134_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork134.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork134_jacobianNonzero
    cubicResidualNetwork134_fourCharts

def cubicResidualNetwork135 : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .xy), (.xx, .zero), (.xy, .x), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork135_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork135.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork135, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork135, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (4 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (-8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (16 : ℝ) * ((v 2) ^ 2 * v 4 * h 0) + (-16 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + (4 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (-4 : ℝ) * (v 1 * v 2 * v 3 * h 1) + (4 : ℝ) * (v 1 * v 2 * v 3 * h 0) + v 0 * (v 4) ^ 2 * h 1 + -(v 0 * (v 4) ^ 2 * h 0) + -(v 0 * v 3 * v 4 * h 1) + v 0 * v 3 * v 4 * h 0 + (-8 : ℝ) * (v 0 * v 2 * v 4 * h 0) + (8 : ℝ) * (v 0 * v 2 * v 3 * h 0) + -(v 0 * v 1 * v 4 * h 1) + v 0 * v 1 * v 3 * h 1 + (v 0) ^ 2 * v 4 * h 0 + -((v 0) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 2 * v 4 * h 1) + (8 : ℝ) * (v 2 * v 4 * h 0) + (16 : ℝ) * ((v 2) ^ 2 * h 0) + (4 : ℝ) * (v 1 * v 2 * h 1) + (-4 : ℝ) * (v 1 * v 2 * h 0) + v 0 * v 4 * h 1 + -(v 0 * v 4 * h 0) + (-8 : ℝ) * (v 0 * v 2 * h 0) + -(v 0 * v 1 * h 1) + (v 0) ^ 2 * h 0) * g1
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork135, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork135, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 2 * v 3 * v 4 * h 0) + v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + -(v 1 * v 3 * v 4 * h 1) + v 1 * v 3 * v 4 * h 0 + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (8 : ℝ) * (v 1 * v 2 * v 3 * h 0) + -((v 1) ^ 2 * v 4 * h 1) + (v 1) ^ 2 * v 3 * h 1 + v 0 * v 1 * v 4 * h 0 + -(v 0 * v 1 * v 3 * h 0) = 0 := by
      linear_combination
        ((4 : ℝ) * (v 2 * v 4 * h 0) + v 1 * v 4 * h 1 + -(v 1 * v 4 * h 0)) * g1 +
      ((-8 : ℝ) * (v 1 * v 2 * h 0) + -((v 1) ^ 2 * h 1) + v 0 * v 1 * h 0) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork135, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork135, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-8 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (16 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (4 : ℝ) * (v 2 * (v 3) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + -(v 0 * (v 4) ^ 2 * h 1) + v 0 * (v 4) ^ 2 * h 0 + (2 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (-2 : ℝ) * (v 0 * v 3 * v 4 * h 0) + -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 = 0 := by
      linear_combination
        ((8 : ℝ) * (v 2 * v 4 * h 0) + (-8 : ℝ) * (v 2 * v 3 * h 0) + -(v 0 * v 4 * h 0) + v 0 * v 3 * h 0) * g1 +
      ((4 : ℝ) * (v 2 * v 4 * h 1) + (-4 : ℝ) * (v 2 * v 3 * h 1) + (8 : ℝ) * (v 2 * v 3 * h 0) + (-8 : ℝ) * (v 1 * v 2 * h 0) + -(v 0 * v 4 * h 1) + v 0 * v 3 * h 1 + -(v 0 * v 3 * h 0) + v 0 * v 1 * h 0) * g3
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork135, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork135, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
        (-((v 4) ^ 2 * h 0) + v 3 * v 4 * h 1 + -((v 3) ^ 2 * h 1) + (v 3) ^ 2 * h 0 + (-2 : ℝ) * (v 1 * v 4 * h 0) + (2 : ℝ) * (v 1 * v 3 * h 0)) * g1 +
      (-((v 4) ^ 2 * h 0) + v 3 * v 4 * h 1 + -(v 3 * v 4 * h 0) + -(v 1 * v 4 * h 1) + (2 : ℝ) * ((v 1) ^ 2 * h 0)) * g2 +
      ((-4 : ℝ) * (v 2 * v 4 * h 0) + (4 : ℝ) * (v 2 * v 3 * h 0)) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork135_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork135.toNetwork := by
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
  simp [cubicResidualNetwork135, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork135_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork135.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork135_jacobianNonzero
    cubicResidualNetwork135_fourCharts

end SmallCusp

import proofs.SmallCusp.Obstruction.CubicDegeneracy
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

def cubicResidualNetwork16 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.y, .yy), (.xy, .x)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork16_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork16.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork16, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g4 : -(v 1 * h 0) = 0 := by
      nlinarith [hc0]
    simp [-mul_eq_zero, cubicResidualNetwork16, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -((v 1) ^ 2 * v 4 * h 0) = 0 := by
      linear_combination
        (v 1 * v 4) * g4
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork16, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork16, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork16, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g4 : v 1 * v 4 + -(v 1 * v 3) + v 1 * v 2 = 0 := by
      nlinarith [hdet]
    have g6 : -(v 1 * h 0) = 0 := by
      nlinarith [hc0]
    simp [-mul_eq_zero, cubicResidualNetwork16, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + -(v 1 * v 3 * v 4 * h 1) + v 1 * v 2 * v 4 * h 1 = 0 := by
      linear_combination
        (v 4 * h 1) * g4 +
      ((v 4) ^ 2) * g6
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork16, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork16, CodedBimolNetwork.toNetwork,
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

theorem cubicResidualNetwork16_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork16.toNetwork := by
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
  simp [cubicResidualNetwork16, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork16_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork16.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork16_jacobianNonzero
    cubicResidualNetwork16_fourCharts

def cubicResidualNetwork17 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.y, .yy), (.xy, .y)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork17_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork17.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork17, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork17, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork17, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g4 : -(v 3 * v 4) + v 2 * v 4 + -(v 1 * v 3) + v 1 * v 2 = 0 := by
      nlinarith [hdet]
    have g7 : v 3 * h 1 + -(v 2 * h 1) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork17, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 3 * (v 4) ^ 2 * h 1 + -(v 3 * (v 4) ^ 2 * h 0) + -(v 2 * (v 4) ^ 2 * h 1) + v 2 * (v 4) ^ 2 * h 0 + -(v 1 * v 3 * v 4 * h 0) + v 1 * v 2 * v 4 * h 0 = 0 := by
      linear_combination
        (v 4 * h 0) * g4 +
      ((v 4) ^ 2) * g7
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork17, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork17, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork17, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g5 : -(v 3 * v 4) + v 2 * v 4 + -(v 1 * v 3) + v 1 * v 2 = 0 := by
      nlinarith [hdet]
    have g7 : -(v 4 * h 1) + -(v 4 * h 0) + -(v 1 * h 0) = 0 := by
      nlinarith [hc0]
    have g8 : v 3 * h 1 + -(v 2 * h 1) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork17, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -((v 3) ^ 2 * v 4 * h 1) + (2 : ℝ) * (v 2 * v 3 * v 4 * h 1) + -((v 2) ^ 2 * v 4 * h 1) = 0 := by
      linear_combination
        (v 3 * h 0 + v 2 * h 0) * g5 +
      (-((v 3) ^ 2) + (v 2) ^ 2) * g7 +
      ((-2 : ℝ) * (v 3 * v 4)) * g8
    nlinarith [hcertificate]

theorem cubicResidualNetwork17_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork17.toNetwork := by
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
  simp [cubicResidualNetwork17, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork17_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork17.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork17_jacobianNonzero
    cubicResidualNetwork17_fourCharts

def cubicResidualNetwork18 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.y, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork18_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork18.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork18, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : -(v 4) + v 3 + -(v 2) = 0 := by
      nlinarith [heq1]
    have g2 : -(v 3 * v 4) + (2 : ℝ) * (v 2 * v 4) + v 1 * v 4 + -(v 1 * v 3) + v 1 * v 2 = 0 := by
      nlinarith [hdet]
    have g3 : (2 : ℝ) * (v 1 * (v 4) ^ 3) + (-2 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 1) ^ 2 * (v 4) ^ 2) + (-2 : ℝ) * ((v 1) ^ 2 * v 2 * v 4) = 0 := by
      nlinarith [hfold]
    have g4 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + v 2 * h 1 + (-2 : ℝ) * (v 2 * (v 4) ^ 2) + -(v 1 * h 0) + (2 : ℝ) * (v 1 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * v 2 * v 4) = 0 := by
      nlinarith [hc0]
    simp [-mul_eq_zero, cubicResidualNetwork18, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
        (-(v 1 * v 4 * h 1) + v 1 * v 4 * h 0 + -(v 1 * v 2 * h 1) + (-2 : ℝ) * ((v 1) ^ 2 * h 1) + (v 1) ^ 2 * h 0) * g1 +
      ((-2 : ℝ) * (v 1 * h 1)) * g2 +
      (-(v 3) + v 2) * g3 +
      (v 1 * v 3 + -(v 1 * v 2)) * g4
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork18, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork18, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 3 * (v 4) ^ 2 * h 1 + -(v 3 * (v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (2 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + -(v 2 * v 3 * v 4 * h 1) + (2 : ℝ) * ((v 2) ^ 2 * v 4 * h 1) + -(v 1 * v 3 * v 4 * h 0) + (2 : ℝ) * (v 1 * v 2 * v 4 * h 0) = 0 := by
      linear_combination
        (-(v 3 * v 4 * h 1) + v 3 * v 4 * h 0 + (2 : ℝ) * (v 2 * v 4 * h 1) + (-2 : ℝ) * (v 2 * v 4 * h 0) + v 2 * v 3 * h 1 + (-2 : ℝ) * ((v 2) ^ 2 * h 1) + v 1 * v 3 * h 0 + (-2 : ℝ) * (v 1 * v 2 * h 0)) * g1
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork18, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g3 : -(v 4) + v 3 + -(v 2) = 0 := by
      nlinarith [heq1]
    have g6 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + v 2 * h 1 + (2 : ℝ) * (v 2 * (v 4) ^ 2) + -(v 1 * h 0) = 0 := by
      nlinarith [hc0]
    have g7 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + v 3 * h 1 + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + -(v 2 * h 1) + (2 : ℝ) * (v 2 * (v 4) ^ 2) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork18, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + -(v 1 * v 3 * v 4 * h 1) + v 1 * v 2 * v 4 * h 1 = 0 := by
      linear_combination
        (v 3 * v 4 * h 1 + (-2 : ℝ) * (v 2 * v 4 * h 1) + v 2 * v 4 * h 0 + -(v 2 * v 3 * h 1) + (2 : ℝ) * ((v 2) ^ 2 * h 1) + -((v 2) ^ 2 * h 0) + v 1 * v 4 * h 0 + -(v 1 * v 2 * h 0) + v 0 * v 4 * h 0) * g0 +
      (-(v 3 * v 4 * h 1) + (2 : ℝ) * (v 2 * v 4 * h 1) + -(v 2 * v 4 * h 0) + -(v 2 * v 3 * h 1) + (2 : ℝ) * ((v 2) ^ 2 * h 1) + -((v 2) ^ 2 * h 0) + -(v 1 * v 4 * h 1) + -((v 1) ^ 2 * h 0) + (2 : ℝ) * (v 0 * v 4 * h 1) + -(v 0 * v 4 * h 0) + -(v 0 * v 3 * h 1) + (2 : ℝ) * (v 0 * v 2 * h 1) + -(v 0 * v 2 * h 0)) * g1 +
      (v 2 * v 3 * h 1 + (-2 : ℝ) * ((v 2) ^ 2 * h 1) + (v 2) ^ 2 * h 0) * g2 +
      ((-2 : ℝ) * (v 0 * v 4 * h 1)) * g3 +
      (-(v 0 * v 4)) * g6 +
      (v 0 * v 4) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork18, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork18, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 3 * (v 4) ^ 2 * h 1 + -(v 3 * (v 4) ^ 2 * h 0) + -((v 3) ^ 2 * v 4 * h 1) + (-2 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (2 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (3 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (-2 : ℝ) * ((v 2) ^ 2 * v 4 * h 1) = 0 := by
      linear_combination
        (-(v 3 * v 4 * h 1) + v 3 * v 4 * h 0 + (v 3) ^ 2 * h 1 + (2 : ℝ) * (v 2 * v 4 * h 1) + (-2 : ℝ) * (v 2 * v 4 * h 0) + (-3 : ℝ) * (v 2 * v 3 * h 1) + (2 : ℝ) * ((v 2) ^ 2 * h 1)) * g2
    nlinarith [hcertificate]

theorem cubicResidualNetwork18_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork18.toNetwork := by
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
  simp [cubicResidualNetwork18, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork18_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork18.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork18_jacobianNonzero
    cubicResidualNetwork18_fourCharts

def cubicResidualNetwork19 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.y, .yy), (.xy, .y)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork19_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork19.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork19, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork19, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork19, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g4 : -(v 3 * v 4) + v 2 * v 4 + -(v 1 * v 3) + v 1 * v 2 = 0 := by
      nlinarith [hdet]
    have g7 : v 3 * h 1 + -(v 2 * h 1) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork19, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
        (v 4 * h 0) * g4 +
      ((v 4) ^ 2 + -(v 2 * v 4)) * g7
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork19, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork19, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork19, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g8 : v 3 * h 1 + -(v 2 * h 1) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork19, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -((v 3) ^ 2 * v 4 * h 1) + (2 : ℝ) * (v 2 * v 3 * v 4 * h 1) + -((v 2) ^ 2 * v 4 * h 1) = 0 := by
      linear_combination
        (-(v 3 * v 4) + v 2 * v 4) * g8
    nlinarith [hcertificate]

theorem cubicResidualNetwork19_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork19.toNetwork := by
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
  simp [cubicResidualNetwork19, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork19_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork19.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork19_jacobianNonzero
    cubicResidualNetwork19_fourCharts

def cubicResidualNetwork20 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.xy, .xx), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork20_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork20.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork20, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g2 : -(v 1 * v 4) + v 1 * v 3 + v 1 * v 2 = 0 := by
      nlinarith [hdet]
    have g3 : (-2 : ℝ) * (v 1 * (v 4) ^ 3) + (6 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (-6 : ℝ) * (v 1 * (v 3) ^ 2 * v 4) + (2 : ℝ) * (v 1 * (v 3) ^ 3) + (2 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (-4 : ℝ) * (v 1 * v 2 * v 3 * v 4) + (2 : ℝ) * (v 1 * v 2 * (v 3) ^ 2) + (-2 : ℝ) * ((v 1) ^ 2 * (v 4) ^ 2) + (4 : ℝ) * ((v 1) ^ 2 * v 3 * v 4) + (-2 : ℝ) * ((v 1) ^ 2 * (v 3) ^ 2) + (2 : ℝ) * ((v 1) ^ 2 * v 2 * v 4) + (-2 : ℝ) * ((v 1) ^ 2 * v 2 * v 3) = 0 := by
      nlinarith [hfold]
    have g4 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + v 3 * h 1 + v 3 * h 0 + (-6 : ℝ) * (v 3 * (v 4) ^ 2) + (6 : ℝ) * ((v 3) ^ 2 * v 4) + (-2 : ℝ) * ((v 3) ^ 3) + v 2 * h 1 + (-2 : ℝ) * (v 2 * (v 4) ^ 2) + (4 : ℝ) * (v 2 * v 3 * v 4) + (-2 : ℝ) * (v 2 * (v 3) ^ 2) + -(v 1 * h 0) + (2 : ℝ) * (v 1 * (v 4) ^ 2) + (-4 : ℝ) * (v 1 * v 3 * v 4) + (2 : ℝ) * (v 1 * (v 3) ^ 2) + (-2 : ℝ) * (v 1 * v 2 * v 4) + (2 : ℝ) * (v 1 * v 2 * v 3) = 0 := by
      nlinarith [hc0]
    simp [-mul_eq_zero, cubicResidualNetwork20, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
        (v 4 * h 1 + -(v 4 * h 0) + -(v 3 * h 1) + v 3 * h 0 + v 2 * h 1 + -(v 1 * h 0)) * g2 +
      (-(v 2)) * g3 +
      (-(v 1 * v 2)) * g4
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork20, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork20, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork20, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g4 : -(v 1 * v 4) + v 1 * v 3 + v 1 * v 2 = 0 := by
      nlinarith [hdet]
    have g5 : (-2 : ℝ) * (v 1 * (v 4) ^ 3) + (6 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (-6 : ℝ) * (v 1 * (v 3) ^ 2 * v 4) + (2 : ℝ) * (v 1 * (v 3) ^ 3) + (2 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (-4 : ℝ) * (v 1 * v 2 * v 3 * v 4) + (2 : ℝ) * (v 1 * v 2 * (v 3) ^ 2) = 0 := by
      nlinarith [hfold]
    have g7 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + -(v 3 * h 1) + -(v 3 * h 0) + (6 : ℝ) * (v 3 * (v 4) ^ 2) + (-6 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + -(v 2 * h 1) + (2 : ℝ) * (v 2 * (v 4) ^ 2) + (-4 : ℝ) * (v 2 * v 3 * v 4) + (2 : ℝ) * (v 2 * (v 3) ^ 2) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork20, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 3 * v 4 * h 0) + v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + -(v 1 * v 2 * v 4 * h 1) + v 1 * v 2 * v 3 * h 1 = 0 := by
      linear_combination
        ((-2 : ℝ) * (v 4 * h 1) + (2 : ℝ) * (v 3 * h 1)) * g4 +
      (v 4 + -(v 3)) * g5 +
      (-(v 1 * v 4) + v 1 * v 3) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork20, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork20, CodedBimolNetwork.toNetwork,
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

theorem cubicResidualNetwork20_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork20.toNetwork := by
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
  simp [cubicResidualNetwork20, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork20_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork20.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork20_jacobianNonzero
    cubicResidualNetwork20_fourCharts

def cubicResidualNetwork21 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.y, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork21_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork21.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork21, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + (2 : ℝ) * (v 2) + -(v 1) + v 0 = 0 := by
      nlinarith [heq0]
    have g1 : -(v 4) + v 3 + -(v 2) = 0 := by
      nlinarith [heq1]
    have g2 : -(v 3 * v 4) + (3 : ℝ) * (v 2 * v 4) + v 1 * v 4 + -(v 1 * v 3) + v 1 * v 2 = 0 := by
      nlinarith [hdet]
    have g3 : (2 : ℝ) * (v 1 * (v 4) ^ 3) + (-4 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 1) ^ 2 * (v 4) ^ 2) + (-4 : ℝ) * ((v 1) ^ 2 * v 2 * v 4) = 0 := by
      nlinarith [hfold]
    have g4 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (2 : ℝ) * (v 2 * h 1) + (-4 : ℝ) * (v 2 * (v 4) ^ 2) + -(v 1 * h 0) + (2 : ℝ) * (v 1 * (v 4) ^ 2) + (-4 : ℝ) * (v 1 * v 2 * v 4) = 0 := by
      nlinarith [hc0]
    have g5 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + v 3 * h 1 + -(v 2 * h 1) + (-4 : ℝ) * (v 2 * (v 4) ^ 2) + (2 : ℝ) * (v 1 * (v 4) ^ 2) + (-4 : ℝ) * (v 1 * v 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork21, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 2 * v 4 * h 1) + -((v 1) ^ 2 * v 4 * h 0) = 0 := by
      linear_combination
        (-(v 2 * v 3 * h 1) + (3 : ℝ) * ((v 2) ^ 2 * h 1) + -(v 1 * v 2 * h 0)) * g0 +
      ((-2 : ℝ) * ((v 3) ^ 2 * h 1) + (4 : ℝ) * (v 2 * v 3 * h 1) + (6 : ℝ) * ((v 2) ^ 2 * h 1) + (-2 : ℝ) * (v 1 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 3 * h 1) + (-2 : ℝ) * (v 1 * v 3 * h 0) + (-6 : ℝ) * (v 1 * v 2 * h 1) + (-2 : ℝ) * (v 1 * v 2 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * h 1) + (2 : ℝ) * ((v 1) ^ 2 * h 0)) * g1 +
      ((2 : ℝ) * (v 3 * h 1) + (3 : ℝ) * (v 2 * h 1) + (-2 : ℝ) * (v 1 * h 1) + v 1 * h 0) * g2 +
      (-(v 4) + -(v 3) + (-6 : ℝ) * (v 2)) * g3 +
      ((-2 : ℝ) * ((v 3) ^ 2) + v 1 * v 3 + -(v 0 * v 2)) * g4 +
      ((2 : ℝ) * ((v 3) ^ 2) + v 1 * v 4 + (6 : ℝ) * (v 1 * v 2) + v 0 * v 2) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork21, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork21, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 3 * (v 4) ^ 2 * h 1 + -(v 3 * (v 4) ^ 2 * h 0) + (-3 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (3 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (6 : ℝ) * ((v 2) ^ 2 * v 4 * h 1) + -(v 1 * v 3 * v 4 * h 0) + (3 : ℝ) * (v 1 * v 2 * v 4 * h 0) = 0 := by
      linear_combination
        (-(v 3 * v 4 * h 1) + v 3 * v 4 * h 0 + (3 : ℝ) * (v 2 * v 4 * h 1) + (-3 : ℝ) * (v 2 * v 4 * h 0) + (2 : ℝ) * (v 2 * v 3 * h 1) + (-6 : ℝ) * ((v 2) ^ 2 * h 1) + v 1 * v 3 * h 0 + (-3 : ℝ) * (v 1 * v 2 * h 0)) * g1
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork21, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : -(v 4) + (2 : ℝ) * (v 2) = 0 := by
      nlinarith [hg1]
    have g2 : -(v 4) + (2 : ℝ) * (v 2) + -(v 1) + v 0 = 0 := by
      nlinarith [heq0]
    have g3 : -(v 4) + v 3 + -(v 2) = 0 := by
      nlinarith [heq1]
    have g6 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + (2 : ℝ) * (v 2 * h 1) + (2 : ℝ) * (v 2 * (v 4) ^ 2) + -(v 1 * h 0) = 0 := by
      nlinarith [hc0]
    have g7 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + v 3 * h 1 + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + -(v 2 * h 1) + (2 : ℝ) * (v 2 * (v 4) ^ 2) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork21, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + -(v 1 * v 3 * v 4 * h 1) + v 1 * v 2 * v 4 * h 1 = 0 := by
      linear_combination
        (v 3 * v 4 * h 1 + (-3 : ℝ) * (v 2 * v 4 * h 1) + (2 : ℝ) * (v 2 * v 4 * h 0) + (-2 : ℝ) * (v 2 * v 3 * h 1) + (6 : ℝ) * ((v 2) ^ 2 * h 1) + (-4 : ℝ) * ((v 2) ^ 2 * h 0) + -(v 1 * v 4 * h 1) + v 1 * v 4 * h 0 + v 1 * v 3 * h 1 + -(v 1 * v 2 * h 1) + (-2 : ℝ) * (v 1 * v 2 * h 0) + v 0 * v 4 * h 0 + -(v 0 * v 1 * h 0)) * g0 +
      (-(v 3 * v 4 * h 1) + (3 : ℝ) * (v 2 * v 4 * h 1) + (-2 : ℝ) * (v 2 * v 4 * h 0) + (-4 : ℝ) * ((v 2) ^ 2 * h 0) + (v 1) ^ 2 * h 1 + -((v 1) ^ 2 * h 0) + -(v 0 * v 4 * h 0) + (-2 : ℝ) * (v 0 * v 2 * h 0) + -(v 0 * v 1 * h 1) + -(v 0 * v 1 * h 0) + -((v 0) ^ 2 * h 1)) * g1 +
      ((4 : ℝ) * ((v 2) ^ 2 * h 0) + -(v 1 * v 3 * h 1) + (3 : ℝ) * (v 1 * v 2 * h 1) + v 0 * v 1 * h 0) * g2 +
      (v 0 * v 1 * h 1 + (v 0) ^ 2 * h 1) * g3 +
      ((v 0) ^ 2) * g6 +
      (-((v 0) ^ 2)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork21, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork21, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 3 * (v 4) ^ 2 * h 1 + -(v 3 * (v 4) ^ 2 * h 0) + -((v 3) ^ 2 * v 4 * h 1) + (-3 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (3 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (4 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (-3 : ℝ) * ((v 2) ^ 2 * v 4 * h 1) = 0 := by
      linear_combination
        (-(v 3 * v 4 * h 1) + v 3 * v 4 * h 0 + (v 3) ^ 2 * h 1 + (3 : ℝ) * (v 2 * v 4 * h 1) + (-3 : ℝ) * (v 2 * v 4 * h 0) + (-4 : ℝ) * (v 2 * v 3 * h 1) + (3 : ℝ) * ((v 2) ^ 2 * h 1)) * g2
    nlinarith [hcertificate]

theorem cubicResidualNetwork21_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork21.toNetwork := by
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
  simp [cubicResidualNetwork21, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork21_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork21.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork21_jacobianNonzero
    cubicResidualNetwork21_fourCharts

def cubicResidualNetwork22 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.y, .yy), (.xy, .y)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork22_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork22.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork22, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork22, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork22, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g4 : -(v 3 * v 4) + v 2 * v 4 + -(v 1 * v 3) + v 1 * v 2 = 0 := by
      nlinarith [hdet]
    have g7 : v 3 * h 1 + -(v 2 * h 1) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork22, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 3 * (v 4) ^ 2 * h 1 + -(v 3 * (v 4) ^ 2 * h 0) + -(v 2 * (v 4) ^ 2 * h 1) + v 2 * (v 4) ^ 2 * h 0 + (-2 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (2 : ℝ) * ((v 2) ^ 2 * v 4 * h 1) + -(v 1 * v 3 * v 4 * h 0) + v 1 * v 2 * v 4 * h 0 = 0 := by
      linear_combination
        (v 4 * h 0) * g4 +
      ((v 4) ^ 2 + (-2 : ℝ) * (v 2 * v 4)) * g7
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork22, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork22, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork22, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g8 : v 3 * h 1 + -(v 2 * h 1) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork22, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -((v 3) ^ 2 * v 4 * h 1) + (2 : ℝ) * (v 2 * v 3 * v 4 * h 1) + -((v 2) ^ 2 * v 4 * h 1) = 0 := by
      linear_combination
        (-(v 3 * v 4) + v 2 * v 4) * g8
    nlinarith [hcertificate]

theorem cubicResidualNetwork22_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork22.toNetwork := by
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
  simp [cubicResidualNetwork22, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork22_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork22.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork22_jacobianNonzero
    cubicResidualNetwork22_fourCharts

def cubicResidualNetwork23 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.xy, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork23_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork23.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork23, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : v 4 + -(v 3) + -(v 2) = 0 := by
      nlinarith [heq1]
    have g2 : -(v 2 * v 4) + (3 : ℝ) * (v 2 * v 3) + -(v 1 * v 4) + v 1 * v 3 + v 1 * v 2 = 0 := by
      nlinarith [hdet]
    have g3 : (-2 : ℝ) * (v 1 * (v 4) ^ 3) + (-2 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (2 : ℝ) * (v 1 * (v 3) ^ 2 * v 4) + (2 : ℝ) * (v 1 * (v 3) ^ 3) + (4 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (-4 : ℝ) * (v 1 * v 2 * (v 3) ^ 2) + (-2 : ℝ) * ((v 1) ^ 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 1) ^ 2 * (v 3) ^ 2) + (4 : ℝ) * ((v 1) ^ 2 * v 2 * v 4) + (-4 : ℝ) * ((v 1) ^ 2 * v 2 * v 3) = 0 := by
      nlinarith [hfold]
    have g5 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + -(v 3 * h 1) + -(v 3 * h 0) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + (2 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + -(v 2 * h 1) + (4 : ℝ) * (v 2 * (v 4) ^ 2) + (-4 : ℝ) * (v 2 * (v 3) ^ 2) + (-2 : ℝ) * (v 1 * (v 4) ^ 2) + (2 : ℝ) * (v 1 * (v 3) ^ 2) + (4 : ℝ) * (v 1 * v 2 * v 4) + (-4 : ℝ) * (v 1 * v 2 * v 3) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork23, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + (2 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (-2 : ℝ) * (v 1 * v 2 * v 3 * h 1) + (v 1) ^ 2 * v 4 * h 0 + -((v 1) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        (((-7 : ℝ) / 3) * (v 1 * v 4 * h 1) + ((-1 : ℝ) / 3) * (v 1 * v 4 * h 0) + -(v 1 * v 3 * h 1) + v 1 * v 3 * h 0 + (-2 : ℝ) * ((v 1) ^ 2 * h 1) + ((1 : ℝ) / 3) * ((v 1) ^ 2 * h 0)) * g1 +
      (-(v 1 * h 1) + ((1 : ℝ) / 3) * (v 1 * h 0)) * g2 +
      (((-4 : ℝ) / 3) * (v 4) + -(v 1)) * g3 +
      (((4 : ℝ) / 3) * (v 1 * v 4) + (v 1) ^ 2) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork23, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + -(v 3) + -(v 1) = 0 := by
      nlinarith [hg0]
    have g1 : v 4 + -(v 3) = 0 := by
      nlinarith [hg1]
    have g3 : v 4 + -(v 3) + -(v 2) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork23, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 2 * (v 4) ^ 2 * h 1 + -(v 2 * (v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (2 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (-3 : ℝ) * (v 2 * (v 3) ^ 2 * h 1) + (3 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + (-2 : ℝ) * ((v 2) ^ 2 * v 4 * h 1) + (6 : ℝ) * ((v 2) ^ 2 * v 3 * h 1) + -(v 1 * v 2 * v 4 * h 0) + (3 : ℝ) * (v 1 * v 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((-2 : ℝ) * (v 2 * v 4 * h 0) + (2 : ℝ) * (v 2 * v 3 * h 1) + -(v 1 * v 2 * h 1)) * g0 +
      (-(v 2 * v 4 * h 1) + (-3 : ℝ) * (v 2 * v 4 * h 0) + (7 : ℝ) * (v 2 * v 3 * h 1) + (-3 : ℝ) * (v 2 * v 3 * h 0) + -(v 1 * v 2 * h 1) + (-3 : ℝ) * (v 1 * v 2 * h 0) + -((v 1) ^ 2 * h 1)) * g1 +
      ((2 : ℝ) * (v 2 * v 4 * h 1) + (-6 : ℝ) * (v 2 * v 3 * h 1) + (v 1) ^ 2 * h 1) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork23, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + -(v 3) + -(v 1) = 0 := by
      nlinarith [hg0]
    have g1 : -(v 4) + -(v 3) + (2 : ℝ) * (v 2) = 0 := by
      nlinarith [hg1]
    have g3 : v 4 + -(v 3) + -(v 2) = 0 := by
      nlinarith [heq1]
    have g4 : -(v 2 * v 4) + (3 : ℝ) * (v 2 * v 3) + -(v 1 * v 4) + v 1 * v 3 + v 1 * v 2 = 0 := by
      nlinarith [hdet]
    have g5 : (-2 : ℝ) * (v 1 * (v 4) ^ 3) + (6 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (-6 : ℝ) * (v 1 * (v 3) ^ 2 * v 4) + (2 : ℝ) * (v 1 * (v 3) ^ 3) + (2 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (-4 : ℝ) * (v 1 * v 2 * v 3 * v 4) + (2 : ℝ) * (v 1 * v 2 * (v 3) ^ 2) = 0 := by
      nlinarith [hfold]
    have g7 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + -(v 3 * h 1) + -(v 3 * h 0) + (6 : ℝ) * (v 3 * (v 4) ^ 2) + (-6 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + -(v 2 * h 1) + (2 : ℝ) * (v 2 * (v 4) ^ 2) + (-4 : ℝ) * (v 2 * v 3 * v 4) + (2 : ℝ) * (v 2 * (v 3) ^ 2) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork23, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 3 * v 4 * h 0) + v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + -(v 1 * v 2 * v 4 * h 1) + v 1 * v 2 * v 3 * h 1 = 0 := by
      linear_combination
        (((3 : ℝ) / 2) * ((v 3) ^ 2 * h 0) + ((-1 : ℝ) / 4) * (v 2 * v 4 * h 0) + ((1 : ℝ) / 2) * (v 1 * v 4 * h 0) + ((-1 : ℝ) / 2) * (v 1 * v 3 * h 0)) * g0 +
      (-(v 3 * v 4 * h 0) + ((-1 : ℝ) / 2) * ((v 3) ^ 2 * h 0) + v 1 * v 4 * h 1 + ((-3 : ℝ) / 4) * (v 1 * v 4 * h 0) + -(v 1 * v 3 * h 1) + -(v 1 * v 2 * h 1)) * g1 +
      (-(v 3 * v 4 * h 0) + -((v 3) ^ 2 * h 0) + (2 : ℝ) * (v 1 * v 4 * h 1) + -(v 1 * v 4 * h 0) + (-2 : ℝ) * (v 1 * v 2 * h 1) + ((-1 : ℝ) / 2) * ((v 1) ^ 2 * h 1)) * g3 +
      (((1 : ℝ) / 4) * (v 4 * h 0)) * g4 +
      (((-1 : ℝ) / 2) * (v 1)) * g5 +
      (((1 : ℝ) / 2) * ((v 1) ^ 2)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork23, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g4 : v 4 + -(v 3) + -(v 2) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork23, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -(v 2 * (v 4) ^ 2 * h 1) + v 2 * (v 4) ^ 2 * h 0 + (4 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (-4 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (-3 : ℝ) * (v 2 * (v 3) ^ 2 * h 1) + (3 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + (v 2) ^ 2 * v 4 * h 1 + (-3 : ℝ) * ((v 2) ^ 2 * v 3 * h 1) = 0 := by
      linear_combination
        (v 2 * v 4 * h 0 + (-3 : ℝ) * (v 2 * v 3 * h 0)) * g2 +
      (-(v 2 * v 4 * h 1) + (3 : ℝ) * (v 2 * v 3 * h 1)) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork23_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork23.toNetwork := by
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
  simp [cubicResidualNetwork23, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork23_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork23.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork23_jacobianNonzero
    cubicResidualNetwork23_fourCharts

def cubicResidualNetwork24 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.xy, .x), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork24_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork24.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork24, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + (2 : ℝ) * (v 2) + -(v 1) + v 0 = 0 := by
      nlinarith [heq0]
    have g1 : v 4 + -(v 3) + -(v 2) = 0 := by
      nlinarith [heq1]
    have g2 : -(v 2 * v 4) + (2 : ℝ) * (v 2 * v 3) + -(v 1 * v 4) + v 1 * v 3 + v 1 * v 2 = 0 := by
      nlinarith [hdet]
    have g3 : (-2 : ℝ) * (v 1 * (v 4) ^ 3) + (2 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (4 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (-4 : ℝ) * (v 1 * v 2 * v 3 * v 4) + (-2 : ℝ) * ((v 1) ^ 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 1) ^ 2 * v 3 * v 4) + (4 : ℝ) * ((v 1) ^ 2 * v 2 * v 4) + (-4 : ℝ) * ((v 1) ^ 2 * v 2 * v 3) = 0 := by
      nlinarith [hfold]
    have g4 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (2 : ℝ) * (v 2 * h 1) + (-4 : ℝ) * (v 2 * (v 4) ^ 2) + -(v 1 * h 0) + (2 : ℝ) * (v 1 * (v 4) ^ 2) + (-4 : ℝ) * (v 1 * v 2 * v 4) = 0 := by
      nlinarith [hc0]
    have g5 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + -(v 3 * h 1) + -(v 3 * h 0) + (2 : ℝ) * (v 3 * (v 4) ^ 2) + -(v 2 * h 1) + (4 : ℝ) * (v 2 * (v 4) ^ 2) + (-4 : ℝ) * (v 2 * v 3 * v 4) + (-2 : ℝ) * (v 1 * (v 4) ^ 2) + (2 : ℝ) * (v 1 * v 3 * v 4) + (4 : ℝ) * (v 1 * v 2 * v 4) + (-4 : ℝ) * (v 1 * v 2 * v 3) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork24, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + v 1 * v 3 * v 4 * h 1 + -(v 1 * v 3 * v 4 * h 0) + (2 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (-2 : ℝ) * (v 1 * v 2 * v 3 * h 1) + (v 1) ^ 2 * v 4 * h 0 + -((v 1) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((2 : ℝ) * (v 2 * v 4 * h 1) + (-4 : ℝ) * ((v 2) ^ 2 * h 1)) * g0 +
      ((3 : ℝ) * (v 2 * v 4 * h 1) + (2 : ℝ) * (v 2 * v 3 * h 1) + (-8 : ℝ) * ((v 2) ^ 2 * h 1) + v 1 * v 4 * h 0 + -(v 1 * v 3 * h 0) + (-4 : ℝ) * (v 0 * v 2 * h 1) + (-2 : ℝ) * (v 0 * v 1 * h 1)) * g1 +
      (v 4 * h 1 + -(v 3 * h 0) + (-3 : ℝ) * (v 2 * h 1) + -(v 1 * h 0) + (-2 : ℝ) * (v 0 * h 1) + (2 : ℝ) * (v 3 * (v 4) ^ 2) + (-4 : ℝ) * (v 2 * v 3 * v 4) + (2 : ℝ) * (v 1 * v 3 * v 4) + (-4 : ℝ) * (v 1 * v 2 * v 3)) * g2 +
      (-(v 3)) * g3 +
      (-(v 2 * v 3) + -(v 1 * v 2)) * g4 +
      ((-2 : ℝ) * (v 2 * v 3) + -(v 1 * v 2)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork24, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : v 4 + -(v 3) = 0 := by
      nlinarith [hg1]
    have g3 : v 4 + -(v 3) + -(v 2) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork24, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 2 * (v 4) ^ 2 * h 1 + -(v 2 * (v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (2 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (-2 : ℝ) * ((v 2) ^ 2 * v 4 * h 1) + (4 : ℝ) * ((v 2) ^ 2 * v 3 * h 1) + -(v 1 * v 2 * v 4 * h 0) + (2 : ℝ) * (v 1 * v 2 * v 3 * h 0) = 0 := by
      linear_combination
        (-(v 2 * v 4 * h 1) + v 2 * v 4 * h 0 + (2 : ℝ) * (v 2 * v 3 * h 1) + (-2 : ℝ) * (v 2 * v 3 * h 0) + (-2 : ℝ) * ((v 2) ^ 2 * h 1) + -(v 1 * v 2 * h 1)) * g0 +
      ((-4 : ℝ) * ((v 2) ^ 2 * h 1) + (-4 : ℝ) * (v 1 * v 2 * h 1) + -((v 1) ^ 2 * h 1)) * g1 +
      ((2 : ℝ) * (v 1 * v 2 * h 1) + (v 1) ^ 2 * h 1) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork24, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : -(v 4) + (2 : ℝ) * (v 2) = 0 := by
      nlinarith [hg1]
    have g2 : -(v 4) + (2 : ℝ) * (v 2) + -(v 1) + v 0 = 0 := by
      nlinarith [heq0]
    have g3 : v 4 + -(v 3) + -(v 2) = 0 := by
      nlinarith [heq1]
    have g5 : (-2 : ℝ) * (v 1 * (v 4) ^ 3) + (6 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (-6 : ℝ) * (v 1 * (v 3) ^ 2 * v 4) + (2 : ℝ) * (v 1 * (v 3) ^ 3) + (2 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (-4 : ℝ) * (v 1 * v 2 * v 3 * v 4) + (2 : ℝ) * (v 1 * v 2 * (v 3) ^ 2) = 0 := by
      nlinarith [hfold]
    have g7 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + -(v 3 * h 1) + -(v 3 * h 0) + (6 : ℝ) * (v 3 * (v 4) ^ 2) + (-6 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + -(v 2 * h 1) + (2 : ℝ) * (v 2 * (v 4) ^ 2) + (-4 : ℝ) * (v 2 * v 3 * v 4) + (2 : ℝ) * (v 2 * (v 3) ^ 2) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork24, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 3 * v 4 * h 0) + v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + -(v 1 * v 2 * v 4 * h 1) + v 1 * v 2 * v 3 * h 1 = 0 := by
      linear_combination
        (-((v 4) ^ 2 * h 1) + -(v 3 * v 4 * h 0) + (-3 : ℝ) * ((v 3) ^ 2 * h 1) + (2 : ℝ) * (v 2 * v 4 * h 1) + (3 : ℝ) * (v 2 * v 3 * h 1) + (2 : ℝ) * (v 2 * v 3 * h 0) + ((-3 : ℝ) / 2) * (v 1 * v 3 * h 0) + -(v 1 * v 2 * h 1) + v 1 * v 2 * h 0 + ((1 : ℝ) / 2) * ((v 1) ^ 2 * h 1) + ((-1 : ℝ) / 2) * ((v 1) ^ 2 * h 0) + ((-1 : ℝ) / 2) * (v 0 * v 3 * h 1) + v 0 * v 3 * h 0 + ((3 : ℝ) / 2) * (v 0 * v 2 * h 1) + ((-1 : ℝ) / 2) * (v 0 * v 1 * h 1) + ((1 : ℝ) / 2) * (v 0 * v 1 * h 0)) * g0 +
      ((v 4) ^ 2 * h 1 + v 3 * v 4 * h 0 + (v 3) ^ 2 * h 1 + -((v 3) ^ 2 * h 0) + (3 : ℝ) * (v 2 * v 3 * h 1) + -(v 2 * v 3 * h 0) + (2 : ℝ) * (v 1 * v 3 * h 1) + ((5 : ℝ) / 2) * (v 0 * v 3 * h 1) + ((3 : ℝ) / 2) * (v 0 * v 2 * h 1) + v 0 * v 1 * h 1) * g1 +
      ((2 : ℝ) * ((v 3) ^ 2 * h 1) + (v 3) ^ 2 * h 0 + v 2 * v 3 * h 0 + ((3 : ℝ) / 2) * (v 1 * v 3 * h 0) + ((-1 : ℝ) / 2) * ((v 1) ^ 2 * h 1) + ((1 : ℝ) / 2) * ((v 1) ^ 2 * h 0)) * g2 +
      ((6 : ℝ) * (v 2 * v 3 * h 1) + -(v 1 * v 4 * h 0) + (2 : ℝ) * (v 0 * v 3 * h 1) + v 0 * v 3 * h 0 + (3 : ℝ) * (v 0 * v 2 * h 1)) * g3 +
      (((-1 : ℝ) / 2) * (v 0)) * g5 +
      (((1 : ℝ) / 2) * (v 0 * v 1)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork24, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : -(v 4) + (2 : ℝ) * (v 2) = 0 := by
      nlinarith [hg1]
    have g2 : v 4 + -(v 3) = 0 := by
      nlinarith [hg2]
    have g4 : v 4 + -(v 3) + -(v 2) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork24, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -(v 2 * (v 4) ^ 2 * h 1) + v 2 * (v 4) ^ 2 * h 0 + (3 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (-3 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (-2 : ℝ) * (v 2 * (v 3) ^ 2 * h 1) + (2 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + (v 2) ^ 2 * v 4 * h 1 + (-2 : ℝ) * ((v 2) ^ 2 * v 3 * h 1) = 0 := by
      linear_combination
        (((-1 : ℝ) / 2) * ((v 4) ^ 2 * h 0) + (2 : ℝ) * ((v 3) ^ 2 * h 0) + ((-3 : ℝ) / 2) * (v 1 * v 4 * h 0)) * g0 +
      (((1 : ℝ) / 2) * ((v 4) ^ 2 * h 0) + (-2 : ℝ) * ((v 3) ^ 2 * h 0) + (-3 : ℝ) * (v 2 * v 3 * h 0) + ((3 : ℝ) / 2) * ((v 1) ^ 2 * h 0)) * g1 +
      ((-2 : ℝ) * (v 1 * v 4 * h 0) + (-2 : ℝ) * (v 1 * v 3 * h 0) + (-3 : ℝ) * ((v 1) ^ 2 * h 0)) * g2 +
      (-(v 2 * v 4 * h 1) + (2 : ℝ) * (v 2 * v 3 * h 1) + (-6 : ℝ) * (v 2 * v 3 * h 0) + (3 : ℝ) * ((v 1) ^ 2 * h 0)) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork24_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork24.toNetwork := by
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
  simp [cubicResidualNetwork24, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork24_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork24.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork24_jacobianNonzero
    cubicResidualNetwork24_fourCharts

def cubicResidualNetwork25 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.xy, .y), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork25_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork25.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork25, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + -(v 3) + (2 : ℝ) * (v 2) + -(v 1) + v 0 = 0 := by
      nlinarith [heq0]
    have g1 : v 4 + -(v 2) = 0 := by
      nlinarith [heq1]
    have g2 : -(v 2 * v 4) + v 2 * v 3 + -(v 1 * v 4) + v 1 * v 2 = 0 := by
      nlinarith [hdet]
    have g3 : (-2 : ℝ) * (v 1 * (v 4) ^ 3) + (-4 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * (v 3) ^ 2 * v 4) + (4 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (4 : ℝ) * (v 1 * v 2 * v 3 * v 4) + (-2 : ℝ) * ((v 1) ^ 2 * (v 4) ^ 2) + (-2 : ℝ) * ((v 1) ^ 2 * v 3 * v 4) + (4 : ℝ) * ((v 1) ^ 2 * v 2 * v 4) = 0 := by
      nlinarith [hfold]
    have g5 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + (-4 : ℝ) * (v 3 * (v 4) ^ 2) + (-2 : ℝ) * ((v 3) ^ 2 * v 4) + -(v 2 * h 1) + (4 : ℝ) * (v 2 * (v 4) ^ 2) + (4 : ℝ) * (v 2 * v 3 * v 4) + (-2 : ℝ) * (v 1 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * v 3 * v 4) + (4 : ℝ) * (v 1 * v 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork25, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + -(v 1 * v 3 * v 4 * h 1) + v 1 * v 3 * v 4 * h 0 + (2 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (v 1) ^ 2 * v 4 * h 0 = 0 := by
      linear_combination
        (-(v 1 * v 2 * h 0)) * g0 +
      ((-3 : ℝ) * (v 1 * v 4 * h 1) + -(v 1 * v 4 * h 0) + -(v 1 * v 3 * h 1) + v 1 * v 3 * h 0 + (-2 : ℝ) * (v 1 * v 2 * h 0) + -((v 1) ^ 2 * h 1) + (v 1) ^ 2 * h 0 + -(v 0 * v 1 * h 1) + -(v 0 * v 1 * h 0)) * g1 +
      (-(v 1 * h 1)) * g2 +
      ((-2 : ℝ) * (v 4) + -(v 0)) * g3 +
      ((2 : ℝ) * (v 1 * v 4) + v 0 * v 1) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork25, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g3 : v 4 + -(v 2) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork25, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 2 * (v 4) ^ 2 * h 1 + -(v 2 * (v 4) ^ 2 * h 0) + -(v 2 * (v 3) ^ 2 * h 1) + v 2 * (v 3) ^ 2 * h 0 + (-2 : ℝ) * ((v 2) ^ 2 * v 4 * h 1) + (2 : ℝ) * ((v 2) ^ 2 * v 3 * h 1) + -(v 1 * v 2 * v 4 * h 0) + v 1 * v 2 * v 3 * h 0 = 0 := by
      linear_combination
        (-((v 3) ^ 2 * h 1) + (v 3) ^ 2 * h 0 + v 2 * v 4 * h 1 + -(v 2 * v 4 * h 0) + (2 : ℝ) * (v 2 * v 3 * h 1) + (-2 : ℝ) * ((v 2) ^ 2 * h 1) + v 1 * v 3 * h 0 + -(v 1 * v 2 * h 0)) * g1 +
      ((v 3) ^ 2 * h 1 + -((v 3) ^ 2 * h 0) + (-2 : ℝ) * (v 2 * v 3 * h 1) + -(v 1 * v 3 * h 0)) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork25, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g3 : v 4 + -(v 2) = 0 := by
      nlinarith [heq1]
    have g5 : (-2 : ℝ) * (v 1 * (v 4) ^ 3) + (2 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) = 0 := by
      nlinarith [hfold]
    have g7 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + -(v 2 * h 1) + (2 : ℝ) * (v 2 * (v 4) ^ 2) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork25, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
        ((2 : ℝ) * (v 1 * v 4 * h 1)) * g3 +
      (v 4) * g5 +
      (-(v 1 * v 4)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork25, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g4 : v 4 + -(v 2) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork25, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
        (-(v 2 * v 4 * h 1) + v 2 * v 4 * h 0 + -(v 2 * v 3 * h 0) + (v 2) ^ 2 * h 1) * g2 +
      (v 2 * v 3 * h 1) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork25_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork25.toNetwork := by
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
  simp [cubicResidualNetwork25, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork25_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork25.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork25_jacobianNonzero
    cubicResidualNetwork25_fourCharts

end SmallCusp

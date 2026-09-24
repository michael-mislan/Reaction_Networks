import proofs.SmallCusp.Obstruction.CubicDegeneracy
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

def cubicResidualNetwork46 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .x), (.xx, .zero), (.xx, .x), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork46_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork46.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork46, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g2 : (-2 : ℝ) * (v 3 * v 4) + (-4 : ℝ) * (v 2 * v 4) + (2 : ℝ) * (v 1 * v 3) + (4 : ℝ) * (v 1 * v 2) = 0 := by
      nlinarith [hdet]
    have g3 : (-6 : ℝ) * (v 3 * (v 4) ^ 3) + (-8 : ℝ) * ((v 3) ^ 2 * (v 4) ^ 2) + (-12 : ℝ) * (v 2 * (v 4) ^ 3) + (-32 : ℝ) * (v 2 * v 3 * (v 4) ^ 2) + (-32 : ℝ) * ((v 2) ^ 2 * (v 4) ^ 2) + (8 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (8 : ℝ) * (v 1 * (v 3) ^ 2 * v 4) + (16 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (32 : ℝ) * (v 1 * v 2 * v 3 * v 4) + (32 : ℝ) * (v 1 * (v 2) ^ 2 * v 4) + (-2 : ℝ) * ((v 1) ^ 2 * v 3 * v 4) + (-4 : ℝ) * ((v 1) ^ 2 * v 2 * v 4) = 0 := by
      nlinarith [hfold]
    have g4 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (-2 : ℝ) * (v 3 * h 0) + (2 : ℝ) * (v 3 * (v 4) ^ 2) + (-4 : ℝ) * (v 2 * h 0) + (4 : ℝ) * (v 2 * (v 4) ^ 2) + v 1 * h 1 + (-2 : ℝ) * (v 1 * (v 4) ^ 2) + (-2 : ℝ) * ((v 1) ^ 2 * v 3) + (-4 : ℝ) * ((v 1) ^ 2 * v 2) = 0 := by
      nlinarith [hc0]
    have g5 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + (-4 : ℝ) * (v 3 * (v 4) ^ 2) + (-8 : ℝ) * (v 2 * (v 4) ^ 2) + -(v 1 * h 1) + (2 : ℝ) * (v 1 * (v 4) ^ 2) + (4 : ℝ) * (v 1 * v 3 * v 4) + (8 : ℝ) * (v 1 * v 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork46, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-2 : ℝ) * (v 3 * (v 4) ^ 2 * h 1) + (4 : ℝ) * (v 3 * (v 4) ^ 2 * h 0) + (4 : ℝ) * ((v 3) ^ 2 * v 4 * h 0) + (-4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (16 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (16 : ℝ) * ((v 2) ^ 2 * v 4 * h 0) + (2 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (-2 : ℝ) * (v 1 * v 3 * v 4 * h 0) + (4 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 2 * v 4 * h 0) = 0 := by
      linear_combination
        (v 4 * h 1 + ((-1 : ℝ) / 2) * (v 4 * h 0) + (2 : ℝ) * (v 3 * h 1) + ((-1 : ℝ) / 2) * (v 1 * h 1)) * g2 +
      (((1 : ℝ) / 2) * (v 4) + (-2 : ℝ) * (v 3)) * g3 +
      (((-3 : ℝ) / 2) * ((v 4) ^ 2) + (-4 : ℝ) * (v 2 * v 4)) * g4 +
      (((-3 : ℝ) / 2) * ((v 4) ^ 2) + (4 : ℝ) * ((v 3) ^ 2) + (-4 : ℝ) * (v 2 * v 4) + (8 : ℝ) * (v 2 * v 3) + -(v 1 * v 3) + (-2 : ℝ) * (v 1 * v 2)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork46, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g4 : (-2 : ℝ) * (v 3 * v 4) + (-4 : ℝ) * (v 2 * v 4) + (2 : ℝ) * (v 1 * v 3) + (4 : ℝ) * (v 1 * v 2) = 0 := by
      nlinarith [hdet]
    simp [-mul_eq_zero, cubicResidualNetwork46, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (2 : ℝ) * (v 3 * (v 4) ^ 2 * h 0) + (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 1 * v 3 * v 4 * h 0) + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (2 : ℝ) * ((v 1) ^ 2 * v 3 * h 0) + (4 : ℝ) * ((v 1) ^ 2 * v 2 * h 0) = 0 := by
      linear_combination
        (-(v 4 * h 0) + v 1 * h 0) * g4
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork46, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g4 : (-2 : ℝ) * (v 3 * v 4) + (-4 : ℝ) * (v 2 * v 4) + (2 : ℝ) * (v 1 * v 3) + (4 : ℝ) * (v 1 * v 2) = 0 := by
      nlinarith [hdet]
    have g5 : (-6 : ℝ) * (v 3 * (v 4) ^ 3) + (-12 : ℝ) * (v 2 * (v 4) ^ 3) + (8 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (16 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (-2 : ℝ) * ((v 1) ^ 2 * v 3 * v 4) + (-4 : ℝ) * ((v 1) ^ 2 * v 2 * v 4) = 0 := by
      nlinarith [hfold]
    have g7 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + -(v 1 * h 1) + (2 : ℝ) * (v 1 * (v 4) ^ 2) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork46, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (2 : ℝ) * (v 3 * (v 4) ^ 2 * h 1) + (-4 : ℝ) * (v 3 * (v 4) ^ 2 * h 0) + (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 3 * v 4 * h 0) + (-4 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (4 : ℝ) * (v 1 * v 2 * v 4 * h 0) = 0 := by
      linear_combination
        (((-5 : ℝ) / 2) * (v 4 * h 1) + ((1 : ℝ) / 2) * (v 4 * h 0) + ((1 : ℝ) / 2) * (v 1 * h 1)) * g4 +
      (v 4) * g5 +
      ((-3 : ℝ) * (v 3 * v 4) + (-6 : ℝ) * (v 2 * v 4) + v 1 * v 3 + (2 : ℝ) * (v 1 * v 2)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork46, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g5 : (-2 : ℝ) * (v 3 * v 4) + (-4 : ℝ) * (v 2 * v 4) + (2 : ℝ) * (v 1 * v 3) + (4 : ℝ) * (v 1 * v 2) = 0 := by
      nlinarith [hdet]
    simp [-mul_eq_zero, cubicResidualNetwork46, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
        (v 4 * h 0 + -(v 1 * h 0)) * g5
    nlinarith [hcertificate]

theorem cubicResidualNetwork46_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork46.toNetwork := by
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
  simp [cubicResidualNetwork46, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork46_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork46.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork46_jacobianNonzero
    cubicResidualNetwork46_fourCharts

def cubicResidualNetwork47 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xx, .x), (.xy, .x)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork47_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork47.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork47, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g4 : (-2 : ℝ) * (v 3 * h 0) + (-4 : ℝ) * (v 2 * h 0) = 0 := by
      nlinarith [hc0]
    simp [-mul_eq_zero, cubicResidualNetwork47, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * ((v 3) ^ 2 * v 4 * h 0) + (-16 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (-16 : ℝ) * ((v 2) ^ 2 * v 4 * h 0) = 0 := by
      linear_combination
        ((2 : ℝ) * (v 3 * v 4) + (4 : ℝ) * (v 2 * v 4)) * g4
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork47, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork47, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork47, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g4 : (2 : ℝ) * (v 3 * v 4) + (4 : ℝ) * (v 2 * v 4) + (-2 : ℝ) * (v 1 * v 3) + (-4 : ℝ) * (v 1 * v 2) = 0 := by
      nlinarith [hdet]
    have g5 : (6 : ℝ) * (v 3 * (v 4) ^ 3) + (12 : ℝ) * (v 2 * (v 4) ^ 3) + (-8 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (-16 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 1) ^ 2 * v 3 * v 4) + (4 : ℝ) * ((v 1) ^ 2 * v 2 * v 4) = 0 := by
      nlinarith [hfold]
    have g6 : (-2 : ℝ) * (v 3 * h 0) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + (-4 : ℝ) * (v 2 * h 0) + (-4 : ℝ) * (v 2 * (v 4) ^ 2) + (4 : ℝ) * (v 1 * v 3 * v 4) + (8 : ℝ) * (v 1 * v 2 * v 4) + (-2 : ℝ) * ((v 1) ^ 2 * v 3) + (-4 : ℝ) * ((v 1) ^ 2 * v 2) = 0 := by
      nlinarith [hc0]
    have g7 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + v 1 * h 1 + (-2 : ℝ) * (v 1 * (v 4) ^ 2) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork47, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (2 : ℝ) * (v 3 * (v 4) ^ 2 * h 1) + (-4 : ℝ) * (v 3 * (v 4) ^ 2 * h 0) + (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 3 * v 4 * h 0) + (-4 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (4 : ℝ) * (v 1 * v 2 * v 4 * h 0) = 0 := by
      linear_combination
        (((5 : ℝ) / 2) * (v 4 * h 1) + ((-1 : ℝ) / 2) * (v 4 * h 0)) * g4 +
      (-(v 4) + ((-1 : ℝ) / 2) * (v 1)) * g5 +
      (((-1 : ℝ) / 2) * (v 1 * v 4)) * g6 +
      ((3 : ℝ) * (v 3 * v 4) + (6 : ℝ) * (v 2 * v 4)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork47, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g5 : (2 : ℝ) * (v 3 * v 4) + (4 : ℝ) * (v 2 * v 4) + (-2 : ℝ) * (v 1 * v 3) + (-4 : ℝ) * (v 1 * v 2) = 0 := by
      nlinarith [hdet]
    simp [-mul_eq_zero, cubicResidualNetwork47, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
        (-(v 4 * h 0) + v 1 * h 0) * g5
    nlinarith [hcertificate]

theorem cubicResidualNetwork47_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork47.toNetwork := by
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
  simp [cubicResidualNetwork47, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork47_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork47.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork47_jacobianNonzero
    cubicResidualNetwork47_fourCharts

def cubicResidualNetwork48 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .zero), (.y, .xx), (.xx, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork48_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork48.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork48, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + (-2 : ℝ) * (v 3) + (2 : ℝ) * (v 2) + v 0 = 0 := by
      nlinarith [heq0]
    have g1 : v 4 + -(v 2) + -(v 1) = 0 := by
      nlinarith [heq1]
    have g2 : (-4 : ℝ) * (v 3 * v 4) + -(v 2 * v 4) + (4 : ℝ) * (v 2 * v 3) + v 1 * v 4 + (4 : ℝ) * (v 1 * v 3) = 0 := by
      nlinarith [hdet]
    have g3 : (-12 : ℝ) * (v 3 * (v 4) ^ 3) + (-32 : ℝ) * ((v 3) ^ 2 * (v 4) ^ 2) + (32 : ℝ) * (v 2 * v 3 * (v 4) ^ 2) + (64 : ℝ) * (v 2 * (v 3) ^ 2 * v 4) + (-16 : ℝ) * ((v 2) ^ 2 * v 3 * v 4) = 0 := by
      nlinarith [hfold]
    have g4 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (-4 : ℝ) * (v 3 * h 0) + (4 : ℝ) * (v 3 * (v 4) ^ 2) + (2 : ℝ) * (v 2 * h 1) + (-4 : ℝ) * (v 2 * (v 4) ^ 2) + (-16 : ℝ) * ((v 2) ^ 2 * v 3) = 0 := by
      nlinarith [hc0]
    have g5 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + (-8 : ℝ) * (v 3 * (v 4) ^ 2) + -(v 2 * h 1) + (4 : ℝ) * (v 2 * (v 4) ^ 2) + (16 : ℝ) * (v 2 * v 3 * v 4) + -(v 1 * h 1) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork48, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * (v 3 * (v 4) ^ 2 * h 1) + (8 : ℝ) * (v 3 * (v 4) ^ 2 * h 0) + (16 : ℝ) * ((v 3) ^ 2 * v 4 * h 0) + (8 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (-8 : ℝ) * (v 2 * v 3 * v 4 * h 0) = 0 := by
      linear_combination
        ((5 : ℝ) * ((v 4) ^ 2 * h 1) + (-9 : ℝ) * (v 2 * v 4 * h 1) + -(v 1 * v 2 * h 1) + -((v 1) ^ 2 * h 1)) * g0 +
      ((5 : ℝ) * ((v 4) ^ 2 * h 1) + (2 : ℝ) * (v 3 * v 4 * h 0) + (8 : ℝ) * ((v 3) ^ 2 * h 0) + (-14 : ℝ) * (v 2 * v 4 * h 1) + (-12 : ℝ) * (v 2 * v 3 * h 1) + (5 : ℝ) * (v 1 * v 4 * h 1) + (18 : ℝ) * (v 1 * v 3 * h 1) + (-2 : ℝ) * (v 1 * v 2 * h 1) + (-5 : ℝ) * (v 0 * v 4 * h 1) + (-16 : ℝ) * (v 0 * v 3 * h 1) + -(v 0 * v 1 * h 1)) * g1 +
      ((-2 : ℝ) * (v 3 * h 0) + (-4 : ℝ) * (v 2 * h 1) + (4 : ℝ) * (v 1 * h 1) + (-4 : ℝ) * (v 0 * h 1) + (-4 : ℝ) * (v 3 * (v 4) ^ 2) + (16 : ℝ) * (v 2 * v 3 * v 4) + (-16 : ℝ) * ((v 2) ^ 2 * v 3)) * g2 +
      (-(v 4) + v 2 + -(v 1)) * g3 +
      ((-4 : ℝ) * (v 2 * v 3) + (-4 : ℝ) * (v 1 * v 3)) * g4 +
      ((6 : ℝ) * (v 3 * v 4) + (-12 : ℝ) * (v 2 * v 3)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork48, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + (-4 : ℝ) * (v 3) = 0 := by
      nlinarith [hg0]
    have g1 : v 4 = 0 := by
      nlinarith [hg1]
    simp [-mul_eq_zero, cubicResidualNetwork48, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 3 * (v 4) ^ 2 * h 0) + v 2 * (v 4) ^ 2 * h 1 + -(v 2 * (v 4) ^ 2 * h 0) + (-16 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (-2 : ℝ) * ((v 2) ^ 2 * v 4 * h 1) + (8 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + (2 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (8 : ℝ) * (v 1 * v 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((-2 : ℝ) * ((v 2) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 2 * h 0)) * g0 +
      ((4 : ℝ) * (v 3 * v 4 * h 0) + v 2 * v 4 * h 1 + -(v 2 * v 4 * h 0) + (-16 : ℝ) * (v 2 * v 3 * h 0) + (-2 : ℝ) * ((v 2) ^ 2 * h 1) + (-2 : ℝ) * ((v 2) ^ 2 * h 0) + -(v 1 * v 4 * h 1) + v 1 * v 4 * h 0 + (2 : ℝ) * (v 1 * v 2 * h 1) + (-2 : ℝ) * (v 1 * v 2 * h 0)) * g1
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork48, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + (-4 : ℝ) * (v 3) = 0 := by
      nlinarith [hg0]
    have g1 : -(v 4) + (2 : ℝ) * (v 2) = 0 := by
      nlinarith [hg1]
    have g2 : -(v 4) + (-2 : ℝ) * (v 3) + (2 : ℝ) * (v 2) + v 0 = 0 := by
      nlinarith [heq0]
    have g3 : v 4 + -(v 2) + -(v 1) = 0 := by
      nlinarith [heq1]
    have g4 : (-4 : ℝ) * (v 3 * v 4) + -(v 2 * v 4) + (4 : ℝ) * (v 2 * v 3) + v 1 * v 4 + (4 : ℝ) * (v 1 * v 3) = 0 := by
      nlinarith [hdet]
    have g5 : (-12 : ℝ) * (v 3 * (v 4) ^ 3) + (16 : ℝ) * (v 2 * v 3 * (v 4) ^ 2) + (-4 : ℝ) * ((v 2) ^ 2 * v 3 * v 4) + (16 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (-8 : ℝ) * (v 1 * v 2 * v 3 * v 4) + (-4 : ℝ) * ((v 1) ^ 2 * v 3 * v 4) = 0 := by
      nlinarith [hfold]
    have g7 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + -(v 2 * h 1) + (2 : ℝ) * (v 2 * (v 4) ^ 2) + -(v 1 * h 1) + (2 : ℝ) * (v 1 * (v 4) ^ 2) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork48, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 3 * (v 4) ^ 2 * h 1) + (-8 : ℝ) * (v 3 * (v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (4 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (-4 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (4 : ℝ) * (v 1 * v 3 * v 4 * h 0) = 0 := by
      linear_combination
        (((-1 : ℝ) / 2) * ((v 4) ^ 2 * h 1) + (2 : ℝ) * ((v 4) ^ 2 * h 0) + (8 : ℝ) * ((v 3) ^ 2 * h 0) + (-4 : ℝ) * (v 2 * v 3 * h 0) + (2 : ℝ) * ((v 2) ^ 2 * h 1) + (4 : ℝ) * (v 1 * v 3 * h 1) + (12 : ℝ) * (v 1 * v 3 * h 0) + (-8 : ℝ) * (v 1 * v 2 * h 0) + (-4 : ℝ) * (v 0 * v 3 * h 0) + ((-5 : ℝ) / 2) * (v 0 * v 2 * h 1) + (6 : ℝ) * (v 0 * v 2 * h 0) + ((1 : ℝ) / 2) * (v 0 * v 1 * h 1) + (-6 : ℝ) * (v 0 * v 1 * h 0)) * g0 +
      (((1 : ℝ) / 2) * ((v 4) ^ 2 * h 1) + (-2 : ℝ) * ((v 4) ^ 2 * h 0) + (2 : ℝ) * (v 3 * v 4 * h 1) + (-8 : ℝ) * ((v 3) ^ 2 * h 1) + (8 : ℝ) * ((v 3) ^ 2 * h 0) + v 2 * v 4 * h 1 + (-4 : ℝ) * (v 2 * v 4 * h 0) + (4 : ℝ) * ((v 2) ^ 2 * h 1) + (8 : ℝ) * ((v 2) ^ 2 * h 0) + (8 : ℝ) * (v 1 * v 3 * h 0) + (8 : ℝ) * (v 1 * v 2 * h 0) + (-6 : ℝ) * (v 0 * v 3 * h 1) + (12 : ℝ) * (v 0 * v 3 * h 0) + ((3 : ℝ) / 2) * (v 0 * v 2 * h 1) + (7 : ℝ) * (v 0 * v 2 * h 0) + ((-1 : ℝ) / 2) * (v 0 * v 1 * h 1) + (7 : ℝ) * (v 0 * v 1 * h 0)) * g1 +
      ((-4 : ℝ) * (v 3 * v 4 * h 1) + (-16 : ℝ) * ((v 3) ^ 2 * h 0) + (-4 : ℝ) * ((v 2) ^ 2 * h 1) + (-24 : ℝ) * (v 1 * v 3 * h 0)) * g2 +
      ((-16 : ℝ) * ((v 3) ^ 2 * h 1) + (16 : ℝ) * ((v 2) ^ 2 * h 0) + (-10 : ℝ) * (v 0 * v 3 * h 1) + (14 : ℝ) * (v 0 * v 2 * h 0) + -(v 0 * v 1 * h 1)) * g3 +
      ((2 : ℝ) * (v 0 * (v 4) ^ 2) + (-2 : ℝ) * (v 0 * v 2 * v 4) + (-2 : ℝ) * (v 0 * v 1 * v 4)) * g4 +
      ((-2 : ℝ) * (v 0)) * g5 +
      ((8 : ℝ) * (v 0 * v 3) + -(v 0 * v 2) + v 0 * v 1) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork48, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + (-4 : ℝ) * (v 3) = 0 := by
      nlinarith [hg0]
    have g1 : -(v 4) + (2 : ℝ) * (v 2) = 0 := by
      nlinarith [hg1]
    have g2 : v 4 = 0 := by
      nlinarith [hg2]
    have g4 : v 4 + -(v 2) + -(v 1) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork48, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * (v 3 * (v 4) ^ 2 * h 0) + -(v 2 * (v 4) ^ 2 * h 1) + v 2 * (v 4) ^ 2 * h 0 + (8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (v 2) ^ 2 * v 4 * h 1 + (-4 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + (8 : ℝ) * (v 1 * v 3 * v 4 * h 0) + (-8 : ℝ) * (v 1 * v 2 * v 3 * h 0) + -((v 1) ^ 2 * v 4 * h 1) + (-4 : ℝ) * ((v 1) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((v 2) ^ 2 * h 0) * g0 +
      ((-2 : ℝ) * (v 1 * v 3 * h 0)) * g1 +
      ((-4 : ℝ) * (v 3 * v 4 * h 0) + -(v 2 * v 4 * h 1) + v 2 * v 4 * h 0 + (8 : ℝ) * (v 2 * v 3 * h 0) + (v 2) ^ 2 * h 1 + (v 2) ^ 2 * h 0 + v 1 * v 4 * h 1 + -(v 1 * v 4 * h 0) + (2 : ℝ) * (v 1 * v 3 * h 0) + -((v 1) ^ 2 * h 1)) * g2 +
      ((4 : ℝ) * (v 1 * v 3 * h 0)) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork48_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork48.toNetwork := by
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
  simp [cubicResidualNetwork48, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork48_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork48.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork48_jacobianNonzero
    cubicResidualNetwork48_fourCharts

def cubicResidualNetwork49 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .zero), (.y, .xy), (.xx, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork49_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork49.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork49, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g2 : (-4 : ℝ) * (v 3 * v 4) + -(v 2 * v 4) + v 1 * v 4 + (4 : ℝ) * (v 1 * v 3) = 0 := by
      nlinarith [hdet]
    have g3 : (-12 : ℝ) * (v 3 * (v 4) ^ 3) + (-32 : ℝ) * ((v 3) ^ 2 * (v 4) ^ 2) + (16 : ℝ) * (v 2 * v 3 * (v 4) ^ 2) + (32 : ℝ) * (v 2 * (v 3) ^ 2 * v 4) + (-4 : ℝ) * ((v 2) ^ 2 * v 3 * v 4) = 0 := by
      nlinarith [hfold]
    have g4 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (-4 : ℝ) * (v 3 * h 0) + (4 : ℝ) * (v 3 * (v 4) ^ 2) + v 2 * h 1 + (-2 : ℝ) * (v 2 * (v 4) ^ 2) + (-4 : ℝ) * ((v 2) ^ 2 * v 3) = 0 := by
      nlinarith [hc0]
    have g5 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + (-8 : ℝ) * (v 3 * (v 4) ^ 2) + (2 : ℝ) * (v 2 * (v 4) ^ 2) + (8 : ℝ) * (v 2 * v 3 * v 4) + -(v 1 * h 1) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork49, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * (v 3 * (v 4) ^ 2 * h 1) + (8 : ℝ) * (v 3 * (v 4) ^ 2 * h 0) + (16 : ℝ) * ((v 3) ^ 2 * v 4 * h 0) + (4 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (-4 : ℝ) * (v 2 * v 3 * v 4 * h 0) = 0 := by
      linear_combination
        ((-10 : ℝ) * (v 3 * v 4 * h 1) + (2 : ℝ) * (v 3 * v 4 * h 0) + (-32 : ℝ) * ((v 3) ^ 2 * h 1) + (8 : ℝ) * ((v 3) ^ 2 * h 0) + (2 : ℝ) * (v 2 * v 3 * h 1)) * g1 +
      ((-8 : ℝ) * (v 3 * h 1) + (2 : ℝ) * (v 3 * h 0)) * g2 +
      (-(v 4)) * g3 +
      ((-4 : ℝ) * (v 3 * v 4)) * g4 +
      ((2 : ℝ) * (v 3 * v 4) + (-2 : ℝ) * (v 2 * v 3)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork49, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + (-4 : ℝ) * (v 3) = 0 := by
      nlinarith [hg0]
    have g1 : v 4 = 0 := by
      nlinarith [hg1]
    simp [-mul_eq_zero, cubicResidualNetwork49, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 3 * (v 4) ^ 2 * h 0) + v 2 * (v 4) ^ 2 * h 1 + -(v 2 * (v 4) ^ 2 * h 0) + (-8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + -((v 2) ^ 2 * v 4 * h 1) + -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + v 1 * v 2 * v 4 * h 1 + (4 : ℝ) * (v 1 * v 2 * v 3 * h 0) = 0 := by
      linear_combination
        (-(v 1 * v 2 * h 0)) * g0 +
      ((4 : ℝ) * (v 3 * v 4 * h 0) + v 2 * v 4 * h 1 + -(v 2 * v 4 * h 0) + (-8 : ℝ) * (v 2 * v 3 * h 0) + -((v 2) ^ 2 * h 1) + -(v 1 * v 4 * h 1) + v 1 * v 4 * h 0 + v 1 * v 2 * h 1 + -(v 1 * v 2 * h 0)) * g1
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork49, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + (-4 : ℝ) * (v 3) = 0 := by
      nlinarith [hg0]
    have g1 : -(v 4) + v 2 = 0 := by
      nlinarith [hg1]
    have g3 : v 4 + -(v 1) = 0 := by
      nlinarith [heq1]
    have g5 : (-12 : ℝ) * (v 3 * (v 4) ^ 3) + (16 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (-4 : ℝ) * ((v 1) ^ 2 * v 3 * v 4) = 0 := by
      nlinarith [hfold]
    have g7 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + -(v 1 * h 1) + (2 : ℝ) * (v 1 * (v 4) ^ 2) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork49, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 3 * (v 4) ^ 2 * h 1) + (-8 : ℝ) * (v 3 * (v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (4 : ℝ) * (v 1 * v 3 * v 4 * h 0) = 0 := by
      linear_combination
        (((-5 : ℝ) / 2) * ((v 2) ^ 2 * h 1) + ((5 : ℝ) / 2) * ((v 1) ^ 2 * h 1)) * g0 +
      ((-10 : ℝ) * (v 3 * v 4 * h 1) + ((-5 : ℝ) / 2) * (v 2 * v 4 * h 1) + (-10 : ℝ) * (v 2 * v 3 * h 1) + ((-5 : ℝ) / 2) * ((v 1) ^ 2 * h 1)) * g1 +
      ((-2 : ℝ) * (v 3 * v 4 * h 0) + ((-5 : ℝ) / 2) * (v 2 * v 4 * h 1) + (-12 : ℝ) * (v 1 * v 3 * h 1) + ((-5 : ℝ) / 2) * (v 1 * v 2 * h 1)) * g3 +
      (v 4) * g5 +
      ((-6 : ℝ) * (v 3 * v 4) + (2 : ℝ) * (v 1 * v 3)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork49, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork49, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * (v 3 * (v 4) ^ 2 * h 0) + -(v 2 * (v 4) ^ 2 * h 1) + v 2 * (v 4) ^ 2 * h 0 + v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + (8 : ℝ) * (v 1 * v 3 * v 4 * h 0) + v 1 * v 2 * v 4 * h 1 + -((v 1) ^ 2 * v 4 * h 1) + (-4 : ℝ) * ((v 1) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 3 * v 4 * h 0) + -(v 2 * v 4 * h 1) + v 2 * v 4 * h 0 + v 1 * v 4 * h 1 + -(v 1 * v 4 * h 0) + (4 : ℝ) * (v 1 * v 3 * h 0) + v 1 * v 2 * h 1 + -((v 1) ^ 2 * h 1)) * g2 +
      ((4 : ℝ) * (v 1 * v 3 * h 0)) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork49_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork49.toNetwork := by
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
  simp [cubicResidualNetwork49, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork49_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork49.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork49_jacobianNonzero
    cubicResidualNetwork49_fourCharts

def cubicResidualNetwork50 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .zero), (.y, .yy), (.xx, .zero), (.xy, .x)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork50_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork50.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork50, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g4 : (-4 : ℝ) * (v 3 * h 0) = 0 := by
      nlinarith [hc0]
    simp [-mul_eq_zero, cubicResidualNetwork50, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-16 : ℝ) * ((v 3) ^ 2 * v 4 * h 0) = 0 := by
      linear_combination
        ((4 : ℝ) * (v 3 * v 4)) * g4
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork50, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork50, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork50, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g4 : (4 : ℝ) * (v 3 * v 4) + (-4 : ℝ) * (v 2 * v 3) + (4 : ℝ) * (v 1 * v 3) = 0 := by
      nlinarith [hdet]
    have g5 : (12 : ℝ) * (v 3 * (v 4) ^ 3) + (-16 : ℝ) * (v 2 * v 3 * (v 4) ^ 2) + (4 : ℝ) * ((v 2) ^ 2 * v 3 * v 4) + (16 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (-8 : ℝ) * (v 1 * v 2 * v 3 * v 4) + (4 : ℝ) * ((v 1) ^ 2 * v 3 * v 4) = 0 := by
      nlinarith [hfold]
    have g6 : (-4 : ℝ) * (v 3 * h 0) + (-4 : ℝ) * (v 3 * (v 4) ^ 2) + (8 : ℝ) * (v 2 * v 3 * v 4) + (-4 : ℝ) * ((v 2) ^ 2 * v 3) + (-8 : ℝ) * (v 1 * v 3 * v 4) + (8 : ℝ) * (v 1 * v 2 * v 3) + (-4 : ℝ) * ((v 1) ^ 2 * v 3) = 0 := by
      nlinarith [hc0]
    have g7 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + v 2 * h 1 + (-2 : ℝ) * (v 2 * (v 4) ^ 2) + -(v 1 * h 1) + (2 : ℝ) * (v 1 * (v 4) ^ 2) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork50, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 3 * (v 4) ^ 2 * h 1) + (-8 : ℝ) * (v 3 * (v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (4 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (4 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 3 * v 4 * h 0) = 0 := by
      linear_combination
        (v 4 * h 1 + ((-1 : ℝ) / 2) * (v 4 * h 0) + ((-1 : ℝ) / 2) * (v 2 * h 1) + ((1 : ℝ) / 2) * (v 1 * h 1)) * g4 +
      (((1 : ℝ) / 2) * (v 4)) * g5 +
      (((3 : ℝ) / 2) * ((v 4) ^ 2)) * g6 +
      ((-2 : ℝ) * (v 2 * v 3) + (2 : ℝ) * (v 1 * v 3)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork50, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g5 : (4 : ℝ) * (v 3 * v 4) + (-4 : ℝ) * (v 2 * v 3) + (4 : ℝ) * (v 1 * v 3) = 0 := by
      nlinarith [hdet]
    simp [-mul_eq_zero, cubicResidualNetwork50, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * (v 3 * (v 4) ^ 2 * h 0) + (8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (-4 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + (-8 : ℝ) * (v 1 * v 3 * v 4 * h 0) + (8 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (-4 : ℝ) * ((v 1) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        (-(v 4 * h 0) + v 2 * h 0 + -(v 1 * h 0)) * g5
    nlinarith [hcertificate]

theorem cubicResidualNetwork50_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork50.toNetwork := by
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
  simp [cubicResidualNetwork50, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork50_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork50.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork50_jacobianNonzero
    cubicResidualNetwork50_fourCharts

def cubicResidualNetwork51 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .zero), (.y, .yy), (.xx, .zero), (.xy, .y)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork51_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork51.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork51, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork51, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork51, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork51, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 2 * (v 4) ^ 2 * h 1 + -(v 2 * (v 4) ^ 2 * h 0) + -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 = 0 := by
      linear_combination
        ((v 4) ^ 2 * h 1 + -((v 4) ^ 2 * h 0)) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork51, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork51, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork51, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + (-4 : ℝ) * (v 3) = 0 := by
      nlinarith [hg0]
    have g1 : -(v 4) = 0 := by
      nlinarith [hg1]
    have g7 : -(v 4 * h 1) + -(v 4 * h 0) + (-4 : ℝ) * (v 3 * h 0) + (-4 : ℝ) * ((v 2) ^ 2 * v 3) + (8 : ℝ) * (v 1 * v 2 * v 3) + (-4 : ℝ) * ((v 1) ^ 2 * v 3) = 0 := by
      nlinarith [hc0]
    have g8 : v 2 * h 1 + -(v 1 * h 1) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork51, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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

theorem cubicResidualNetwork51_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork51.toNetwork := by
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
  simp [cubicResidualNetwork51, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork51_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork51.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork51_jacobianNonzero
    cubicResidualNetwork51_fourCharts

def cubicResidualNetwork52 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .x), (.y, .yy), (.xx, .zero), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork52_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork52.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork52, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + (-2 : ℝ) * (v 3) + v 1 + v 0 = 0 := by
      nlinarith [heq0]
    have g1 : -(v 4) + v 2 + -(v 1) = 0 := by
      nlinarith [heq1]
    have g2 : (4 : ℝ) * (v 3 * v 4) + -(v 2 * v 4) + (-4 : ℝ) * (v 2 * v 3) + (2 : ℝ) * (v 1 * v 4) + (4 : ℝ) * (v 1 * v 3) = 0 := by
      nlinarith [hdet]
    have g3 : (12 : ℝ) * (v 3 * (v 4) ^ 3) + (32 : ℝ) * ((v 3) ^ 2 * (v 4) ^ 2) + (-16 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (-32 : ℝ) * (v 1 * (v 3) ^ 2 * v 4) + (4 : ℝ) * ((v 1) ^ 2 * v 3 * v 4) = 0 := by
      nlinarith [hfold]
    have g5 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (8 : ℝ) * (v 3 * (v 4) ^ 2) + v 2 * h 1 + -(v 1 * h 1) + (-2 : ℝ) * (v 1 * (v 4) ^ 2) + (-8 : ℝ) * (v 1 * v 3 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork52, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 3 * (v 4) ^ 2 * h 1) + (-8 : ℝ) * (v 3 * (v 4) ^ 2 * h 0) + (-16 : ℝ) * ((v 3) ^ 2 * v 4 * h 0) + (-4 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (4 : ℝ) * (v 1 * v 3 * v 4 * h 0) = 0 := by
      linear_combination
        ((-2 : ℝ) * ((v 2) ^ 2 * h 1) + (6 : ℝ) * (v 1 * v 2 * h 1) + (-4 : ℝ) * ((v 1) ^ 2 * h 1)) * g0 +
      ((-4 : ℝ) * (v 3 * v 4 * h 1) + (8 : ℝ) * (v 3 * v 4 * h 0) + (-16 : ℝ) * ((v 3) ^ 2 * h 1) + (24 : ℝ) * ((v 3) ^ 2 * h 0) + (2 : ℝ) * (v 2 * v 3 * h 1) + (-8 : ℝ) * (v 1 * v 3 * h 1) + (-2 : ℝ) * (v 1 * v 3 * h 0) + ((3 : ℝ) / 2) * (v 1 * v 2 * h 1) + (-3 : ℝ) * ((v 1) ^ 2 * h 1) + (-8 : ℝ) * (v 0 * v 3 * h 1) + (2 : ℝ) * (v 0 * v 2 * h 1) + (-4 : ℝ) * (v 0 * v 1 * h 1)) * g1 +
      ((6 : ℝ) * (v 3 * h 0) + (2 : ℝ) * (v 2 * h 1) + (-4 : ℝ) * (v 1 * h 1) + ((-1 : ℝ) / 2) * (v 1 * h 0) + (-2 : ℝ) * (v 0 * h 1) + (4 : ℝ) * (v 3 * (v 4) ^ 2) + v 1 * (v 4) ^ 2 + (-4 : ℝ) * (v 1 * v 3 * v 4) + -((v 1) ^ 2 * v 4)) * g2 +
      ((-4 : ℝ) * (v 3) + -(v 1)) * g3 +
      ((16 : ℝ) * ((v 3) ^ 2) + (2 : ℝ) * (v 2 * v 3) + ((1 : ℝ) / 2) * (v 1 * v 2) + -((v 1) ^ 2)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork52, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + (-4 : ℝ) * (v 3) = 0 := by
      nlinarith [hg0]
    have g1 : -(v 4) = 0 := by
      nlinarith [hg1]
    simp [-mul_eq_zero, cubicResidualNetwork52, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * (v 3 * (v 4) ^ 2 * h 0) + v 2 * (v 4) ^ 2 * h 1 + -(v 2 * (v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * (v 4) ^ 2 * h 1) + (2 : ℝ) * (v 1 * (v 4) ^ 2 * h 0) + (8 : ℝ) * (v 1 * v 3 * v 4 * h 0) + -(v 1 * v 2 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (2 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (4 : ℝ) * ((v 1) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        (v 1 * v 2 * h 0 + -((v 1) ^ 2 * h 0)) * g0 +
      ((4 : ℝ) * (v 3 * v 4 * h 0) + -(v 2 * v 4 * h 1) + v 2 * v 4 * h 0 + (2 : ℝ) * (v 1 * v 4 * h 1) + (-2 : ℝ) * (v 1 * v 4 * h 0) + (-8 : ℝ) * (v 1 * v 3 * h 0) + v 1 * v 2 * h 1 + -(v 1 * v 2 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * h 1) + (v 1) ^ 2 * h 0) * g1
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork52, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + (-4 : ℝ) * (v 3) = 0 := by
      nlinarith [hg0]
    have g1 : -(v 4) + v 1 = 0 := by
      nlinarith [hg1]
    have g3 : -(v 4) + v 2 + -(v 1) = 0 := by
      nlinarith [heq1]
    have g4 : (4 : ℝ) * (v 3 * v 4) + -(v 2 * v 4) + (-4 : ℝ) * (v 2 * v 3) + (2 : ℝ) * (v 1 * v 4) + (4 : ℝ) * (v 1 * v 3) = 0 := by
      nlinarith [hdet]
    have g5 : (12 : ℝ) * (v 3 * (v 4) ^ 3) + (-16 : ℝ) * (v 2 * v 3 * (v 4) ^ 2) + (4 : ℝ) * ((v 2) ^ 2 * v 3 * v 4) + (16 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (-8 : ℝ) * (v 1 * v 2 * v 3 * v 4) + (4 : ℝ) * ((v 1) ^ 2 * v 3 * v 4) = 0 := by
      nlinarith [hfold]
    have g6 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (-4 : ℝ) * (v 3 * h 0) + (-4 : ℝ) * (v 3 * (v 4) ^ 2) + (-2 : ℝ) * (v 2 * (v 4) ^ 2) + (8 : ℝ) * (v 2 * v 3 * v 4) + (-4 : ℝ) * ((v 2) ^ 2 * v 3) + v 1 * h 1 + (2 : ℝ) * (v 1 * (v 4) ^ 2) + (-8 : ℝ) * (v 1 * v 3 * v 4) + (8 : ℝ) * (v 1 * v 2 * v 3) + (-4 : ℝ) * ((v 1) ^ 2 * v 3) = 0 := by
      nlinarith [hc0]
    have g7 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + v 2 * h 1 + (-2 : ℝ) * (v 2 * (v 4) ^ 2) + -(v 1 * h 1) + (2 : ℝ) * (v 1 * (v 4) ^ 2) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork52, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 3 * (v 4) ^ 2 * h 1) + (-8 : ℝ) * (v 3 * (v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (4 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (4 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 3 * v 4 * h 0) = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 3 * v 4 * h 0) + ((1 : ℝ) / 2) * (v 2 * v 4 * h 1) + ((-1 : ℝ) / 2) * (v 2 * v 4 * h 0) + ((-1 : ℝ) / 2) * ((v 2) ^ 2 * h 1) + ((1 : ℝ) / 2) * (v 1 * v 2 * h 1) + (v 1) ^ 2 * h 0) * g0 +
      (((1 : ℝ) / 2) * ((v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 3 * v 4 * h 1) + ((-1 : ℝ) / 2) * (v 2 * v 4 * h 1) + ((1 : ℝ) / 2) * ((v 2) ^ 2 * h 1) + v 1 * v 4 * h 0 + (4 : ℝ) * (v 1 * v 3 * h 0) + ((-1 : ℝ) / 2) * (v 1 * v 2 * h 1)) * g1 +
      (((-1 : ℝ) / 2) * ((v 4) ^ 2 * h 0) + (-12 : ℝ) * (v 3 * v 4 * h 1) + ((-1 : ℝ) / 2) * (v 1 * v 2 * h 1)) * g3 +
      ((4 : ℝ) * (v 3 * (v 4) ^ 2) + (-4 : ℝ) * (v 2 * v 3 * v 4) + (4 : ℝ) * (v 1 * v 3 * v 4)) * g4 +
      ((-2 : ℝ) * (v 4)) * g5 +
      ((4 : ℝ) * (v 3 * v 4)) * g6 +
      ((8 : ℝ) * (v 3 * v 4) + (-2 : ℝ) * (v 2 * v 3)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork52, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + (-4 : ℝ) * (v 3) = 0 := by
      nlinarith [hg0]
    have g1 : -(v 4) + v 1 = 0 := by
      nlinarith [hg1]
    have g2 : -(v 4) = 0 := by
      nlinarith [hg2]
    simp [-mul_eq_zero, cubicResidualNetwork52, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * (v 3 * (v 4) ^ 2 * h 0) + v 2 * (v 4) ^ 2 * h 1 + -(v 2 * (v 4) ^ 2 * h 0) + (8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + -((v 2) ^ 2 * v 4 * h 1) + (-4 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + (-2 : ℝ) * (v 1 * (v 4) ^ 2 * h 1) + (2 : ℝ) * (v 1 * (v 4) ^ 2 * h 0) + (-8 : ℝ) * (v 1 * v 3 * v 4 * h 0) + (3 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (8 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (-4 : ℝ) * ((v 1) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((v 2) ^ 2 * h 0 + (-2 : ℝ) * (v 1 * v 2 * h 0)) * g0 +
      ((-4 : ℝ) * (v 1 * v 3 * h 0)) * g1 +
      ((4 : ℝ) * (v 3 * v 4 * h 0) + -(v 2 * v 4 * h 1) + v 2 * v 4 * h 0 + (-8 : ℝ) * (v 2 * v 3 * h 0) + (v 2) ^ 2 * h 1 + -((v 2) ^ 2 * h 0) + (2 : ℝ) * (v 1 * v 4 * h 1) + (-2 : ℝ) * (v 1 * v 4 * h 0) + (12 : ℝ) * (v 1 * v 3 * h 0) + (-3 : ℝ) * (v 1 * v 2 * h 1) + (2 : ℝ) * (v 1 * v 2 * h 0) + (2 : ℝ) * ((v 1) ^ 2 * h 1)) * g2
    nlinarith [hcertificate]

theorem cubicResidualNetwork52_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork52.toNetwork := by
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
  simp [cubicResidualNetwork52, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork52_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork52.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork52_jacobianNonzero
    cubicResidualNetwork52_fourCharts

def cubicResidualNetwork53 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .x), (.y, .yy), (.xx, .zero), (.xy, .y)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork53_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork53.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork53, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork53, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork53, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + (-4 : ℝ) * (v 3) = 0 := by
      nlinarith [hg0]
    have g3 : v 2 + -(v 1) = 0 := by
      nlinarith [heq1]
    have g7 : v 2 * h 1 + -(v 1 * h 1) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork53, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 2 * (v 4) ^ 2 * h 1 + -(v 2 * (v 4) ^ 2 * h 0) + -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + -(v 1 * v 2 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (v 1) ^ 2 * v 4 * h 1 + (4 : ℝ) * ((v 1) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        (v 2 * v 4 * h 0 + (v 2) ^ 2 * h 0 + -(v 1 * v 4 * h 0) + v 1 * v 2 * h 1 + -((v 1) ^ 2 * h 1) + -((v 1) ^ 2 * h 0)) * g0 +
      ((4 : ℝ) * (v 3 * v 4 * h 0) + v 2 * v 4 * h 0 + (4 : ℝ) * (v 2 * v 3 * h 0) + v 1 * v 4 * h 0) * g3 +
      ((v 4) ^ 2 + (4 : ℝ) * (v 1 * v 3)) * g7
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork53, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork53, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork53, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + (-4 : ℝ) * (v 3) = 0 := by
      nlinarith [hg0]
    have g1 : -(v 4) + v 1 = 0 := by
      nlinarith [hg1]
    have g7 : -(v 4 * h 1) + -(v 4 * h 0) + (-4 : ℝ) * (v 3 * h 0) + (-4 : ℝ) * ((v 2) ^ 2 * v 3) + v 1 * h 1 + (8 : ℝ) * (v 1 * v 2 * v 3) + (-4 : ℝ) * ((v 1) ^ 2 * v 3) = 0 := by
      nlinarith [hc0]
    have g8 : v 2 * h 1 + -(v 1 * h 1) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork53, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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

theorem cubicResidualNetwork53_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork53.toNetwork := by
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
  simp [cubicResidualNetwork53, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork53_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork53.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork53_jacobianNonzero
    cubicResidualNetwork53_fourCharts

def cubicResidualNetwork54 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .x), (.xx, .zero), (.xy, .xx), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork54_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork54.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork54, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g2 : (-4 : ℝ) * (v 2 * v 4) + (4 : ℝ) * (v 2 * v 3) + (4 : ℝ) * (v 1 * v 2) = 0 := by
      nlinarith [hdet]
    have g3 : (-12 : ℝ) * (v 2 * (v 4) ^ 3) + (36 : ℝ) * (v 2 * v 3 * (v 4) ^ 2) + (-36 : ℝ) * (v 2 * (v 3) ^ 2 * v 4) + (12 : ℝ) * (v 2 * (v 3) ^ 3) + (-32 : ℝ) * ((v 2) ^ 2 * (v 4) ^ 2) + (64 : ℝ) * ((v 2) ^ 2 * v 3 * v 4) + (-32 : ℝ) * ((v 2) ^ 2 * (v 3) ^ 2) + (16 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (-32 : ℝ) * (v 1 * v 2 * v 3 * v 4) + (16 : ℝ) * (v 1 * v 2 * (v 3) ^ 2) + (32 : ℝ) * (v 1 * (v 2) ^ 2 * v 4) + (-32 : ℝ) * (v 1 * (v 2) ^ 2 * v 3) + (-4 : ℝ) * ((v 1) ^ 2 * v 2 * v 4) + (4 : ℝ) * ((v 1) ^ 2 * v 2 * v 3) = 0 := by
      nlinarith [hfold]
    have g4 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + v 3 * h 1 + v 3 * h 0 + (-6 : ℝ) * (v 3 * (v 4) ^ 2) + (6 : ℝ) * ((v 3) ^ 2 * v 4) + (-2 : ℝ) * ((v 3) ^ 3) + (-4 : ℝ) * (v 2 * h 0) + (4 : ℝ) * (v 2 * (v 4) ^ 2) + (-8 : ℝ) * (v 2 * v 3 * v 4) + (4 : ℝ) * (v 2 * (v 3) ^ 2) + v 1 * h 1 + (-2 : ℝ) * (v 1 * (v 4) ^ 2) + (4 : ℝ) * (v 1 * v 3 * v 4) + (-2 : ℝ) * (v 1 * (v 3) ^ 2) + (-4 : ℝ) * ((v 1) ^ 2 * v 2) = 0 := by
      nlinarith [hc0]
    have g5 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + -(v 3 * h 1) + -(v 3 * h 0) + (6 : ℝ) * (v 3 * (v 4) ^ 2) + (-6 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + (-8 : ℝ) * (v 2 * (v 4) ^ 2) + (16 : ℝ) * (v 2 * v 3 * v 4) + (-8 : ℝ) * (v 2 * (v 3) ^ 2) + -(v 1 * h 1) + (2 : ℝ) * (v 1 * (v 4) ^ 2) + (-4 : ℝ) * (v 1 * v 3 * v 4) + (2 : ℝ) * (v 1 * (v 3) ^ 2) + (8 : ℝ) * (v 1 * v 2 * v 4) + (-8 : ℝ) * (v 1 * v 2 * v 3) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork54, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (8 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (-16 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (-4 : ℝ) * (v 2 * (v 3) ^ 2 * h 1) + (8 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + (16 : ℝ) * ((v 2) ^ 2 * v 4 * h 0) + (-16 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + (4 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (-4 : ℝ) * (v 1 * v 2 * v 3 * h 1) + (4 : ℝ) * (v 1 * v 2 * v 3 * h 0) = 0 := by
      linear_combination
        (((5 : ℝ) / 2) * (v 4 * h 1) + ((-1 : ℝ) / 2) * (v 4 * h 0) + -(v 3 * h 1) + ((1 : ℝ) / 2) * (v 3 * h 0) + (4 : ℝ) * (v 2 * h 1) + ((-1 : ℝ) / 2) * (v 1 * h 1)) * g2 +
      (-(v 4) + ((-1 : ℝ) / 2) * (v 3) + (-4 : ℝ) * (v 2)) * g3 +
      (((3 : ℝ) / 2) * (v 3 * v 4) + ((-3 : ℝ) / 2) * ((v 3) ^ 2)) * g4 +
      (((3 : ℝ) / 2) * (v 3 * v 4) + ((-3 : ℝ) / 2) * ((v 3) ^ 2) + (6 : ℝ) * (v 2 * v 4) + (16 : ℝ) * ((v 2) ^ 2) + (-2 : ℝ) * (v 1 * v 2)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork54, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g4 : (-4 : ℝ) * (v 2 * v 4) + (4 : ℝ) * (v 2 * v 3) + (4 : ℝ) * (v 1 * v 2) = 0 := by
      nlinarith [hdet]
    simp [-mul_eq_zero, cubicResidualNetwork54, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (4 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (8 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (4 : ℝ) * ((v 1) ^ 2 * v 2 * h 0) = 0 := by
      linear_combination
        (-(v 4 * h 0) + v 3 * h 0 + v 1 * h 0) * g4
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork54, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g4 : (-4 : ℝ) * (v 2 * v 4) + (4 : ℝ) * (v 2 * v 3) + (4 : ℝ) * (v 1 * v 2) = 0 := by
      nlinarith [hdet]
    have g5 : (-12 : ℝ) * (v 2 * (v 4) ^ 3) + (36 : ℝ) * (v 2 * v 3 * (v 4) ^ 2) + (-36 : ℝ) * (v 2 * (v 3) ^ 2 * v 4) + (12 : ℝ) * (v 2 * (v 3) ^ 3) + (16 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (-32 : ℝ) * (v 1 * v 2 * v 3 * v 4) + (16 : ℝ) * (v 1 * v 2 * (v 3) ^ 2) + (-4 : ℝ) * ((v 1) ^ 2 * v 2 * v 4) + (4 : ℝ) * ((v 1) ^ 2 * v 2 * v 3) = 0 := by
      nlinarith [hfold]
    have g7 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + -(v 3 * h 1) + -(v 3 * h 0) + (6 : ℝ) * (v 3 * (v 4) ^ 2) + (-6 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + -(v 1 * h 1) + (2 : ℝ) * (v 1 * (v 4) ^ 2) + (-4 : ℝ) * (v 1 * v 3 * v 4) + (2 : ℝ) * (v 1 * (v 3) ^ 2) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork54, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-8 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (16 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (4 : ℝ) * (v 2 * (v 3) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + (-4 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (4 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (4 : ℝ) * (v 1 * v 2 * v 3 * h 1) + (-4 : ℝ) * (v 1 * v 2 * v 3 * h 0) = 0 := by
      linear_combination
        (((-5 : ℝ) / 2) * (v 4 * h 1) + ((1 : ℝ) / 2) * (v 4 * h 0) + ((5 : ℝ) / 2) * (v 3 * h 1) + ((-1 : ℝ) / 2) * (v 3 * h 0) + ((1 : ℝ) / 2) * (v 1 * h 1)) * g4 +
      (v 4 + -(v 3)) * g5 +
      ((-6 : ℝ) * (v 2 * v 4) + (6 : ℝ) * (v 2 * v 3) + (2 : ℝ) * (v 1 * v 2)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork54, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g5 : (-4 : ℝ) * (v 2 * v 4) + (4 : ℝ) * (v 2 * v 3) + (4 : ℝ) * (v 1 * v 2) = 0 := by
      nlinarith [hdet]
    simp [-mul_eq_zero, cubicResidualNetwork54, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (-4 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + (8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (-8 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (-4 : ℝ) * ((v 1) ^ 2 * v 2 * h 0) = 0 := by
      linear_combination
        (v 4 * h 0 + -(v 3 * h 0) + -(v 1 * h 0)) * g5
    nlinarith [hcertificate]

theorem cubicResidualNetwork54_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork54.toNetwork := by
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
  simp [cubicResidualNetwork54, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork54_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork54.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork54_jacobianNonzero
    cubicResidualNetwork54_fourCharts

def cubicResidualNetwork55 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .xx), (.y, .yy), (.xx, .zero), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork55_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork55.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork55, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + (-2 : ℝ) * (v 3) + (2 : ℝ) * (v 1) + v 0 = 0 := by
      nlinarith [heq0]
    have g1 : -(v 4) + v 2 + -(v 1) = 0 := by
      nlinarith [heq1]
    have g2 : (4 : ℝ) * (v 3 * v 4) + -(v 2 * v 4) + (-4 : ℝ) * (v 2 * v 3) + (3 : ℝ) * (v 1 * v 4) + (4 : ℝ) * (v 1 * v 3) = 0 := by
      nlinarith [hdet]
    have g3 : (12 : ℝ) * (v 3 * (v 4) ^ 3) + (32 : ℝ) * ((v 3) ^ 2 * (v 4) ^ 2) + (-32 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (-64 : ℝ) * (v 1 * (v 3) ^ 2 * v 4) + (16 : ℝ) * ((v 1) ^ 2 * v 3 * v 4) = 0 := by
      nlinarith [hfold]
    have g5 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (8 : ℝ) * (v 3 * (v 4) ^ 2) + v 2 * h 1 + -(v 1 * h 1) + (-4 : ℝ) * (v 1 * (v 4) ^ 2) + (-16 : ℝ) * (v 1 * v 3 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork55, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 3 * (v 4) ^ 2 * h 1) + (-8 : ℝ) * (v 3 * (v 4) ^ 2 * h 0) + (-16 : ℝ) * ((v 3) ^ 2 * v 4 * h 0) + (-8 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (8 : ℝ) * (v 1 * v 3 * v 4 * h 0) = 0 := by
      linear_combination
        ((-6 : ℝ) * ((v 4) ^ 2 * h 1) + ((16 : ℝ) / 3) * (v 3 * v 4 * h 0) + (4 : ℝ) * ((v 2) ^ 2 * h 1) + (-4 : ℝ) * (v 1 * v 2 * h 1)) * g0 +
      ((6 : ℝ) * ((v 4) ^ 2 * h 1) + (26 : ℝ) * (v 3 * v 4 * h 1) + ((-10 : ℝ) / 3) * (v 3 * v 4 * h 0) + ((-16 : ℝ) / 3) * ((v 3) ^ 2 * h 1) + (-8 : ℝ) * ((v 3) ^ 2 * h 0) + ((-20 : ℝ) / 3) * (v 2 * v 3 * h 1) + (-8 : ℝ) * (v 1 * v 2 * h 1) + (-6 : ℝ) * (v 0 * v 4 * h 1) + ((-40 : ℝ) / 3) * (v 0 * v 3 * h 1) + ((-8 : ℝ) / 3) * (v 0 * v 3 * h 0) + ((-14 : ℝ) / 3) * (v 0 * v 2 * h 1) + (2 : ℝ) * (v 0 * v 1 * h 1)) * g1 +
      ((6 : ℝ) * (v 4 * h 1) + (-2 : ℝ) * (v 3 * h 0) + (-4 : ℝ) * (v 2 * h 1) + (-2 : ℝ) * (v 0 * h 1) + ((-2 : ℝ) / 3) * (v 0 * h 0) + ((-8 : ℝ) / 3) * (v 3 * (v 4) ^ 2) + ((16 : ℝ) / 3) * (v 1 * v 3 * v 4) + ((4 : ℝ) / 3) * (v 0 * (v 4) ^ 2) + ((-8 : ℝ) / 3) * (v 0 * v 1 * v 4)) * g2 +
      (-(v 4) + ((-4 : ℝ) / 3) * (v 3) + ((-4 : ℝ) / 3) * (v 0)) * g3 +
      ((6 : ℝ) * (v 3 * v 4) + ((16 : ℝ) / 3) * ((v 3) ^ 2) + ((-4 : ℝ) / 3) * (v 2 * v 3) + ((16 : ℝ) / 3) * (v 0 * v 3) + ((2 : ℝ) / 3) * (v 0 * v 2) + (-2 : ℝ) * (v 0 * v 1)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork55, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + (-4 : ℝ) * (v 3) = 0 := by
      nlinarith [hg0]
    have g1 : -(v 4) = 0 := by
      nlinarith [hg1]
    simp [-mul_eq_zero, cubicResidualNetwork55, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * (v 3 * (v 4) ^ 2 * h 0) + v 2 * (v 4) ^ 2 * h 1 + -(v 2 * (v 4) ^ 2 * h 0) + (-3 : ℝ) * (v 1 * (v 4) ^ 2 * h 1) + (3 : ℝ) * (v 1 * (v 4) ^ 2 * h 0) + (16 : ℝ) * (v 1 * v 3 * v 4 * h 0) + (-2 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (6 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (8 : ℝ) * ((v 1) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((2 : ℝ) * (v 1 * v 2 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * h 0)) * g0 +
      ((4 : ℝ) * (v 3 * v 4 * h 0) + -(v 2 * v 4 * h 1) + v 2 * v 4 * h 0 + (3 : ℝ) * (v 1 * v 4 * h 1) + (-3 : ℝ) * (v 1 * v 4 * h 0) + (-16 : ℝ) * (v 1 * v 3 * h 0) + (2 : ℝ) * (v 1 * v 2 * h 1) + (-2 : ℝ) * (v 1 * v 2 * h 0) + (-6 : ℝ) * ((v 1) ^ 2 * h 1) + (2 : ℝ) * ((v 1) ^ 2 * h 0)) * g1
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork55, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + (-4 : ℝ) * (v 3) = 0 := by
      nlinarith [hg0]
    have g1 : -(v 4) + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [hg1]
    have g2 : -(v 4) + (-2 : ℝ) * (v 3) + (2 : ℝ) * (v 1) + v 0 = 0 := by
      nlinarith [heq0]
    have g3 : -(v 4) + v 2 + -(v 1) = 0 := by
      nlinarith [heq1]
    have g4 : (4 : ℝ) * (v 3 * v 4) + -(v 2 * v 4) + (-4 : ℝ) * (v 2 * v 3) + (3 : ℝ) * (v 1 * v 4) + (4 : ℝ) * (v 1 * v 3) = 0 := by
      nlinarith [hdet]
    have g5 : (12 : ℝ) * (v 3 * (v 4) ^ 3) + (-16 : ℝ) * (v 2 * v 3 * (v 4) ^ 2) + (4 : ℝ) * ((v 2) ^ 2 * v 3 * v 4) + (16 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (-8 : ℝ) * (v 1 * v 2 * v 3 * v 4) + (4 : ℝ) * ((v 1) ^ 2 * v 3 * v 4) = 0 := by
      nlinarith [hfold]
    have g6 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (-4 : ℝ) * (v 3 * h 0) + (-4 : ℝ) * (v 3 * (v 4) ^ 2) + (-2 : ℝ) * (v 2 * (v 4) ^ 2) + (8 : ℝ) * (v 2 * v 3 * v 4) + (-4 : ℝ) * ((v 2) ^ 2 * v 3) + (2 : ℝ) * (v 1 * h 1) + (2 : ℝ) * (v 1 * (v 4) ^ 2) + (-8 : ℝ) * (v 1 * v 3 * v 4) + (8 : ℝ) * (v 1 * v 2 * v 3) + (-4 : ℝ) * ((v 1) ^ 2 * v 3) = 0 := by
      nlinarith [hc0]
    have g7 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + v 2 * h 1 + (-2 : ℝ) * (v 2 * (v 4) ^ 2) + -(v 1 * h 1) + (2 : ℝ) * (v 1 * (v 4) ^ 2) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork55, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 3 * (v 4) ^ 2 * h 1) + (-8 : ℝ) * (v 3 * (v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (4 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (4 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 3 * v 4 * h 0) = 0 := by
      linear_combination
        (-(v 2 * v 4 * h 0) + ((17 : ℝ) / 7) * (v 1 * v 4 * h 0) + ((8 : ℝ) / 7) * ((v 1) ^ 2 * h 0) + ((-4 : ℝ) / 7) * (v 0 * v 4 * h 0)) * g0 +
      (((-8 : ℝ) / 7) * (v 3 * v 4 * h 1) + ((36 : ℝ) / 7) * (v 3 * v 4 * h 0) + v 2 * v 4 * h 0 + ((-1 : ℝ) / 7) * ((v 2) ^ 2 * h 0) + ((-17 : ℝ) / 7) * (v 1 * v 4 * h 0) + ((15 : ℝ) / 7) * (v 1 * v 2 * h 0) + ((2 : ℝ) / 7) * ((v 1) ^ 2 * h 0) + ((4 : ℝ) / 7) * (v 0 * v 4 * h 0) + ((8 : ℝ) / 7) * (v 0 * v 1 * h 0)) * g1 +
      (((-16 : ℝ) / 7) * (v 3 * v 4 * h 0) + ((-16 : ℝ) / 7) * ((v 1) ^ 2 * h 0)) * g2 +
      ((-8 : ℝ) * (v 3 * v 4 * h 1) + ((-1 : ℝ) / 7) * ((v 2) ^ 2 * h 1) + ((3 : ℝ) / 7) * (v 1 * v 2 * h 1) + ((2 : ℝ) / 7) * (v 1 * v 2 * h 0) + (-4 : ℝ) * ((v 1) ^ 2 * h 0)) * g3 +
      (((8 : ℝ) / 7) * (v 3 * (v 4) ^ 2) + ((2 : ℝ) / 7) * (v 2 * (v 4) ^ 2) + ((-8 : ℝ) / 7) * (v 2 * v 3 * v 4) + ((-2 : ℝ) / 7) * ((v 2) ^ 2 * v 4) + ((8 : ℝ) / 7) * (v 1 * v 3 * v 4) + ((2 : ℝ) / 7) * (v 1 * v 2 * v 4)) * g4 +
      (((-6 : ℝ) / 7) * (v 4) + ((-2 : ℝ) / 7) * (v 2)) * g5 +
      (((8 : ℝ) / 7) * (v 3 * v 4)) * g6 +
      ((4 : ℝ) * (v 3 * v 4) + ((1 : ℝ) / 7) * ((v 2) ^ 2) + ((-3 : ℝ) / 7) * (v 1 * v 2)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork55, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + (-4 : ℝ) * (v 3) = 0 := by
      nlinarith [hg0]
    have g1 : -(v 4) + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [hg1]
    have g2 : -(v 4) = 0 := by
      nlinarith [hg2]
    simp [-mul_eq_zero, cubicResidualNetwork55, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * (v 3 * (v 4) ^ 2 * h 0) + v 2 * (v 4) ^ 2 * h 1 + -(v 2 * (v 4) ^ 2 * h 0) + (8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + -((v 2) ^ 2 * v 4 * h 1) + (-4 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + (-3 : ℝ) * (v 1 * (v 4) ^ 2 * h 1) + (3 : ℝ) * (v 1 * (v 4) ^ 2 * h 0) + (-8 : ℝ) * (v 1 * v 3 * v 4 * h 0) + (4 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (8 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (-3 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (-4 : ℝ) * ((v 1) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((v 2) ^ 2 * h 0 + (-2 : ℝ) * (v 1 * v 2 * h 0)) * g0 +
      ((-2 : ℝ) * (v 1 * v 3 * h 0)) * g1 +
      ((4 : ℝ) * (v 3 * v 4 * h 0) + -(v 2 * v 4 * h 1) + v 2 * v 4 * h 0 + (-8 : ℝ) * (v 2 * v 3 * h 0) + (v 2) ^ 2 * h 1 + -((v 2) ^ 2 * h 0) + (3 : ℝ) * (v 1 * v 4 * h 1) + (-3 : ℝ) * (v 1 * v 4 * h 0) + (10 : ℝ) * (v 1 * v 3 * h 0) + (-4 : ℝ) * (v 1 * v 2 * h 1) + (2 : ℝ) * (v 1 * v 2 * h 0) + (3 : ℝ) * ((v 1) ^ 2 * h 1)) * g2
    nlinarith [hcertificate]

theorem cubicResidualNetwork55_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork55.toNetwork := by
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
  simp [cubicResidualNetwork55, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork55_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork55.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork55_jacobianNonzero
    cubicResidualNetwork55_fourCharts

end SmallCusp

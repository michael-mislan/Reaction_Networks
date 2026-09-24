import proofs.SmallCusp.Obstruction.CubicDegeneracy
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

def cubicResidualNetwork136 : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .xy), (.xx, .zero), (.xy, .xx), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork136_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork136.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork136, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork136, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (8 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (-16 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (-4 : ℝ) * (v 2 * (v 3) ^ 2 * h 1) + (8 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + (16 : ℝ) * ((v 2) ^ 2 * v 4 * h 0) + (-16 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + (4 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (-4 : ℝ) * (v 1 * v 2 * v 3 * h 1) + (4 : ℝ) * (v 1 * v 2 * v 3 * h 0) + v 0 * (v 4) ^ 2 * h 1 + -(v 0 * (v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (2 : ℝ) * (v 0 * v 3 * v 4 * h 0) + v 0 * (v 3) ^ 2 * h 1 + -(v 0 * (v 3) ^ 2 * h 0) + (-8 : ℝ) * (v 0 * v 2 * v 4 * h 0) + (8 : ℝ) * (v 0 * v 2 * v 3 * h 0) + -(v 0 * v 1 * v 4 * h 1) + v 0 * v 1 * v 3 * h 1 + (v 0) ^ 2 * v 4 * h 0 + -((v 0) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 2 * v 4 * h 1) + (8 : ℝ) * (v 2 * v 4 * h 0) + (4 : ℝ) * (v 2 * v 3 * h 1) + (-8 : ℝ) * (v 2 * v 3 * h 0) + (16 : ℝ) * ((v 2) ^ 2 * h 0) + (4 : ℝ) * (v 1 * v 2 * h 1) + (-4 : ℝ) * (v 1 * v 2 * h 0) + v 0 * v 4 * h 1 + -(v 0 * v 4 * h 0) + -(v 0 * v 3 * h 1) + v 0 * v 3 * h 0 + (-8 : ℝ) * (v 0 * v 2 * h 0) + -(v 0 * v 1 * h 1) + (v 0) ^ 2 * h 0) * g1
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork136, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork136, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (4 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 3 * v 4 * h 0) + v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (8 : ℝ) * (v 1 * v 2 * v 3 * h 0) + -((v 1) ^ 2 * v 4 * h 1) + (v 1) ^ 2 * v 3 * h 1 + v 0 * v 1 * v 4 * h 0 + -(v 0 * v 1 * v 3 * h 0) = 0 := by
      linear_combination
        ((4 : ℝ) * (v 2 * v 4 * h 0) + (-4 : ℝ) * (v 2 * v 3 * h 0) + -(v 1 * v 4 * h 0) + -(v 1 * v 3 * h 1) + (-8 : ℝ) * (v 1 * v 2 * h 0) + -((v 1) ^ 2 * h 1)) * g1 +
      (v 1 * v 4 * h 1 + v 1 * v 3 * h 0 + v 0 * v 1 * h 0) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork136, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork136, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork136, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork136, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
        (v 1 * v 3 * h 1 + -(v 1 * v 3 * h 0)) * g2 +
      ((-4 : ℝ) * (v 2 * v 4 * h 0) + (4 : ℝ) * (v 2 * v 3 * h 0) + -(v 1 * v 4 * h 1) + v 1 * v 4 * h 0) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork136_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork136.toNetwork := by
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
  simp [cubicResidualNetwork136, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork136_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork136.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork136_jacobianNonzero
    cubicResidualNetwork136_fourCharts

def cubicResidualNetwork137 : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xy, .zero), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork137_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork137.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork137, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : v 4 + -(v 3) + (-2 : ℝ) * (v 2) + v 0 = 0 := by
      nlinarith [heq0]
    have g1 : -(v 4) + -(v 3) + v 1 = 0 := by
      nlinarith [heq1]
    have g2 : (4 : ℝ) * (v 2 * v 4) + (4 : ℝ) * (v 2 * v 3) + v 1 * v 4 + -(v 1 * v 3) + (-4 : ℝ) * (v 1 * v 2) + -(v 0 * v 4) + -(v 0 * v 3) + v 0 * v 1 = 0 := by
      nlinarith [hdet]
    have g3 : (12 : ℝ) * (v 2 * (v 4) ^ 3) + (-12 : ℝ) * (v 2 * v 3 * (v 4) ^ 2) + (-12 : ℝ) * (v 2 * (v 3) ^ 2 * v 4) + (12 : ℝ) * (v 2 * (v 3) ^ 3) + (-32 : ℝ) * ((v 2) ^ 2 * (v 4) ^ 2) + (32 : ℝ) * ((v 2) ^ 2 * (v 3) ^ 2) + (-2 : ℝ) * (v 0 * (v 4) ^ 3) + (2 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (-2 : ℝ) * (v 0 * (v 3) ^ 3) + (16 : ℝ) * (v 0 * v 2 * (v 4) ^ 2) + (-16 : ℝ) * (v 0 * v 2 * (v 3) ^ 2) + (-2 : ℝ) * ((v 0) ^ 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 0) ^ 2 * (v 3) ^ 2) = 0 := by
      nlinarith [hfold]
    have g4 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + -(v 3 * h 1) + -(v 3 * h 0) + (6 : ℝ) * (v 3 * (v 4) ^ 2) + (-6 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + (-4 : ℝ) * (v 2 * h 0) + (4 : ℝ) * (v 2 * (v 4) ^ 2) + (-8 : ℝ) * (v 2 * v 3 * v 4) + (4 : ℝ) * (v 2 * (v 3) ^ 2) + v 0 * h 0 + (-2 : ℝ) * (v 0 * (v 4) ^ 2) + (4 : ℝ) * (v 0 * v 3 * v 4) + (-2 : ℝ) * (v 0 * (v 3) ^ 2) = 0 := by
      nlinarith [hc0]
    have g5 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + -(v 3 * h 1) + -(v 3 * h 0) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + (-2 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + (-8 : ℝ) * (v 2 * (v 4) ^ 2) + (8 : ℝ) * (v 2 * (v 3) ^ 2) + v 1 * h 1 + (2 : ℝ) * (v 0 * (v 4) ^ 2) + (-2 : ℝ) * (v 0 * (v 3) ^ 2) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork137, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (4 : ℝ) * (v 2 * (v 3) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + (-16 : ℝ) * ((v 2) ^ 2 * v 4 * h 0) + (-16 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + v 0 * (v 4) ^ 2 * h 1 + -(v 0 * (v 4) ^ 2 * h 0) + -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 + (8 : ℝ) * (v 0 * v 2 * v 4 * h 0) + (8 : ℝ) * (v 0 * v 2 * v 3 * h 0) + -((v 0) ^ 2 * v 4 * h 0) + -((v 0) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((4 : ℝ) * ((v 4) ^ 2 * h 1) + (4 : ℝ) * (v 3 * v 4 * h 1) + (-2 : ℝ) * ((v 1) ^ 2 * h 1)) * g0 +
      ((4 : ℝ) * ((v 4) ^ 2 * h 1) + (-4 : ℝ) * (v 3 * v 4 * h 1) + (-14 : ℝ) * (v 2 * v 4 * h 1) + (-2 : ℝ) * (v 2 * v 4 * h 0) + (-10 : ℝ) * (v 2 * v 3 * h 1) + (2 : ℝ) * (v 2 * v 3 * h 0) + (-16 : ℝ) * ((v 2) ^ 2 * h 1) + (8 : ℝ) * ((v 2) ^ 2 * h 0) + (4 : ℝ) * (v 1 * v 2 * h 1) + (6 : ℝ) * (v 0 * v 4 * h 1) + (2 : ℝ) * (v 0 * v 3 * h 1) + (4 : ℝ) * (v 0 * v 2 * h 1) + (-2 : ℝ) * (v 0 * v 2 * h 0)) * g1 +
      ((-4 : ℝ) * (v 4 * h 1) + (-4 : ℝ) * (v 2 * h 1) + (2 : ℝ) * (v 2 * h 0) + (2 : ℝ) * (v 1 * h 1)) * g2 +
      (v 4 + -(v 3)) * g3 +
      ((4 : ℝ) * (v 2 * v 4) + (4 : ℝ) * (v 2 * v 3) + -(v 0 * v 4) + -(v 0 * v 3)) * g4 +
      ((-2 : ℝ) * (v 2 * v 4) + (2 : ℝ) * (v 2 * v 3)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork137, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : -(v 4) + -(v 3) = 0 := by
      nlinarith [hg1]
    have g3 : -(v 4) + -(v 3) + v 1 = 0 := by
      nlinarith [heq1]
    have g4 : (4 : ℝ) * (v 2 * v 4) + (4 : ℝ) * (v 2 * v 3) + v 1 * v 4 + -(v 1 * v 3) + (-4 : ℝ) * (v 1 * v 2) + -(v 0 * v 4) + -(v 0 * v 3) + v 0 * v 1 = 0 := by
      nlinarith [hdet]
    simp [-mul_eq_zero, cubicResidualNetwork137, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 3 * v 4 * h 0) + v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + -(v 0 * v 1 * v 4 * h 0) + v 0 * v 1 * v 3 * h 0 = 0 := by
      linear_combination
        ((-4 : ℝ) * ((v 3) ^ 2 * h 1) + (-4 : ℝ) * (v 2 * v 4 * h 0) + (4 : ℝ) * (v 2 * v 3 * h 0) + -(v 1 * v 4 * h 1) + v 1 * v 4 * h 0 + (3 : ℝ) * (v 1 * v 3 * h 1) + -(v 1 * v 3 * h 0) + (-2 : ℝ) * (v 0 * v 3 * h 0) + v 0 * v 1 * h 0) * g1 +
      ((4 : ℝ) * ((v 3) ^ 2 * h 1) + (8 : ℝ) * (v 2 * v 3 * h 0)) * g3 +
      ((2 : ℝ) * (v 3 * h 0)) * g4
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork137, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : v 4 + -(v 3) + (-4 : ℝ) * (v 2) + v 0 = 0 := by
      nlinarith [hg0]
    have g1 : v 4 + -(v 3) = 0 := by
      nlinarith [hg1]
    have g3 : -(v 4) + -(v 3) + v 1 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork137, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (8 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (-16 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (4 : ℝ) * (v 2 * (v 3) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + (-4 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (4 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (-4 : ℝ) * (v 1 * v 2 * v 3 * h 1) + (4 : ℝ) * (v 1 * v 2 * v 3 * h 0) + -(v 0 * (v 4) ^ 2 * h 1) + v 0 * (v 4) ^ 2 * h 0 + (-2 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (2 : ℝ) * (v 0 * v 3 * v 4 * h 0) + -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 + v 0 * v 1 * v 4 * h 1 + v 0 * v 1 * v 3 * h 1 = 0 := by
      linear_combination
        ((v 1) ^ 2 * h 0) * g0 +
      ((-4 : ℝ) * (v 2 * v 4 * h 1) + (8 : ℝ) * (v 2 * v 4 * h 0) + (-4 : ℝ) * (v 2 * v 3 * h 1) + (8 : ℝ) * (v 2 * v 3 * h 0) + (4 : ℝ) * (v 1 * v 2 * h 1) + (-8 : ℝ) * (v 1 * v 2 * h 0) + -((v 1) ^ 2 * h 0) + -(v 0 * v 4 * h 1) + v 0 * v 4 * h 0 + -(v 0 * v 3 * h 1) + v 0 * v 3 * h 0 + v 0 * v 1 * h 1 + -(v 0 * v 1 * h 0)) * g1 +
      ((-8 : ℝ) * (v 2 * v 4 * h 1) + (16 : ℝ) * (v 2 * v 4 * h 0) + (4 : ℝ) * (v 1 * v 2 * h 0) + (2 : ℝ) * (v 0 * v 3 * h 1) + (-2 : ℝ) * (v 0 * v 3 * h 0) + -(v 0 * v 1 * h 0)) * g3
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork137, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g4 : -(v 4) + -(v 3) + v 1 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork137, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (-4 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + (8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (8 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (v 1) ^ 2 * v 4 * h 1 + -((v 1) ^ 2 * v 3 * h 1) + (-4 : ℝ) * ((v 1) ^ 2 * v 2 * h 0) = 0 := by
      linear_combination
        (-(v 1 * v 4 * h 1) + v 1 * v 4 * h 0 + -(v 1 * v 3 * h 1) + v 1 * v 3 * h 0 + (v 1) ^ 2 * h 1) * g1 +
      ((4 : ℝ) * (v 2 * v 4 * h 0) + (4 : ℝ) * (v 2 * v 3 * h 0) + (-4 : ℝ) * (v 1 * v 2 * h 0)) * g2 +
      ((-4 : ℝ) * (v 1 * v 2 * h 0)) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork137_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork137.toNetwork := by
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
  simp [cubicResidualNetwork137, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork137_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork137.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork137_jacobianNonzero
    cubicResidualNetwork137_fourCharts

def cubicResidualNetwork138 : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xy, .zero), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork138_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork138.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork138, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 3) + (-2 : ℝ) * (v 2) + v 0 = 0 := by
      nlinarith [heq0]
    have g1 : (-2 : ℝ) * (v 4) + -(v 3) + v 1 = 0 := by
      nlinarith [heq1]
    have g2 : (4 : ℝ) * (v 3 * v 4) + (16 : ℝ) * (v 2 * v 4) + (4 : ℝ) * (v 2 * v 3) + -(v 1 * v 3) + (-4 : ℝ) * (v 1 * v 2) + (-4 : ℝ) * (v 0 * v 4) + -(v 0 * v 3) + v 0 * v 1 = 0 := by
      nlinarith [hdet]
    have g4 : -(v 3 * h 1) + -(v 3 * h 0) + (2 : ℝ) * ((v 3) ^ 3) + (-4 : ℝ) * (v 2 * h 0) + (4 : ℝ) * (v 2 * (v 3) ^ 2) + v 0 * h 0 + (-2 : ℝ) * (v 0 * (v 3) ^ 2) = 0 := by
      nlinarith [hc0]
    simp [-mul_eq_zero, cubicResidualNetwork138, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * ((v 3) ^ 2 * v 4 * h 1) + (-32 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (4 : ℝ) * (v 2 * (v 3) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + (-64 : ℝ) * ((v 2) ^ 2 * v 4 * h 1) + (-16 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + (8 : ℝ) * (v 0 * v 3 * v 4 * h 1) + -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 + (32 : ℝ) * (v 0 * v 2 * v 4 * h 1) + (8 : ℝ) * (v 0 * v 2 * v 3 * h 0) + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) + -((v 0) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((-24 : ℝ) * ((v 4) ^ 2 * h 1) + (32 : ℝ) * (v 2 * v 4 * h 1) + (8 : ℝ) * (v 2 * v 3 * h 0) + (16 : ℝ) * (v 1 * v 4 * h 1) + (-2 : ℝ) * ((v 1) ^ 2 * h 1) + (-8 : ℝ) * (v 0 * v 4 * h 1) + (-2 : ℝ) * (v 0 * v 3 * h 0) + (-32 : ℝ) * ((v 4) ^ 4) + (40 : ℝ) * ((v 3) ^ 2 * (v 4) ^ 2) + (64 : ℝ) * ((v 2) ^ 2 * v 3 * v 4) + (16 : ℝ) * (v 1 * (v 4) ^ 3) + (2 : ℝ) * (v 1 * (v 3) ^ 3) + (40 : ℝ) * (v 1 * v 2 * v 3 * v 4) + (-4 : ℝ) * (v 1 * v 2 * (v 3) ^ 2) + (-8 : ℝ) * ((v 1) ^ 2 * v 2 * v 4) + (-8 : ℝ) * ((v 1) ^ 2 * v 2 * v 3) + (-2 : ℝ) * ((v 1) ^ 3 * v 3) + (4 : ℝ) * ((v 1) ^ 3 * v 2) + (80 : ℝ) * (v 0 * (v 4) ^ 3) + (-16 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (16 : ℝ) * (v 0 * v 2 * (v 4) ^ 2) + (4 : ℝ) * (v 0 * v 2 * (v 3) ^ 2) + (-112 : ℝ) * (v 0 * (v 2) ^ 2 * v 4) + (-56 : ℝ) * (v 0 * (v 2) ^ 2 * v 3) + (-40 : ℝ) * (v 0 * v 1 * (v 4) ^ 2) + (8 : ℝ) * (v 0 * v 1 * v 3 * v 4) + (-8 : ℝ) * (v 0 * v 1 * v 2 * v 4) + (-4 : ℝ) * (v 0 * v 1 * v 2 * v 3) + (56 : ℝ) * (v 0 * v 1 * (v 2) ^ 2) + (-4 : ℝ) * (v 0 * (v 1) ^ 2 * v 4) + (2 : ℝ) * (v 0 * (v 1) ^ 3)) * g0 +
      ((4 : ℝ) * (v 3 * v 4 * h 1) + (-8 : ℝ) * (v 2 * v 4 * h 1) + (-4 : ℝ) * (v 2 * v 3 * h 1) + (4 : ℝ) * (v 1 * v 2 * h 1) + (-4 : ℝ) * (v 0 * v 4 * h 1) + (-8 : ℝ) * (v 0 * v 2 * h 1) + (2 : ℝ) * ((v 0) ^ 2 * h 1) + (16 : ℝ) * (v 3 * (v 4) ^ 3) + (-40 : ℝ) * ((v 3) ^ 2 * (v 4) ^ 2) + (32 : ℝ) * (v 2 * (v 4) ^ 3) + (-144 : ℝ) * (v 2 * v 3 * (v 4) ^ 2) + (64 : ℝ) * ((v 2) ^ 3 * v 3) + (4 : ℝ) * (v 1 * (v 3) ^ 2 * v 4) + (-2 : ℝ) * (v 1 * (v 3) ^ 3) + (24 : ℝ) * (v 1 * v 2 * v 3 * v 4) + (24 : ℝ) * (v 1 * (v 2) ^ 2 * v 3) + (-2 : ℝ) * ((v 1) ^ 2 * (v 3) ^ 2) + (8 : ℝ) * ((v 1) ^ 2 * (v 2) ^ 2) + (-16 : ℝ) * (v 0 * (v 4) ^ 3) + (12 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (2 : ℝ) * (v 0 * (v 3) ^ 3) + (-80 : ℝ) * (v 0 * v 2 * (v 4) ^ 2) + (-32 : ℝ) * (v 0 * v 2 * v 3 * v 4) + (-16 : ℝ) * (v 0 * (v 2) ^ 2 * v 4) + (112 : ℝ) * (v 0 * (v 2) ^ 3) + (-4 : ℝ) * (v 0 * v 1 * v 3 * v 4) + (4 : ℝ) * (v 0 * v 1 * (v 3) ^ 2) + (4 : ℝ) * (v 0 * (v 1) ^ 2 * v 3) + (40 : ℝ) * ((v 0) ^ 2 * (v 4) ^ 2) + (-4 : ℝ) * ((v 0) ^ 2 * v 3 * v 4) + (-2 : ℝ) * ((v 0) ^ 2 * (v 3) ^ 2) + (8 : ℝ) * ((v 0) ^ 2 * v 2 * v 4) + (12 : ℝ) * ((v 0) ^ 2 * v 2 * v 3) + (-56 : ℝ) * ((v 0) ^ 2 * (v 2) ^ 2) + (-2 : ℝ) * ((v 0) ^ 2 * v 1 * v 3) + (-2 : ℝ) * ((v 0) ^ 2 * (v 1) ^ 2)) * g1 +
      ((-4 : ℝ) * (v 4 * h 1) + (2 : ℝ) * (v 1 * h 1) + (-2 : ℝ) * (v 0 * h 1) + (-16 : ℝ) * (v 3 * (v 4) ^ 2) + (16 : ℝ) * ((v 2) ^ 2 * v 3) + (8 : ℝ) * (v 1 * v 3 * v 4) + (8 : ℝ) * (v 1 * v 2 * v 3) + (-8 : ℝ) * (v 0 * v 3 * v 4) + (-8 : ℝ) * (v 0 * v 2 * v 3)) * g2 +
      (v 0 * v 3) * g4
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork138, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : -(v 3) = 0 := by
      nlinarith [hg1]
    simp [-mul_eq_zero, cubicResidualNetwork138, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-8 : ℝ) * ((v 3) ^ 2 * v 4 * h 1) + (4 : ℝ) * ((v 3) ^ 2 * v 4 * h 0) + (-16 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (-4 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + (4 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (-4 : ℝ) * (v 0 * v 3 * v 4 * h 0) + v 0 * v 1 * v 3 * h 0 = 0 := by
      linear_combination
        ((8 : ℝ) * (v 3 * v 4 * h 1) + (-4 : ℝ) * (v 3 * v 4 * h 0) + (16 : ℝ) * (v 2 * v 4 * h 1) + (4 : ℝ) * (v 2 * v 3 * h 0) + -(v 1 * v 3 * h 1) + v 1 * v 3 * h 0 + (-4 : ℝ) * (v 0 * v 4 * h 1) + (4 : ℝ) * (v 0 * v 4 * h 0) + -(v 0 * v 1 * h 0)) * g1
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork138, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : -(v 3) = 0 := by
      nlinarith [hg1]
    simp [-mul_eq_zero, cubicResidualNetwork138, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * ((v 3) ^ 2 * v 4 * h 1) + (-16 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (4 : ℝ) * (v 2 * (v 3) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + (-4 : ℝ) * (v 1 * v 2 * v 3 * h 1) + (4 : ℝ) * (v 1 * v 2 * v 3 * h 0) + -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 + v 0 * v 1 * v 3 * h 1 = 0 := by
      linear_combination
        ((4 : ℝ) * (v 3 * v 4 * h 1) + (16 : ℝ) * (v 2 * v 4 * h 0) + (-4 : ℝ) * (v 2 * v 3 * h 1) + (8 : ℝ) * (v 2 * v 3 * h 0) + (4 : ℝ) * (v 1 * v 2 * h 1) + (-4 : ℝ) * (v 1 * v 2 * h 0) + v 0 * v 3 * h 1 + -(v 0 * v 3 * h 0) + -(v 0 * v 1 * h 1)) * g1
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork138, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 3) + (-4 : ℝ) * (v 2) + v 0 = 0 := by
      nlinarith [hg0]
    have g1 : -(v 3) = 0 := by
      nlinarith [hg1]
    have g2 : -(v 3) = 0 := by
      nlinarith [hg2]
    have g3 : -(v 3) + (-2 : ℝ) * (v 2) + v 0 = 0 := by
      nlinarith [heq0]
    have g4 : (-2 : ℝ) * (v 4) + -(v 3) + v 1 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork138, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-16 : ℝ) * (v 3 * (v 4) ^ 2 * h 1) + (-8 : ℝ) * ((v 3) ^ 2 * v 4 * h 1) + (4 : ℝ) * ((v 3) ^ 2 * v 4 * h 0) + (-64 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-32 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (-4 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + (8 : ℝ) * (v 1 * v 3 * v 4 * h 1) + v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + (32 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (8 : ℝ) * (v 1 * v 2 * v 3 * h 0) + -((v 1) ^ 2 * v 3 * h 1) + (-4 : ℝ) * ((v 1) ^ 2 * v 2 * h 0) = 0 := by
      linear_combination
        ((4 : ℝ) * (v 1 * v 4 * h 0)) * g0 +
      ((16 : ℝ) * ((v 4) ^ 2 * h 1) + (-4 : ℝ) * (v 3 * v 4 * h 0) + v 1 * v 3 * h 0 + (v 1) ^ 2 * h 1) * g1 +
      ((8 : ℝ) * (v 3 * v 4 * h 1) + (4 : ℝ) * (v 2 * v 3 * h 0) + (-8 : ℝ) * (v 1 * v 4 * h 1) + -(v 1 * v 3 * h 1) + (-4 : ℝ) * (v 1 * v 2 * h 0)) * g2 +
      ((-4 : ℝ) * (v 1 * v 4 * h 0)) * g3 +
      ((32 : ℝ) * (v 2 * v 4 * h 0) + (-4 : ℝ) * (v 1 * v 2 * h 0)) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork138_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork138.toNetwork := by
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
  simp [cubicResidualNetwork138, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork138_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork138.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork138_jacobianNonzero
    cubicResidualNetwork138_fourCharts

def cubicResidualNetwork139 : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xy, .y), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork139_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork139.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork139, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : v 4 + -(v 3) + (-2 : ℝ) * (v 2) + v 0 = 0 := by
      nlinarith [heq0]
    have g1 : -(v 4) + v 1 = 0 := by
      nlinarith [heq1]
    have g2 : (4 : ℝ) * (v 2 * v 4) + v 1 * v 4 + -(v 1 * v 3) + (-4 : ℝ) * (v 1 * v 2) + -(v 0 * v 4) + v 0 * v 1 = 0 := by
      nlinarith [hdet]
    have g3 : (12 : ℝ) * (v 2 * (v 4) ^ 3) + (-24 : ℝ) * (v 2 * v 3 * (v 4) ^ 2) + (12 : ℝ) * (v 2 * (v 3) ^ 2 * v 4) + (-32 : ℝ) * ((v 2) ^ 2 * (v 4) ^ 2) + (32 : ℝ) * ((v 2) ^ 2 * v 3 * v 4) + (-2 : ℝ) * (v 0 * (v 4) ^ 3) + (4 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (-2 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (16 : ℝ) * (v 0 * v 2 * (v 4) ^ 2) + (-16 : ℝ) * (v 0 * v 2 * v 3 * v 4) + (-2 : ℝ) * ((v 0) ^ 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 0) ^ 2 * v 3 * v 4) = 0 := by
      nlinarith [hfold]
    have g4 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + -(v 3 * h 1) + -(v 3 * h 0) + (6 : ℝ) * (v 3 * (v 4) ^ 2) + (-6 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + (-4 : ℝ) * (v 2 * h 0) + (4 : ℝ) * (v 2 * (v 4) ^ 2) + (-8 : ℝ) * (v 2 * v 3 * v 4) + (4 : ℝ) * (v 2 * (v 3) ^ 2) + v 0 * h 0 + (-2 : ℝ) * (v 0 * (v 4) ^ 2) + (4 : ℝ) * (v 0 * v 3 * v 4) + (-2 : ℝ) * (v 0 * (v 3) ^ 2) = 0 := by
      nlinarith [hc0]
    have g5 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (-4 : ℝ) * (v 3 * (v 4) ^ 2) + (2 : ℝ) * ((v 3) ^ 2 * v 4) + (-8 : ℝ) * (v 2 * (v 4) ^ 2) + (8 : ℝ) * (v 2 * v 3 * v 4) + v 1 * h 1 + (2 : ℝ) * (v 0 * (v 4) ^ 2) + (-2 : ℝ) * (v 0 * v 3 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork139, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (4 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (-8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (-16 : ℝ) * ((v 2) ^ 2 * v 4 * h 0) + v 0 * (v 4) ^ 2 * h 1 + -(v 0 * (v 4) ^ 2 * h 0) + -(v 0 * v 3 * v 4 * h 1) + v 0 * v 3 * v 4 * h 0 + (8 : ℝ) * (v 0 * v 2 * v 4 * h 0) + -((v 0) ^ 2 * v 4 * h 0) = 0 := by
      linear_combination
        (v 3 * v 4 * h 0 + (-4 : ℝ) * (v 1 * v 3 * h 1) + (4 : ℝ) * ((v 1) ^ 2 * h 1) + -((v 1) ^ 2 * h 0)) * g0 +
      (v 3 * v 4 * h 0 + -((v 3) ^ 2 * h 0) + (-6 : ℝ) * (v 2 * v 4 * h 1) + (2 : ℝ) * (v 2 * v 4 * h 0) + (6 : ℝ) * (v 2 * v 3 * h 1) + (-4 : ℝ) * (v 2 * v 3 * h 0) + (-4 : ℝ) * (v 1 * v 4 * h 1) + v 1 * v 4 * h 0 + (4 : ℝ) * (v 1 * v 3 * h 1) + -(v 1 * v 3 * h 0) + (8 : ℝ) * (v 1 * v 2 * h 1) + (-2 : ℝ) * (v 1 * v 2 * h 0) + (2 : ℝ) * (v 0 * v 4 * h 1) + -(v 0 * v 4 * h 0) + (-2 : ℝ) * (v 0 * v 3 * h 1) + (2 : ℝ) * (v 0 * v 3 * h 0) + (-8 : ℝ) * (v 0 * v 2 * h 1) + (4 : ℝ) * (v 0 * v 2 * h 0) + (-4 : ℝ) * (v 0 * v 1 * h 1) + v 0 * v 1 * h 0 + (2 : ℝ) * ((v 0) ^ 2 * h 1) + -((v 0) ^ 2 * h 0)) * g1 +
      ((-3 : ℝ) * (v 4 * h 1) + v 4 * h 0 + ((7 : ℝ) / 2) * (v 3 * h 1) + -(v 3 * h 0) + (-2 : ℝ) * (v 0 * h 1) + v 0 * h 0) * g2 +
      (((-1 : ℝ) / 2) * (v 3)) * g3 +
      (-((v 4) ^ 2) + ((1 : ℝ) / 2) * (v 3 * v 4) + (4 : ℝ) * (v 2 * v 4) + -(v 0 * v 4)) * g4 +
      (-((v 4) ^ 2) + ((3 : ℝ) / 2) * (v 3 * v 4) + ((-1 : ℝ) / 2) * ((v 3) ^ 2) + (2 : ℝ) * (v 2 * v 4) + -(v 0 * v 4) + ((1 : ℝ) / 2) * (v 0 * v 3)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork139, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g3 : -(v 4) + v 1 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork139, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 2 * v 3 * v 4 * h 0) + v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 3 * v 4 * h 0) + v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + -(v 0 * v 1 * v 4 * h 0) + v 0 * v 1 * v 3 * h 0 = 0 := by
      linear_combination
        (-((v 3) ^ 2 * h 1) + (v 3) ^ 2 * h 0 + (-4 : ℝ) * (v 2 * v 4 * h 0) + (4 : ℝ) * (v 2 * v 3 * h 0) + -(v 1 * v 4 * h 1) + v 1 * v 4 * h 0 + (2 : ℝ) * (v 1 * v 3 * h 1) + (-2 : ℝ) * (v 1 * v 3 * h 0) + -(v 0 * v 3 * h 0) + v 0 * v 1 * h 0) * g1 +
      ((v 3) ^ 2 * h 1 + -((v 3) ^ 2 * h 0) + v 0 * v 3 * h 0) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork139, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : v 4 + -(v 3) + (-4 : ℝ) * (v 2) + v 0 = 0 := by
      nlinarith [hg0]
    have g1 : v 4 + -(v 3) = 0 := by
      nlinarith [hg1]
    have g3 : -(v 4) + v 1 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork139, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
        (v 1 * v 4 * h 0) * g0 +
      (-((v 4) ^ 2 * h 0) + (-8 : ℝ) * (v 2 * v 4 * h 0) + (8 : ℝ) * (v 1 * v 2 * h 0)) * g1 +
      (-((v 4) ^ 2 * h 0) + v 3 * v 4 * h 0 + (-4 : ℝ) * (v 2 * v 4 * h 1) + (8 : ℝ) * (v 2 * v 3 * h 0) + v 0 * v 4 * h 1 + -(v 0 * v 4 * h 0)) * g3
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork139, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g4 : -(v 4) + v 1 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork139, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
        ((4 : ℝ) * (v 2 * v 4 * h 0) + v 1 * v 4 * h 1 + -(v 1 * v 4 * h 0) + v 1 * v 3 * h 0 + (-4 : ℝ) * (v 1 * v 2 * h 0) + -((v 1) ^ 2 * h 1)) * g2 +
      (-(v 1 * v 3 * h 1) + (-4 : ℝ) * (v 1 * v 2 * h 0)) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork139_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork139.toNetwork := by
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
  simp [cubicResidualNetwork139, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork139_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork139.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork139_jacobianNonzero
    cubicResidualNetwork139_fourCharts

end SmallCusp

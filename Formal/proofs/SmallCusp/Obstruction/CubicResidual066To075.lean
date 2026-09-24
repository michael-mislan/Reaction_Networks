import proofs.SmallCusp.Obstruction.CubicDegeneracy
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

def cubicResidualNetwork66 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xx), (.y, .x), (.xx, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork66_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork66.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork66, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + (-2 : ℝ) * (v 3) + v 2 + v 1 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g1 : v 4 + -(v 2) = 0 := by
      nlinarith [heq1]
    have g2 : (-4 : ℝ) * (v 3 * v 4) + (4 : ℝ) * (v 2 * v 3) + v 1 * v 4 + -(v 1 * v 2) + -(v 0 * v 4) + v 0 * v 2 = 0 := by
      nlinarith [hdet]
    have g3 : (-12 : ℝ) * (v 3 * (v 4) ^ 3) + (-32 : ℝ) * ((v 3) ^ 2 * (v 4) ^ 2) + (16 : ℝ) * (v 2 * v 3 * (v 4) ^ 2) + (32 : ℝ) * (v 2 * (v 3) ^ 2 * v 4) + (-4 : ℝ) * ((v 2) ^ 2 * v 3 * v 4) + (2 : ℝ) * (v 1 * (v 4) ^ 3) + (16 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (-16 : ℝ) * (v 1 * v 2 * v 3 * v 4) + (-2 : ℝ) * ((v 1) ^ 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 1) ^ 2 * v 2 * v 4) + (-2 : ℝ) * (v 0 * (v 4) ^ 3) + (-16 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * v 2 * (v 4) ^ 2) + (16 : ℝ) * (v 0 * v 2 * v 3 * v 4) + (4 : ℝ) * (v 0 * v 1 * (v 4) ^ 2) + (-4 : ℝ) * (v 0 * v 1 * v 2 * v 4) + (-2 : ℝ) * ((v 0) ^ 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 0) ^ 2 * v 2 * v 4) = 0 := by
      nlinarith [hfold]
    have g5 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + (-8 : ℝ) * (v 3 * (v 4) ^ 2) + -(v 2 * h 1) + (2 : ℝ) * (v 2 * (v 4) ^ 2) + (8 : ℝ) * (v 2 * v 3 * v 4) + (2 : ℝ) * (v 1 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * v 2 * v 4) + (-2 : ℝ) * (v 0 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * v 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork66, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * (v 3 * (v 4) ^ 2 * h 1) + (8 : ℝ) * (v 3 * (v 4) ^ 2 * h 0) + (16 : ℝ) * ((v 3) ^ 2 * v 4 * h 0) + (4 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (-4 : ℝ) * (v 2 * v 3 * v 4 * h 0) + v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + (-8 : ℝ) * (v 1 * v 3 * v 4 * h 0) + -(v 1 * v 2 * v 4 * h 1) + (v 1) ^ 2 * v 4 * h 0 + -(v 0 * (v 4) ^ 2 * h 1) + v 0 * (v 4) ^ 2 * h 0 + (8 : ℝ) * (v 0 * v 3 * v 4 * h 0) + v 0 * v 2 * v 4 * h 1 + (-2 : ℝ) * (v 0 * v 1 * v 4 * h 0) + (v 0) ^ 2 * v 4 * h 0 = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 3 * v 4 * h 0) + v 1 * v 4 * h 0 + -(v 0 * v 4 * h 0)) * g0 +
      ((-10 : ℝ) * (v 3 * v 4 * h 1) + (-2 : ℝ) * (v 3 * v 4 * h 0) + (-8 : ℝ) * ((v 3) ^ 2 * h 1) + (2 : ℝ) * (v 2 * v 3 * h 1) + (2 : ℝ) * (v 1 * v 4 * h 1) + v 1 * v 4 * h 0 + (2 : ℝ) * (v 1 * v 3 * h 1) + (-2 : ℝ) * (v 0 * v 4 * h 1) + -(v 0 * v 4 * h 0) + (-2 : ℝ) * (v 0 * v 3 * h 1)) * g1 +
      ((-8 : ℝ) * (v 3 * (v 4) ^ 2) + (-16 : ℝ) * ((v 3) ^ 2 * v 4) + (4 : ℝ) * (v 2 * v 3 * v 4) + (4 : ℝ) * (v 1 * v 3 * v 4) + (-4 : ℝ) * (v 0 * v 3 * v 4)) * g2 +
      (-(v 4)) * g3 +
      ((6 : ℝ) * (v 3 * v 4) + (8 : ℝ) * ((v 3) ^ 2) + (-2 : ℝ) * (v 2 * v 3) + -(v 1 * v 4) + (-2 : ℝ) * (v 1 * v 3) + v 0 * v 4 + (2 : ℝ) * (v 0 * v 3)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork66, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + (-4 : ℝ) * (v 3) + v 1 + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : v 4 = 0 := by
      nlinarith [hg1]
    have g6 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (-4 : ℝ) * (v 3 * h 0) + (4 : ℝ) * (v 3 * (v 4) ^ 2) + v 2 * h 1 + (-2 : ℝ) * (v 2 * (v 4) ^ 2) + (-4 : ℝ) * ((v 2) ^ 2 * v 3) + v 1 * h 0 + (-2 : ℝ) * (v 1 * (v 4) ^ 2) + (2 : ℝ) * (v 1 * v 2 * v 4) + -(v 0 * h 0) + (2 : ℝ) * (v 0 * (v 4) ^ 2) + (-2 : ℝ) * (v 0 * v 2 * v 4) = 0 := by
      nlinarith [hc0]
    have g7 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + (-8 : ℝ) * (v 3 * (v 4) ^ 2) + -(v 2 * h 1) + (2 : ℝ) * (v 2 * (v 4) ^ 2) + (8 : ℝ) * (v 2 * v 3 * v 4) + (2 : ℝ) * (v 1 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * v 2 * v 4) + (-2 : ℝ) * (v 0 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * v 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork66, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork66, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g4 : (-4 : ℝ) * (v 3 * v 4) + (4 : ℝ) * (v 2 * v 3) + v 1 * v 4 + -(v 1 * v 2) + -(v 0 * v 4) + v 0 * v 2 = 0 := by
      nlinarith [hdet]
    have g7 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + -(v 2 * h 1) + (2 : ℝ) * (v 2 * (v 4) ^ 2) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork66, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 3 * (v 4) ^ 2 * h 1) + (-8 : ℝ) * (v 3 * (v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (4 : ℝ) * (v 2 * v 3 * v 4 * h 0) + -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + v 1 * v 2 * v 4 * h 1 + v 0 * (v 4) ^ 2 * h 1 + -(v 0 * (v 4) ^ 2 * h 0) + -(v 0 * v 2 * v 4 * h 1) = 0 := by
      linear_combination
        ((4 : ℝ) * (v 3 * v 4 * h 0) + (2 : ℝ) * (v 1 * v 4 * h 1) + (-2 : ℝ) * (v 0 * v 4 * h 1)) * g1 +
      ((8 : ℝ) * (v 3 * v 4 * h 1)) * g3 +
      ((2 : ℝ) * ((v 4) ^ 3)) * g4 +
      ((-4 : ℝ) * (v 3 * v 4) + v 1 * v 4 + -(v 0 * v 4)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork66, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + (-4 : ℝ) * (v 3) + v 1 + -(v 0) = 0 := by
      nlinarith [hg0]
    have g2 : v 4 = 0 := by
      nlinarith [hg2]
    have g7 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (-4 : ℝ) * (v 3 * h 0) + (-4 : ℝ) * (v 3 * (v 4) ^ 2) + v 2 * h 1 + (-2 : ℝ) * (v 2 * (v 4) ^ 2) + (8 : ℝ) * (v 2 * v 3 * v 4) + (-4 : ℝ) * ((v 2) ^ 2 * v 3) + v 1 * h 0 + -(v 0 * h 0) = 0 := by
      nlinarith [hc0]
    have g8 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + -(v 2 * h 1) + (2 : ℝ) * (v 2 * (v 4) ^ 2) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork66, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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

theorem cubicResidualNetwork66_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork66.toNetwork := by
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
  simp [cubicResidualNetwork66, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork66_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork66.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork66_jacobianNonzero
    cubicResidualNetwork66_fourCharts

def cubicResidualNetwork67 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xx), (.y, .yy), (.xx, .zero), (.xy, .x)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork67_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork67.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork67, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g2 : (4 : ℝ) * (v 3 * v 4) + (-4 : ℝ) * (v 2 * v 3) + -(v 1 * v 4) + v 1 * v 2 + v 0 * v 4 + -(v 0 * v 2) = 0 := by
      nlinarith [hdet]
    have g5 : -(v 4 * h 1) + -(v 4 * h 0) + v 2 * h 1 = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork67, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-16 : ℝ) * ((v 3) ^ 2 * v 4 * h 0) + (8 : ℝ) * (v 1 * v 3 * v 4 * h 0) + -((v 1) ^ 2 * v 4 * h 0) + (-8 : ℝ) * (v 0 * v 3 * v 4 * h 0) + (2 : ℝ) * (v 0 * v 1 * v 4 * h 0) + -((v 0) ^ 2 * v 4 * h 0) = 0 := by
      linear_combination
        ((4 : ℝ) * (v 3 * h 1) + -(v 1 * h 1) + v 0 * h 1) * g2 +
      ((16 : ℝ) * ((v 3) ^ 2) + (-8 : ℝ) * (v 1 * v 3) + (v 1) ^ 2 + (8 : ℝ) * (v 0 * v 3) + (-2 : ℝ) * (v 0 * v 1) + (v 0) ^ 2) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork67, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork67, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork67, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : (-4 : ℝ) * (v 3) + v 1 + -(v 0) = 0 := by
      nlinarith [hg0]
    have g3 : -(v 4) + v 2 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork67, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 3 * (v 4) ^ 2 * h 1) + (-8 : ℝ) * (v 3 * (v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (4 : ℝ) * (v 2 * v 3 * v 4 * h 0) + -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + v 1 * v 2 * v 4 * h 1 + v 0 * (v 4) ^ 2 * h 1 + -(v 0 * (v 4) ^ 2 * h 0) + -(v 0 * v 2 * v 4 * h 1) = 0 := by
      linear_combination
        ((v 2) ^ 2 * h 0) * g0 +
      ((-4 : ℝ) * (v 3 * v 4 * h 1) + (8 : ℝ) * (v 3 * v 4 * h 0) + (4 : ℝ) * (v 2 * v 3 * h 0) + v 1 * v 4 * h 1 + -(v 1 * v 4 * h 0) + -(v 1 * v 2 * h 0) + -(v 0 * v 4 * h 1) + v 0 * v 4 * h 0 + v 0 * v 2 * h 0) * g3
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork67, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : (-4 : ℝ) * (v 3) + v 1 + -(v 0) = 0 := by
      nlinarith [hg0]
    have g7 : (-4 : ℝ) * (v 3 * h 0) + (-4 : ℝ) * (v 3 * (v 4) ^ 2) + (8 : ℝ) * (v 2 * v 3 * v 4) + (-4 : ℝ) * ((v 2) ^ 2 * v 3) + v 1 * h 0 + -(v 0 * h 0) = 0 := by
      nlinarith [hc0]
    simp [-mul_eq_zero, cubicResidualNetwork67, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
      (h 0) * g7
    nlinarith [hcertificate]

theorem cubicResidualNetwork67_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork67.toNetwork := by
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
  simp [cubicResidualNetwork67, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork67_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork67.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork67_jacobianNonzero
    cubicResidualNetwork67_fourCharts

def cubicResidualNetwork68 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xx), (.y, .x), (.xx, .xy), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork68_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork68.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork68, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g3 : (-2 : ℝ) * (v 1 * (v 4) ^ 3) + (2 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * (v 2) ^ 2 * v 3) + (-2 : ℝ) * ((v 1) ^ 2 * (v 4) ^ 2) + (-2 : ℝ) * ((v 1) ^ 2 * v 2 * v 4) + (2 : ℝ) * (v 0 * (v 4) ^ 3) + (-2 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * v 2 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * (v 2) ^ 2 * v 3) + (4 : ℝ) * (v 0 * v 1 * (v 4) ^ 2) + (4 : ℝ) * (v 0 * v 1 * v 2 * v 4) + (-2 : ℝ) * ((v 0) ^ 2 * (v 4) ^ 2) + (-2 : ℝ) * ((v 0) ^ 2 * v 2 * v 4) = 0 := by
      nlinarith [hfold]
    have g4 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + (-2 : ℝ) * (v 3 * h 0) + (2 : ℝ) * (v 3 * (v 4) ^ 2) + v 2 * h 1 + (-2 : ℝ) * (v 2 * (v 4) ^ 2) + (-2 : ℝ) * ((v 2) ^ 2 * v 3) + v 1 * h 0 + (-2 : ℝ) * (v 1 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * v 2 * v 4) + -(v 0 * h 0) + (2 : ℝ) * (v 0 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * v 2 * v 4) = 0 := by
      nlinarith [hc0]
    have g5 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (2 : ℝ) * (v 3 * h 0) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + -(v 2 * h 1) + (2 : ℝ) * (v 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 2) ^ 2 * v 3) + (2 : ℝ) * (v 1 * (v 4) ^ 2) + (2 : ℝ) * (v 1 * v 2 * v 4) + (-2 : ℝ) * (v 0 * (v 4) ^ 2) + (-2 : ℝ) * (v 0 * v 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork68, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + v 1 * v 2 * v 4 * h 1 + (-2 : ℝ) * (v 1 * v 2 * v 3 * h 0) + -((v 1) ^ 2 * v 4 * h 0) + -(v 0 * (v 4) ^ 2 * h 1) + v 0 * (v 4) ^ 2 * h 0 + -(v 0 * v 2 * v 4 * h 1) + (2 : ℝ) * (v 0 * v 2 * v 3 * h 0) + (2 : ℝ) * (v 0 * v 1 * v 4 * h 0) + -((v 0) ^ 2 * v 4 * h 0) = 0 := by
      linear_combination
        (-(v 4 * h 1) + v 4 * h 0 + (2 : ℝ) * (v 3 * h 1) + (2 : ℝ) * (v 3 * h 0) + -(v 2 * h 0) + -(v 1 * h 1) + v 0 * h 1) * g2 +
      ((-2 : ℝ) * (v 3) + v 1 + -(v 0)) * g3 +
      ((4 : ℝ) * ((v 3) ^ 2) + -((v 2) ^ 2) + (-2 : ℝ) * (v 1 * v 3) + (2 : ℝ) * (v 0 * v 3)) * g4 +
      ((4 : ℝ) * ((v 3) ^ 2) + -((v 2) ^ 2) + (-4 : ℝ) * (v 1 * v 3) + (v 1) ^ 2 + (4 : ℝ) * (v 0 * v 3) + (-2 : ℝ) * (v 0 * v 1) + (v 0) ^ 2) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork68, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork68, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork68, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g5 : (-2 : ℝ) * (v 1 * (v 4) ^ 3) + (2 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * (v 2) ^ 2 * v 3) + (2 : ℝ) * (v 0 * (v 4) ^ 3) + (-2 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * v 2 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * (v 2) ^ 2 * v 3) = 0 := by
      nlinarith [hfold]
    have g6 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + (-2 : ℝ) * (v 3 * h 0) + (2 : ℝ) * (v 3 * (v 4) ^ 2) + v 2 * h 1 + (-2 : ℝ) * (v 2 * (v 4) ^ 2) + (-2 : ℝ) * ((v 2) ^ 2 * v 3) + v 1 * h 0 + -(v 0 * h 0) = 0 := by
      nlinarith [hc0]
    have g7 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (2 : ℝ) * (v 3 * h 0) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + -(v 2 * h 1) + (2 : ℝ) * (v 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 2) ^ 2 * v 3) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork68, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + -(v 1 * v 2 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 2 * v 3 * h 0) + v 0 * (v 4) ^ 2 * h 1 + -(v 0 * (v 4) ^ 2 * h 0) + v 0 * v 2 * v 4 * h 1 + (-2 : ℝ) * (v 0 * v 2 * v 3 * h 0) = 0 := by
      linear_combination
        (v 4 * h 1 + -(v 4 * h 0) + (-2 : ℝ) * (v 3 * h 1) + (-2 : ℝ) * (v 3 * h 0) + v 2 * h 0) * g4 +
      ((2 : ℝ) * (v 3)) * g5 +
      ((-4 : ℝ) * ((v 3) ^ 2) + (v 2) ^ 2) * g6 +
      ((-4 : ℝ) * ((v 3) ^ 2) + (v 2) ^ 2 + (2 : ℝ) * (v 1 * v 3) + (-2 : ℝ) * (v 0 * v 3)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork68, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork68, CodedBimolNetwork.toNetwork,
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

theorem cubicResidualNetwork68_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork68.toNetwork := by
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
  simp [cubicResidualNetwork68, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork68_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork68.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork68_jacobianNonzero
    cubicResidualNetwork68_fourCharts

def cubicResidualNetwork69 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xx), (.y, .x), (.xx, .xy), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork69_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork69.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork69, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g3 : (2 : ℝ) * (v 1 * (v 4) ^ 3) + (2 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * (v 2) ^ 2 * v 3) + (-2 : ℝ) * ((v 1) ^ 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 1) ^ 2 * v 2 * v 4) + (-2 : ℝ) * (v 0 * (v 4) ^ 3) + (-2 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * v 2 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * (v 2) ^ 2 * v 3) + (4 : ℝ) * (v 0 * v 1 * (v 4) ^ 2) + (-4 : ℝ) * (v 0 * v 1 * v 2 * v 4) + (-2 : ℝ) * ((v 0) ^ 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 0) ^ 2 * v 2 * v 4) = 0 := by
      nlinarith [hfold]
    have g4 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (-2 : ℝ) * (v 3 * h 0) + (2 : ℝ) * (v 3 * (v 4) ^ 2) + v 2 * h 1 + (-2 : ℝ) * (v 2 * (v 4) ^ 2) + (-2 : ℝ) * ((v 2) ^ 2 * v 3) + v 1 * h 0 + (-2 : ℝ) * (v 1 * (v 4) ^ 2) + (2 : ℝ) * (v 1 * v 2 * v 4) + -(v 0 * h 0) + (2 : ℝ) * (v 0 * (v 4) ^ 2) + (-2 : ℝ) * (v 0 * v 2 * v 4) = 0 := by
      nlinarith [hc0]
    have g5 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + (2 : ℝ) * (v 3 * h 0) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + -(v 2 * h 1) + (2 : ℝ) * (v 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 2) ^ 2 * v 3) + (2 : ℝ) * (v 1 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * v 2 * v 4) + (-2 : ℝ) * (v 0 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * v 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork69, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + -(v 1 * v 2 * v 4 * h 1) + (-2 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (v 1) ^ 2 * v 4 * h 0 + -(v 0 * (v 4) ^ 2 * h 1) + v 0 * (v 4) ^ 2 * h 0 + v 0 * v 2 * v 4 * h 1 + (2 : ℝ) * (v 0 * v 2 * v 3 * h 0) + (-2 : ℝ) * (v 0 * v 1 * v 4 * h 0) + (v 0) ^ 2 * v 4 * h 0 = 0 := by
      linear_combination
        (v 4 * h 1 + -(v 4 * h 0) + (2 : ℝ) * (v 3 * h 1) + (2 : ℝ) * (v 3 * h 0) + -(v 2 * h 0) + -(v 1 * h 1) + v 0 * h 1) * g2 +
      ((-2 : ℝ) * (v 3) + v 1 + -(v 0)) * g3 +
      ((4 : ℝ) * ((v 3) ^ 2) + -((v 2) ^ 2) + (-2 : ℝ) * (v 1 * v 3) + (2 : ℝ) * (v 0 * v 3)) * g4 +
      ((4 : ℝ) * ((v 3) ^ 2) + -((v 2) ^ 2) + (-4 : ℝ) * (v 1 * v 3) + (v 1) ^ 2 + (4 : ℝ) * (v 0 * v 3) + (-2 : ℝ) * (v 0 * v 1) + (v 0) ^ 2) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork69, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork69, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork69, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g5 : (2 : ℝ) * (v 1 * (v 4) ^ 3) + (2 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * (v 2) ^ 2 * v 3) + (-2 : ℝ) * (v 0 * (v 4) ^ 3) + (-2 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * v 2 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * (v 2) ^ 2 * v 3) = 0 := by
      nlinarith [hfold]
    have g6 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (-2 : ℝ) * (v 3 * h 0) + (2 : ℝ) * (v 3 * (v 4) ^ 2) + v 2 * h 1 + (-2 : ℝ) * (v 2 * (v 4) ^ 2) + (-2 : ℝ) * ((v 2) ^ 2 * v 3) + v 1 * h 0 + -(v 0 * h 0) = 0 := by
      nlinarith [hc0]
    have g7 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + (2 : ℝ) * (v 3 * h 0) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + -(v 2 * h 1) + (2 : ℝ) * (v 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 2) ^ 2 * v 3) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork69, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + v 1 * v 2 * v 4 * h 1 + (2 : ℝ) * (v 1 * v 2 * v 3 * h 0) + v 0 * (v 4) ^ 2 * h 1 + -(v 0 * (v 4) ^ 2 * h 0) + -(v 0 * v 2 * v 4 * h 1) + (-2 : ℝ) * (v 0 * v 2 * v 3 * h 0) = 0 := by
      linear_combination
        (-(v 4 * h 1) + v 4 * h 0 + (-2 : ℝ) * (v 3 * h 1) + (-2 : ℝ) * (v 3 * h 0) + v 2 * h 0) * g4 +
      ((2 : ℝ) * (v 3)) * g5 +
      ((-4 : ℝ) * ((v 3) ^ 2) + (v 2) ^ 2) * g6 +
      ((-4 : ℝ) * ((v 3) ^ 2) + (v 2) ^ 2 + (2 : ℝ) * (v 1 * v 3) + (-2 : ℝ) * (v 0 * v 3)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork69, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork69, CodedBimolNetwork.toNetwork,
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

theorem cubicResidualNetwork69_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork69.toNetwork := by
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
  simp [cubicResidualNetwork69, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork69_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork69.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork69_jacobianNonzero
    cubicResidualNetwork69_fourCharts

def cubicResidualNetwork70 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xx), (.y, .x), (.xx, .xy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork70_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork70.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork70, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) = 0 := by
      nlinarith [heq1]
    have g2 : (-4 : ℝ) * (v 1 * v 4) + -(v 1 * v 2) + (4 : ℝ) * (v 0 * v 4) + v 0 * v 2 = 0 := by
      nlinarith [hdet]
    simp [-mul_eq_zero, cubicResidualNetwork70, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (8 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 3 * v 4 * h 0) + (-2 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (-4 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (-8 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (8 : ℝ) * (v 0 * v 3 * v 4 * h 0) + (2 : ℝ) * (v 0 * v 2 * v 3 * h 0) + (8 : ℝ) * (v 0 * v 1 * v 4 * h 1) + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) = 0 := by
      linear_combination
        ((2 : ℝ) * ((v 3) ^ 2 * h 1) + ((-3 : ℝ) / 2) * ((v 2) ^ 2 * h 1) + (2 : ℝ) * (v 1 * v 3 * h 1) + -(v 0 * v 2 * h 1)) * g0 +
      ((2 : ℝ) * ((v 3) ^ 2 * h 1) + ((-3 : ℝ) / 2) * ((v 2) ^ 2 * h 1) + (4 : ℝ) * (v 1 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 4 * h 0) + (-2 : ℝ) * (v 1 * v 2 * h 1) + (-2 : ℝ) * (v 1 * v 2 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * h 1) + (-4 : ℝ) * (v 0 * v 4 * h 1) + (8 : ℝ) * (v 0 * v 4 * h 0) + (2 : ℝ) * (v 0 * v 3 * h 1) + v 0 * v 2 * h 1 + (2 : ℝ) * (v 0 * v 2 * h 0) + (2 : ℝ) * (v 0 * v 1 * h 1)) * g1 +
      ((-2 : ℝ) * (v 4 * h 1) + (4 : ℝ) * (v 4 * h 0) + ((1 : ℝ) / 2) * (v 2 * h 1) + (2 : ℝ) * (v 2 * h 0) + (2 : ℝ) * (v 1 * h 1) + -(v 0 * h 1)) * g2
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork70, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork70, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork70, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : (-2 : ℝ) * (v 3) + v 1 + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : (4 : ℝ) * (v 4) + v 2 = 0 := by
      nlinarith [hg1]
    have g2 : (2 : ℝ) * (v 4) + -(v 3) + v 2 + v 1 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork70, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-8 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (8 : ℝ) * (v 1 * v 3 * v 4 * h 0) + (2 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (8 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (-8 : ℝ) * (v 0 * v 3 * v 4 * h 0) + (-2 : ℝ) * (v 0 * v 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 3 * v 4 * h 1) + (-2 : ℝ) * ((v 3) ^ 2 * h 1)) * g0 +
      ((-4 : ℝ) * ((v 3) ^ 2 * h 1) + (-2 : ℝ) * (v 1 * v 3 * h 1) + (2 : ℝ) * (v 1 * v 3 * h 0) + (2 : ℝ) * (v 0 * v 3 * h 1) + (-2 : ℝ) * (v 0 * v 3 * h 0)) * g1 +
      ((4 : ℝ) * ((v 3) ^ 2 * h 1)) * g2 +
      ((-2 : ℝ) * (v 1 * v 3 * h 1) + (2 : ℝ) * (v 0 * v 3 * h 1)) * g3
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork70, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork70, CodedBimolNetwork.toNetwork,
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

theorem cubicResidualNetwork70_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork70.toNetwork := by
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
  simp [cubicResidualNetwork70, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork70_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork70.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork70_jacobianNonzero
    cubicResidualNetwork70_fourCharts

def cubicResidualNetwork71 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xx), (.y, .xy), (.xx, .xy), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork71_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork71.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork71, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : v 4 + -(v 3) + v 2 + v 1 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g1 : -(v 4) + v 3 = 0 := by
      nlinarith [heq1]
    have g2 : v 2 * v 4 + (-2 : ℝ) * (v 2 * v 3) + -(v 1 * v 4) + v 0 * v 4 = 0 := by
      nlinarith [hdet]
    have g4 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + (-2 : ℝ) * (v 3 * h 0) + (2 : ℝ) * (v 3 * (v 4) ^ 2) + v 2 * h 1 + (-2 : ℝ) * (v 2 * (v 4) ^ 2) + (-2 : ℝ) * ((v 2) ^ 2 * v 3) + v 1 * h 0 + (-2 : ℝ) * (v 1 * (v 4) ^ 2) + (-2 : ℝ) * (v 1 * v 2 * v 4) + -(v 0 * h 0) + (2 : ℝ) * (v 0 * (v 4) ^ 2) + (2 : ℝ) * (v 0 * v 2 * v 4) = 0 := by
      nlinarith [hc0]
    have g5 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (2 : ℝ) * (v 3 * h 0) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + (2 : ℝ) * (v 2 * (v 4) ^ 2) + (2 : ℝ) * ((v 2) ^ 2 * v 3) + (2 : ℝ) * (v 1 * (v 4) ^ 2) + (2 : ℝ) * (v 1 * v 2 * v 4) + (-2 : ℝ) * (v 0 * (v 4) ^ 2) + (-2 : ℝ) * (v 0 * v 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork71, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + v 1 * v 2 * v 4 * h 1 + (-2 : ℝ) * (v 1 * v 2 * v 3 * h 0) + -((v 1) ^ 2 * v 4 * h 0) + -(v 0 * (v 4) ^ 2 * h 1) + v 0 * (v 4) ^ 2 * h 0 + -(v 0 * v 2 * v 4 * h 1) + (2 : ℝ) * (v 0 * v 2 * v 3 * h 0) + (2 : ℝ) * (v 0 * v 1 * v 4 * h 0) + -((v 0) ^ 2 * v 4 * h 0) = 0 := by
      linear_combination
        (v 3 * v 4 * h 1 + -(v 1 * v 3 * h 0) + v 0 * v 4 * h 0) * g0 +
      (v 3 * v 4 * h 1 + (-2 : ℝ) * ((v 2) ^ 2 * h 1) + -(v 1 * v 4 * h 1) + v 1 * v 4 * h 0 + -(v 1 * v 3 * h 0) + -(v 1 * v 2 * h 0) + (v 1) ^ 2 * h 0 + v 0 * v 4 * h 1 + (2 : ℝ) * (v 0 * v 2 * h 0) + -(v 0 * v 1 * h 0)) * g1 +
      (-(v 2 * h 1)) * g2 +
      (-(v 3 * v 4) + -(v 2 * v 4)) * g4 +
      (-(v 3 * v 4) + -(v 2 * v 4)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork71, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : -(v 4) + (2 : ℝ) * (v 3) = 0 := by
      nlinarith [hg1]
    have g3 : -(v 4) + v 3 = 0 := by
      nlinarith [heq1]
    have g4 : v 2 * v 4 + (-2 : ℝ) * (v 2 * v 3) + -(v 1 * v 4) + v 0 * v 4 = 0 := by
      nlinarith [hdet]
    simp [-mul_eq_zero, cubicResidualNetwork71, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 2 * (v 4) ^ 2 * h 1 + -(v 2 * (v 4) ^ 2 * h 0) + (v 2) ^ 2 * v 4 * h 1 + (-2 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + -(v 1 * v 2 * v 4 * h 0) + v 0 * v 2 * v 4 * h 0 = 0 := by
      linear_combination
        (v 2 * v 4 * h 1 + -(v 2 * v 4 * h 0) + (v 2) ^ 2 * h 1 + -((v 2) ^ 2 * h 0)) * g1 +
      ((-2 : ℝ) * (v 2 * v 4 * h 1) + (2 : ℝ) * (v 2 * v 4 * h 0) + (-2 : ℝ) * ((v 2) ^ 2 * h 1) + (2 : ℝ) * ((v 2) ^ 2 * h 0)) * g3 +
      (v 2 * h 0) * g4
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork71, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : v 4 + (-2 : ℝ) * (v 3) + v 1 + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : v 4 + v 2 = 0 := by
      nlinarith [hg1]
    have g2 : v 4 + -(v 3) + v 2 + v 1 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : -(v 4) + v 3 = 0 := by
      nlinarith [heq1]
    have g6 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + (-2 : ℝ) * (v 3 * h 0) + (2 : ℝ) * (v 3 * (v 4) ^ 2) + v 2 * h 1 + v 1 * h 0 + -(v 0 * h 0) = 0 := by
      nlinarith [hc0]
    have g7 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (2 : ℝ) * (v 3 * h 0) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork71, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + v 0 * (v 4) ^ 2 * h 1 + -(v 0 * (v 4) ^ 2 * h 0) = 0 := by
      linear_combination
        (-((v 2) ^ 2 * h 1) + -(v 1 * v 2 * h 1)) * g0 +
      (-((v 2) ^ 2 * h 1) + -(v 1 * v 4 * h 1) + v 1 * v 4 * h 0 + -(v 1 * v 2 * h 0) + v 0 * v 3 * h 1 + -(v 0 * v 3 * h 0) + -(v 0 * v 2 * h 1) + v 0 * v 2 * h 0) * g1 +
      (v 1 * v 2 * h 1) * g2 +
      ((-2 : ℝ) * ((v 2) ^ 2 * h 1) + -(v 1 * v 2 * h 1) + -(v 0 * v 4 * h 1) + v 0 * v 4 * h 0 + -(v 0 * v 2 * h 1) + v 0 * v 2 * h 0) * g3 +
      ((v 2) ^ 2) * g6 +
      ((v 2) ^ 2) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork71, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : v 4 + v 2 = 0 := by
      nlinarith [hg1]
    have g2 : -(v 4) + (2 : ℝ) * (v 3) = 0 := by
      nlinarith [hg2]
    have g4 : -(v 4) + v 3 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork71, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -(v 2 * (v 4) ^ 2 * h 1) + v 2 * (v 4) ^ 2 * h 0 = 0 := by
      linear_combination
        ((v 4) ^ 2 * h 0 + -(v 2 * v 4 * h 1)) * g1 +
      (-((v 4) ^ 2 * h 0) + (v 2) ^ 2 * h 1) * g2 +
      ((2 : ℝ) * ((v 4) ^ 2 * h 0) + (-2 : ℝ) * ((v 2) ^ 2 * h 1)) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork71_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork71.toNetwork := by
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
  simp [cubicResidualNetwork71, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork71_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork71.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork71_jacobianNonzero
    cubicResidualNetwork71_fourCharts

def cubicResidualNetwork72 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xx), (.y, .xy), (.xx, .xy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork72_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork72.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork72, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : (-2 : ℝ) * (v 4) + v 3 = 0 := by
      nlinarith [heq1]
    have g2 : (-2 : ℝ) * (v 2 * v 3) + (-4 : ℝ) * (v 1 * v 4) + (4 : ℝ) * (v 0 * v 4) = 0 := by
      nlinarith [hdet]
    have g4 : (4 : ℝ) * (v 4 * h 1) + (-2 : ℝ) * (v 3 * h 0) + (-32 : ℝ) * (v 3 * (v 4) ^ 2) + (16 : ℝ) * ((v 3) ^ 2 * v 4) + v 2 * h 1 + (-16 : ℝ) * (v 2 * v 3 * v 4) + (-2 : ℝ) * ((v 2) ^ 2 * v 3) + v 1 * h 0 + (-16 : ℝ) * (v 1 * v 3 * v 4) + (4 : ℝ) * ((v 1) ^ 2 * v 4) + -(v 0 * h 0) + (16 : ℝ) * (v 0 * v 3 * v 4) + (-8 : ℝ) * (v 0 * v 1 * v 4) + (4 : ℝ) * ((v 0) ^ 2 * v 4) = 0 := by
      nlinarith [hc0]
    have g5 : (-4 : ℝ) * (v 4 * h 1) + (2 : ℝ) * (v 3 * h 0) + (32 : ℝ) * (v 3 * (v 4) ^ 2) + (-16 : ℝ) * ((v 3) ^ 2 * v 4) + (16 : ℝ) * (v 2 * v 3 * v 4) + (2 : ℝ) * ((v 2) ^ 2 * v 3) + (16 : ℝ) * (v 1 * v 3 * v 4) + (-4 : ℝ) * ((v 1) ^ 2 * v 4) + (-16 : ℝ) * (v 0 * v 3 * v 4) + (8 : ℝ) * (v 0 * v 1 * v 4) + (-4 : ℝ) * ((v 0) ^ 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork72, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (8 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 3 * v 4 * h 0) + (-2 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (-4 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (-8 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (8 : ℝ) * (v 0 * v 3 * v 4 * h 0) + (2 : ℝ) * (v 0 * v 2 * v 3 * h 0) + (8 : ℝ) * (v 0 * v 1 * v 4 * h 1) + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) = 0 := by
      linear_combination
        ((-8 : ℝ) * (v 2 * v 4 * h 1) + (-4 : ℝ) * (v 2 * v 3 * h 1) + (-2 : ℝ) * ((v 2) ^ 2 * h 1) + (-8 : ℝ) * (v 1 * v 4 * h 0) + (2 : ℝ) * (v 1 * v 2 * h 1) + (-2 : ℝ) * (v 1 * v 2 * h 0) + (8 : ℝ) * (v 0 * v 4 * h 0) + (-2 : ℝ) * (v 0 * v 2 * h 1) + (2 : ℝ) * (v 0 * v 2 * h 0)) * g1 +
      ((-2 : ℝ) * (v 3 * h 1) + -(v 2 * h 1) + v 1 * h 1 + -(v 0 * h 1)) * g2 +
      ((-16 : ℝ) * ((v 4) ^ 2) + (-4 : ℝ) * (v 2 * v 4)) * g4 +
      ((-16 : ℝ) * ((v 4) ^ 2) + (-4 : ℝ) * (v 2 * v 4)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork72, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : (-2 : ℝ) * (v 3) + v 1 + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : (2 : ℝ) * (v 3) = 0 := by
      nlinarith [hg1]
    simp [-mul_eq_zero, cubicResidualNetwork72, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (8 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (-8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (-2 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + (-4 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (4 : ℝ) * (v 0 * v 2 * v 4 * h 1) = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 2 * v 4 * h 1)) * g0 +
      ((-4 : ℝ) * (v 2 * v 4 * h 0) + -((v 2) ^ 2 * h 0)) * g1
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork72, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : (-2 : ℝ) * (v 3) + v 1 + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : (4 : ℝ) * (v 4) + v 2 = 0 := by
      nlinarith [hg1]
    have g3 : (-2 : ℝ) * (v 4) + v 3 = 0 := by
      nlinarith [heq1]
    have g4 : (-2 : ℝ) * (v 2 * v 3) + (-4 : ℝ) * (v 1 * v 4) + (4 : ℝ) * (v 0 * v 4) = 0 := by
      nlinarith [hdet]
    have g5 : (-32 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (16 : ℝ) * (v 1 * (v 3) ^ 2 * v 4) + (32 : ℝ) * (v 0 * v 3 * (v 4) ^ 2) + (-16 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) = 0 := by
      nlinarith [hfold]
    have g6 : (4 : ℝ) * (v 4 * h 1) + (-2 : ℝ) * (v 3 * h 0) + (-32 : ℝ) * (v 3 * (v 4) ^ 2) + (16 : ℝ) * ((v 3) ^ 2 * v 4) + v 2 * h 1 + v 1 * h 0 + -(v 0 * h 0) = 0 := by
      nlinarith [hc0]
    have g7 : (-4 : ℝ) * (v 4 * h 1) + (2 : ℝ) * (v 3 * h 0) + (32 : ℝ) * (v 3 * (v 4) ^ 2) + (-16 : ℝ) * ((v 3) ^ 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork72, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-8 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (8 : ℝ) * (v 1 * v 3 * v 4 * h 0) + (8 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (-8 : ℝ) * (v 0 * v 3 * v 4 * h 0) = 0 := by
      linear_combination
        (v 1 * v 2 * h 0 + -(v 0 * v 2 * h 0)) * g0 +
      ((4 : ℝ) * (v 1 * v 4 * h 0) + (-2 : ℝ) * (v 1 * v 3 * h 1) + v 1 * v 2 * h 1 + (4 : ℝ) * (v 0 * v 4 * h 1) + (-2 : ℝ) * (v 0 * v 3 * h 0) + v 0 * v 1 * h 0 + -((v 0) ^ 2 * h 0)) * g1 +
      ((8 : ℝ) * (v 1 * v 4 * h 0) + (2 : ℝ) * (v 1 * v 2 * h 1) + (2 : ℝ) * (v 1 * v 2 * h 0) + (8 : ℝ) * (v 0 * v 4 * h 1) + (2 : ℝ) * (v 0 * v 2 * h 1) + (2 : ℝ) * (v 0 * v 1 * h 0) + (-2 : ℝ) * ((v 0) ^ 2 * h 0)) * g3 +
      (v 0 * h 1) * g4 +
      (-(v 0)) * g5 +
      (-(v 1 * v 2)) * g6 +
      (-(v 1 * v 2) + -(v 0 * v 1) + (v 0) ^ 2) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork72, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork72, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-8 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (8 : ℝ) * (v 2 * v 3 * v 4 * h 0) = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 2 * v 4 * h 1) + (4 : ℝ) * (v 2 * v 4 * h 0)) * g2
    nlinarith [hcertificate]

theorem cubicResidualNetwork72_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork72.toNetwork := by
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
  simp [cubicResidualNetwork72, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork72_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork72.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork72_jacobianNonzero
    cubicResidualNetwork72_fourCharts

def cubicResidualNetwork73 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xx), (.xx, .xy), (.xy, .xx), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork73_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork73.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork73, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : (2 : ℝ) * (v 4) + v 3 + -(v 2) + v 1 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g1 : (-2 : ℝ) * (v 4) + -(v 3) + v 2 = 0 := by
      nlinarith [heq1]
    have g2 : (-4 : ℝ) * (v 1 * v 4) + -(v 1 * v 3) + (4 : ℝ) * (v 0 * v 4) + v 0 * v 3 = 0 := by
      nlinarith [hdet]
    simp [-mul_eq_zero, cubicResidualNetwork73, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + (8 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (-4 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + -((v 1) ^ 2 * v 3 * h 0) + -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 + (-8 : ℝ) * (v 0 * v 2 * v 4 * h 1) + (8 : ℝ) * (v 0 * v 2 * v 4 * h 0) + (8 : ℝ) * (v 0 * v 1 * v 4 * h 1) + (2 : ℝ) * (v 0 * v 1 * v 3 * h 0) + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) + -((v 0) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        (v 1 * v 3 * h 1 + -(v 1 * v 3 * h 0) + -(v 0 * v 3 * h 1) + v 0 * v 3 * h 0) * g0 +
      ((-4 : ℝ) * (v 1 * v 4 * h 0) + -(v 1 * v 3 * h 1) + (4 : ℝ) * (v 0 * v 4 * h 0) + v 0 * v 3 * h 1) * g1 +
      ((2 : ℝ) * (v 4 * h 0) + v 3 * h 1 + (-2 : ℝ) * (v 2 * h 1) + v 2 * h 0 + v 1 * h 1 + -(v 0 * h 1)) * g2
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork73, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork73, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork73, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : (4 : ℝ) * (v 4) + v 3 = 0 := by
      nlinarith [hg1]
    have g3 : (-2 : ℝ) * (v 4) + -(v 3) + v 2 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork73, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -(v 1 * (v 3) ^ 2 * h 1) + v 1 * (v 3) ^ 2 * h 0 + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + v 0 * (v 3) ^ 2 * h 1 + -(v 0 * (v 3) ^ 2 * h 0) + (8 : ℝ) * (v 0 * v 2 * v 4 * h 1) + (-8 : ℝ) * (v 0 * v 2 * v 4 * h 0) = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 1 * v 4 * h 1) + (4 : ℝ) * (v 1 * v 4 * h 0) + -(v 1 * v 3 * h 1) + v 1 * v 3 * h 0 + (-4 : ℝ) * (v 0 * v 4 * h 0) + -(v 0 * v 3 * h 1) + -(v 0 * v 3 * h 0) + (2 : ℝ) * (v 0 * v 2 * h 1)) * g1 +
      ((-8 : ℝ) * (v 1 * v 4 * h 1) + (8 : ℝ) * (v 1 * v 4 * h 0) + (-8 : ℝ) * (v 0 * v 4 * h 0) + (-2 : ℝ) * (v 0 * v 3 * h 1)) * g3
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork73, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork73, CodedBimolNetwork.toNetwork,
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

theorem cubicResidualNetwork73_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork73.toNetwork := by
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
  simp [cubicResidualNetwork73, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork73_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork73.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork73_jacobianNonzero
    cubicResidualNetwork73_fourCharts

def cubicResidualNetwork74 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xx), (.xx, .xy), (.xy, .yy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork74_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork74.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork74, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : (2 : ℝ) * (v 4) + -(v 3) + -(v 2) + v 1 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g1 : (-2 : ℝ) * (v 4) + v 3 + v 2 = 0 := by
      nlinarith [heq1]
    have g2 : (-4 : ℝ) * (v 1 * v 4) + v 1 * v 3 + (4 : ℝ) * (v 0 * v 4) + -(v 0 * v 3) = 0 := by
      nlinarith [hdet]
    simp [-mul_eq_zero, cubicResidualNetwork74, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + (8 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (-4 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (v 1) ^ 2 * v 3 * h 0 + -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 + (-8 : ℝ) * (v 0 * v 2 * v 4 * h 1) + (8 : ℝ) * (v 0 * v 2 * v 4 * h 0) + (8 : ℝ) * (v 0 * v 1 * v 4 * h 1) + (-2 : ℝ) * (v 0 * v 1 * v 3 * h 0) + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) + (v 0) ^ 2 * v 3 * h 0 = 0 := by
      linear_combination
        (-(v 1 * v 3 * h 1) + v 1 * v 3 * h 0 + v 0 * v 3 * h 1 + -(v 0 * v 3 * h 0)) * g0 +
      ((-4 : ℝ) * (v 1 * v 4 * h 0) + v 1 * v 3 * h 1 + (4 : ℝ) * (v 0 * v 4 * h 0) + -(v 0 * v 3 * h 1)) * g1 +
      ((2 : ℝ) * (v 4 * h 0) + -(v 3 * h 1) + (-2 : ℝ) * (v 2 * h 1) + v 2 * h 0 + v 1 * h 1 + -(v 0 * h 1)) * g2
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork74, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork74, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork74, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : (4 : ℝ) * (v 4) + -(v 3) = 0 := by
      nlinarith [hg1]
    have g3 : (-2 : ℝ) * (v 4) + v 3 + v 2 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork74, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -(v 1 * (v 3) ^ 2 * h 1) + v 1 * (v 3) ^ 2 * h 0 + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + v 0 * (v 3) ^ 2 * h 1 + -(v 0 * (v 3) ^ 2 * h 0) + (8 : ℝ) * (v 0 * v 2 * v 4 * h 1) + (-8 : ℝ) * (v 0 * v 2 * v 4 * h 0) = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 1 * v 4 * h 1) + (4 : ℝ) * (v 1 * v 4 * h 0) + v 1 * v 3 * h 1 + -(v 1 * v 3 * h 0) + (-4 : ℝ) * (v 0 * v 4 * h 0) + v 0 * v 3 * h 1 + v 0 * v 3 * h 0 + (2 : ℝ) * (v 0 * v 2 * h 1)) * g1 +
      ((-8 : ℝ) * (v 1 * v 4 * h 1) + (8 : ℝ) * (v 1 * v 4 * h 0) + (-8 : ℝ) * (v 0 * v 4 * h 0) + (2 : ℝ) * (v 0 * v 3 * h 1)) * g3
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork74, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork74, CodedBimolNetwork.toNetwork,
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

theorem cubicResidualNetwork74_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork74.toNetwork := by
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
  simp [cubicResidualNetwork74, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork74_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork74.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork74_jacobianNonzero
    cubicResidualNetwork74_fourCharts

def cubicResidualNetwork75 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xx), (.y, .x), (.xy, .yy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork75_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork75.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork75, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) = 0 := by
      nlinarith [heq1]
    have g2 : (-4 : ℝ) * (v 1 * v 4) + v 1 * v 3 + -(v 1 * v 2) + (4 : ℝ) * (v 0 * v 4) + -(v 0 * v 3) + v 0 * v 2 = 0 := by
      nlinarith [hdet]
    simp [-mul_eq_zero, cubicResidualNetwork75, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
        ((-2 : ℝ) * (v 3 * v 4 * h 1) + (v 3) ^ 2 * h 1 + -((v 2) ^ 2 * h 1) + -((v 2) ^ 2 * h 0) + v 1 * v 3 * h 0 + -(v 0 * v 3 * h 0)) * g0 +
      ((-2 : ℝ) * (v 3 * v 4 * h 1) + (v 3) ^ 2 * h 1 + -((v 2) ^ 2 * h 1) + -((v 2) ^ 2 * h 0) + (4 : ℝ) * (v 1 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 4 * h 0) + -(v 1 * v 2 * h 1) + (-3 : ℝ) * (v 1 * v 2 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * h 1) + (-4 : ℝ) * (v 0 * v 4 * h 1) + (4 : ℝ) * (v 0 * v 4 * h 0) + v 0 * v 2 * h 1 + (3 : ℝ) * (v 0 * v 2 * h 0) + (4 : ℝ) * (v 0 * v 1 * h 1) + (-2 : ℝ) * ((v 0) ^ 2 * h 1)) * g1 +
      ((-2 : ℝ) * (v 4 * h 1) + (2 : ℝ) * (v 4 * h 0) + (2 : ℝ) * (v 2 * h 0) + (2 : ℝ) * (v 1 * h 1) + (-2 : ℝ) * (v 0 * h 1)) * g2
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork75, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork75, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork75, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : (4 : ℝ) * (v 4) + -(v 3) + v 2 = 0 := by
      nlinarith [hg1]
    have g2 : (2 : ℝ) * (v 4) + -(v 3) + v 2 + v 1 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork75, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
        (-((v 3) ^ 2 * h 1) + v 2 * v 3 * h 1) * g0 +
      (-((v 3) ^ 2 * h 1)) * g1 +
      ((v 3) ^ 2 * h 0) * g2 +
      ((-2 : ℝ) * ((v 3) ^ 2 * h 1) + (v 3) ^ 2 * h 0) * g3
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork75, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork75, CodedBimolNetwork.toNetwork,
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

theorem cubicResidualNetwork75_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork75.toNetwork := by
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
  simp [cubicResidualNetwork75, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork75_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork75.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork75_jacobianNonzero
    cubicResidualNetwork75_fourCharts

end SmallCusp

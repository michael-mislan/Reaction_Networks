import proofs.SmallCusp.Obstruction.CubicDegeneracy
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

def cubicResidualNetwork56 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .xx), (.y, .yy), (.xx, .zero), (.xy, .y)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork56_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork56.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork56, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork56, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork56, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork56, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 2 * (v 4) ^ 2 * h 1 + -(v 2 * (v 4) ^ 2 * h 0) + -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + (-2 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (2 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (8 : ℝ) * ((v 1) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        (-(v 2 * v 4 * h 1) + v 2 * v 4 * h 0 + (4 : ℝ) * (v 2 * v 3 * h 1) + (-4 : ℝ) * (v 2 * v 3 * h 0) + (2 : ℝ) * ((v 2) ^ 2 * h 0) + v 1 * v 4 * h 1 + -(v 1 * v 4 * h 0) + (-4 : ℝ) * (v 1 * v 3 * h 1) + (4 : ℝ) * (v 1 * v 3 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * h 0)) * g0 +
      ((-16 : ℝ) * ((v 3) ^ 2 * h 0) + (2 : ℝ) * (v 2 * v 4 * h 0) + (8 : ℝ) * (v 2 * v 3 * h 0) + (-2 : ℝ) * (v 1 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 4 * h 0)) * g3 +
      ((16 : ℝ) * ((v 3) ^ 2)) * g7
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork56, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork56, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork56, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g7 : -(v 4 * h 1) + -(v 4 * h 0) + (-4 : ℝ) * (v 3 * h 0) + (-4 : ℝ) * ((v 2) ^ 2 * v 3) + (2 : ℝ) * (v 1 * h 1) + (8 : ℝ) * (v 1 * v 2 * v 3) + (-4 : ℝ) * ((v 1) ^ 2 * v 3) = 0 := by
      nlinarith [hc0]
    have g8 : v 2 * h 1 + -(v 1 * h 1) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork56, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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

theorem cubicResidualNetwork56_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork56.toNetwork := by
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
  simp [cubicResidualNetwork56, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork56_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork56.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork56_jacobianNonzero
    cubicResidualNetwork56_fourCharts

def cubicResidualNetwork57 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .xx), (.xx, .zero), (.xy, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork57_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork57.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork57, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g2 : (-4 : ℝ) * (v 2 * v 4) + (4 : ℝ) * (v 2 * v 3) + -(v 1 * v 4) + (3 : ℝ) * (v 1 * v 3) + (4 : ℝ) * (v 1 * v 2) = 0 := by
      nlinarith [hdet]
    have g3 : (-12 : ℝ) * (v 2 * (v 4) ^ 3) + (-12 : ℝ) * (v 2 * v 3 * (v 4) ^ 2) + (12 : ℝ) * (v 2 * (v 3) ^ 2 * v 4) + (12 : ℝ) * (v 2 * (v 3) ^ 3) + (-32 : ℝ) * ((v 2) ^ 2 * (v 4) ^ 2) + (32 : ℝ) * ((v 2) ^ 2 * (v 3) ^ 2) + (32 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (-32 : ℝ) * (v 1 * v 2 * (v 3) ^ 2) + (64 : ℝ) * (v 1 * (v 2) ^ 2 * v 4) + (-64 : ℝ) * (v 1 * (v 2) ^ 2 * v 3) + (-16 : ℝ) * ((v 1) ^ 2 * v 2 * v 4) + (16 : ℝ) * ((v 1) ^ 2 * v 2 * v 3) = 0 := by
      nlinarith [hfold]
    have g5 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + -(v 3 * h 1) + -(v 3 * h 0) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + (2 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + (-8 : ℝ) * (v 2 * (v 4) ^ 2) + (8 : ℝ) * (v 2 * (v 3) ^ 2) + -(v 1 * h 1) + (4 : ℝ) * (v 1 * (v 4) ^ 2) + (-4 : ℝ) * (v 1 * (v 3) ^ 2) + (16 : ℝ) * (v 1 * v 2 * v 4) + (-16 : ℝ) * (v 1 * v 2 * v 3) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork57, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (4 : ℝ) * (v 2 * (v 3) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + (16 : ℝ) * ((v 2) ^ 2 * v 4 * h 0) + (-16 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + (8 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (-8 : ℝ) * (v 1 * v 2 * v 3 * h 1) + (8 : ℝ) * (v 1 * v 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((-10 : ℝ) * (v 2 * v 4 * h 1) + (2 : ℝ) * (v 2 * v 4 * h 0) + (-10 : ℝ) * (v 2 * v 3 * h 1) + (2 : ℝ) * (v 2 * v 3 * h 0) + (-32 : ℝ) * ((v 2) ^ 2 * h 1) + (8 : ℝ) * ((v 2) ^ 2 * h 0) + (4 : ℝ) * (v 1 * v 2 * h 1)) * g1 +
      ((-4 : ℝ) * (v 2 * h 1) + (2 : ℝ) * (v 2 * h 0)) * g2 +
      (-(v 4) + -(v 3) + (-4 : ℝ) * (v 2)) * g3 +
      ((6 : ℝ) * (v 2 * v 4) + (6 : ℝ) * (v 2 * v 3) + (16 : ℝ) * ((v 2) ^ 2) + (-4 : ℝ) * (v 1 * v 2)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork57, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + -(v 3) + (-4 : ℝ) * (v 2) = 0 := by
      nlinarith [hg0]
    have g1 : v 4 + -(v 3) = 0 := by
      nlinarith [hg1]
    have g2 : -(v 4) + -(v 3) + (-2 : ℝ) * (v 2) + (2 : ℝ) * (v 1) + v 0 = 0 := by
      nlinarith [heq0]
    have g3 : v 4 + -(v 3) + -(v 1) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork57, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 3 * v 4 * h 0) + (-3 : ℝ) * (v 1 * (v 3) ^ 2 * h 1) + (3 : ℝ) * (v 1 * (v 3) ^ 2 * h 0) + (-16 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (16 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (6 : ℝ) * ((v 1) ^ 2 * v 3 * h 1) + (8 : ℝ) * ((v 1) ^ 2 * v 2 * h 0) = 0 := by
      linear_combination
        ((-2 : ℝ) * (v 1 * v 4 * h 0) + (-2 : ℝ) * (v 1 * v 3 * h 1) + (2 : ℝ) * ((v 1) ^ 2 * h 1)) * g0 +
      ((-4 : ℝ) * (v 2 * v 4 * h 0) + (4 : ℝ) * (v 2 * v 3 * h 0) + v 1 * v 4 * h 1 + (-3 : ℝ) * (v 1 * v 4 * h 0) + v 1 * v 3 * h 1 + (-3 : ℝ) * (v 1 * v 3 * h 0) + (8 : ℝ) * (v 1 * v 2 * h 1) + (-8 : ℝ) * (v 1 * v 2 * h 0) + (-4 : ℝ) * (v 0 * v 4 * h 1) + (4 : ℝ) * (v 0 * v 1 * h 1)) * g1 +
      ((4 : ℝ) * (v 1 * v 3 * h 1)) * g2 +
      ((8 : ℝ) * (v 2 * v 4 * h 0) + (-8 : ℝ) * (v 1 * v 2 * h 1) + (-8 : ℝ) * (v 1 * v 2 * h 0) + (4 : ℝ) * (v 0 * v 4 * h 1)) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork57, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + -(v 3) + (-4 : ℝ) * (v 2) = 0 := by
      nlinarith [hg0]
    have g1 : -(v 4) + -(v 3) + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [hg1]
    have g3 : v 4 + -(v 3) + -(v 1) = 0 := by
      nlinarith [heq1]
    have g4 : (-4 : ℝ) * (v 2 * v 4) + (4 : ℝ) * (v 2 * v 3) + -(v 1 * v 4) + (3 : ℝ) * (v 1 * v 3) + (4 : ℝ) * (v 1 * v 2) = 0 := by
      nlinarith [hdet]
    have g5 : (-12 : ℝ) * (v 2 * (v 4) ^ 3) + (36 : ℝ) * (v 2 * v 3 * (v 4) ^ 2) + (-36 : ℝ) * (v 2 * (v 3) ^ 2 * v 4) + (12 : ℝ) * (v 2 * (v 3) ^ 3) + (16 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (-32 : ℝ) * (v 1 * v 2 * v 3 * v 4) + (16 : ℝ) * (v 1 * v 2 * (v 3) ^ 2) + (-4 : ℝ) * ((v 1) ^ 2 * v 2 * v 4) + (4 : ℝ) * ((v 1) ^ 2 * v 2 * v 3) = 0 := by
      nlinarith [hfold]
    have g6 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + -(v 3 * h 1) + -(v 3 * h 0) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + (-2 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + (-4 : ℝ) * (v 2 * h 0) + (-4 : ℝ) * (v 2 * (v 4) ^ 2) + (8 : ℝ) * (v 2 * v 3 * v 4) + (-4 : ℝ) * (v 2 * (v 3) ^ 2) + (2 : ℝ) * (v 1 * h 1) + (-2 : ℝ) * (v 1 * (v 4) ^ 2) + (2 : ℝ) * (v 1 * (v 3) ^ 2) + (8 : ℝ) * (v 1 * v 2 * v 4) + (-8 : ℝ) * (v 1 * v 2 * v 3) + (-4 : ℝ) * ((v 1) ^ 2 * v 2) = 0 := by
      nlinarith [hc0]
    have g7 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + -(v 3 * h 1) + -(v 3 * h 0) + (6 : ℝ) * (v 3 * (v 4) ^ 2) + (-6 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + -(v 1 * h 1) + (2 : ℝ) * (v 1 * (v 4) ^ 2) + (-4 : ℝ) * (v 1 * v 3 * v 4) + (2 : ℝ) * (v 1 * (v 3) ^ 2) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork57, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
        (((-1 : ℝ) / 4) * ((v 3) ^ 2 * h 0) + ((1 : ℝ) / 24) * (v 1 * v 4 * h 0) + (2 : ℝ) * (v 1 * v 2 * h 0)) * g0 +
      (((1 : ℝ) / 6) * (v 3 * v 4 * h 0) + ((1 : ℝ) / 12) * ((v 3) ^ 2 * h 0) + (2 : ℝ) * (v 2 * v 4 * h 1) + ((1 : ℝ) / 2) * (v 2 * v 4 * h 0) + (-2 : ℝ) * (v 2 * v 3 * h 1) + ((8 : ℝ) / 3) * (v 1 * v 2 * h 0)) * g1 +
      (((1 : ℝ) / 6) * (v 3 * v 4 * h 0) + ((1 : ℝ) / 6) * ((v 3) ^ 2 * h 0) + (9 : ℝ) * (v 2 * v 4 * h 1) + ((-14 : ℝ) / 3) * (v 2 * v 4 * h 0) + (-11 : ℝ) * (v 2 * v 3 * h 1) + ((16 : ℝ) / 3) * (v 1 * v 2 * h 0)) * g3 +
      (((-1 : ℝ) / 24) * (v 4 * h 0) + (2 : ℝ) * (v 2 * h 0) + (2 : ℝ) * (v 2 * (v 4) ^ 2) + (-4 : ℝ) * (v 2 * v 3 * v 4) + (2 : ℝ) * (v 2 * (v 3) ^ 2) + (-2 : ℝ) * (v 1 * v 2 * v 4) + (2 : ℝ) * (v 1 * v 2 * v 3)) * g4 +
      (((1 : ℝ) / 2) * (v 4) + ((-3 : ℝ) / 2) * (v 3)) * g5 +
      ((-2 : ℝ) * (v 2 * v 4) + (2 : ℝ) * (v 2 * v 3)) * g6 +
      ((-5 : ℝ) * (v 2 * v 4) + (7 : ℝ) * (v 2 * v 3)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork57, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork57, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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

theorem cubicResidualNetwork57_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork57.toNetwork := by
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
  simp [cubicResidualNetwork57, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork57_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork57.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork57_jacobianNonzero
    cubicResidualNetwork57_fourCharts

def cubicResidualNetwork58 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .xx), (.xx, .zero), (.xy, .x), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork58_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork58.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork58, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g2 : (-4 : ℝ) * (v 2 * v 4) + (4 : ℝ) * (v 2 * v 3) + -(v 1 * v 4) + (2 : ℝ) * (v 1 * v 3) + (4 : ℝ) * (v 1 * v 2) = 0 := by
      nlinarith [hdet]
    have g3 : (-12 : ℝ) * (v 2 * (v 4) ^ 3) + (12 : ℝ) * (v 2 * v 3 * (v 4) ^ 2) + (-32 : ℝ) * ((v 2) ^ 2 * (v 4) ^ 2) + (32 : ℝ) * ((v 2) ^ 2 * v 3 * v 4) + (32 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (-32 : ℝ) * (v 1 * v 2 * v 3 * v 4) + (64 : ℝ) * (v 1 * (v 2) ^ 2 * v 4) + (-64 : ℝ) * (v 1 * (v 2) ^ 2 * v 3) + (-16 : ℝ) * ((v 1) ^ 2 * v 2 * v 4) + (16 : ℝ) * ((v 1) ^ 2 * v 2 * v 3) = 0 := by
      nlinarith [hfold]
    have g4 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (-4 : ℝ) * (v 2 * h 0) + (4 : ℝ) * (v 2 * (v 4) ^ 2) + (2 : ℝ) * (v 1 * h 1) + (-4 : ℝ) * (v 1 * (v 4) ^ 2) + (-16 : ℝ) * ((v 1) ^ 2 * v 2) = 0 := by
      nlinarith [hc0]
    have g5 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + -(v 3 * h 1) + -(v 3 * h 0) + (2 : ℝ) * (v 3 * (v 4) ^ 2) + (-8 : ℝ) * (v 2 * (v 4) ^ 2) + (8 : ℝ) * (v 2 * v 3 * v 4) + -(v 1 * h 1) + (4 : ℝ) * (v 1 * (v 4) ^ 2) + (-4 : ℝ) * (v 1 * v 3 * v 4) + (16 : ℝ) * (v 1 * v 2 * v 4) + (-16 : ℝ) * (v 1 * v 2 * v 3) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork58, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (4 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (-8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (16 : ℝ) * ((v 2) ^ 2 * v 4 * h 0) + (-16 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + (8 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (-8 : ℝ) * (v 1 * v 2 * v 3 * h 1) + (8 : ℝ) * (v 1 * v 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((-10 : ℝ) * (v 2 * v 4 * h 1) + (2 : ℝ) * (v 2 * v 4 * h 0) + (-32 : ℝ) * ((v 2) ^ 2 * h 1) + (8 : ℝ) * ((v 2) ^ 2 * h 0) + (4 : ℝ) * (v 1 * v 2 * h 1)) * g1 +
      ((-8 : ℝ) * (v 2 * h 1) + (2 : ℝ) * (v 2 * h 0)) * g2 +
      (-(v 4)) * g3 +
      ((-4 : ℝ) * (v 2 * v 4) + (4 : ℝ) * (v 2 * v 3)) * g4 +
      ((2 : ℝ) * (v 2 * v 4) + (-4 : ℝ) * (v 1 * v 2)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork58, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + (-4 : ℝ) * (v 2) = 0 := by
      nlinarith [hg0]
    have g1 : v 4 + -(v 3) = 0 := by
      nlinarith [hg1]
    have g3 : v 4 + -(v 3) + -(v 1) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork58, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 2 * v 3 * v 4 * h 0) + v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 3 * v 4 * h 0) + (-16 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (16 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (4 : ℝ) * ((v 1) ^ 2 * v 3 * h 1) + (8 : ℝ) * ((v 1) ^ 2 * v 2 * h 0) = 0 := by
      linear_combination
        (-(v 1 * v 4 * h 1) + -(v 1 * v 4 * h 0) + v 1 * v 3 * h 1 + (-2 : ℝ) * ((v 1) ^ 2 * h 1)) * g0 +
      (-((v 3) ^ 2 * h 1) + (-2 : ℝ) * (v 1 * v 4 * h 0) + -(v 1 * v 3 * h 1) + (-12 : ℝ) * (v 1 * v 2 * h 1) + (-8 : ℝ) * (v 1 * v 2 * h 0) + (-4 : ℝ) * ((v 1) ^ 2 * h 1)) * g1 +
      ((v 3) ^ 2 * h 1 + (4 : ℝ) * (v 2 * v 4 * h 0) + (8 : ℝ) * (v 1 * v 2 * h 1) + (-8 : ℝ) * (v 1 * v 2 * h 0)) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork58, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + (-4 : ℝ) * (v 2) = 0 := by
      nlinarith [hg0]
    have g1 : -(v 4) + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [hg1]
    have g2 : -(v 4) + (-2 : ℝ) * (v 2) + (2 : ℝ) * (v 1) + v 0 = 0 := by
      nlinarith [heq0]
    have g3 : v 4 + -(v 3) + -(v 1) = 0 := by
      nlinarith [heq1]
    have g4 : (-4 : ℝ) * (v 2 * v 4) + (4 : ℝ) * (v 2 * v 3) + -(v 1 * v 4) + (2 : ℝ) * (v 1 * v 3) + (4 : ℝ) * (v 1 * v 2) = 0 := by
      nlinarith [hdet]
    have g5 : (-12 : ℝ) * (v 2 * (v 4) ^ 3) + (36 : ℝ) * (v 2 * v 3 * (v 4) ^ 2) + (-36 : ℝ) * (v 2 * (v 3) ^ 2 * v 4) + (12 : ℝ) * (v 2 * (v 3) ^ 3) + (16 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (-32 : ℝ) * (v 1 * v 2 * v 3 * v 4) + (16 : ℝ) * (v 1 * v 2 * (v 3) ^ 2) + (-4 : ℝ) * ((v 1) ^ 2 * v 2 * v 4) + (4 : ℝ) * ((v 1) ^ 2 * v 2 * v 3) = 0 := by
      nlinarith [hfold]
    have g6 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (-4 : ℝ) * (v 3 * (v 4) ^ 2) + (2 : ℝ) * ((v 3) ^ 2 * v 4) + (-4 : ℝ) * (v 2 * h 0) + (-4 : ℝ) * (v 2 * (v 4) ^ 2) + (8 : ℝ) * (v 2 * v 3 * v 4) + (-4 : ℝ) * (v 2 * (v 3) ^ 2) + (2 : ℝ) * (v 1 * h 1) + (-2 : ℝ) * (v 1 * (v 4) ^ 2) + (2 : ℝ) * (v 1 * v 3 * v 4) + (8 : ℝ) * (v 1 * v 2 * v 4) + (-8 : ℝ) * (v 1 * v 2 * v 3) + (-4 : ℝ) * ((v 1) ^ 2 * v 2) = 0 := by
      nlinarith [hc0]
    have g7 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + -(v 3 * h 1) + -(v 3 * h 0) + (6 : ℝ) * (v 3 * (v 4) ^ 2) + (-6 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + -(v 1 * h 1) + (2 : ℝ) * (v 1 * (v 4) ^ 2) + (-4 : ℝ) * (v 1 * v 3 * v 4) + (2 : ℝ) * (v 1 * (v 3) ^ 2) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork58, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
        (((11 : ℝ) / 4) * (v 3 * v 4 * h 1) + (-6 : ℝ) * ((v 3) ^ 2 * h 1) + (v 3) ^ 2 * h 0 + (8 : ℝ) * (v 2 * v 4 * h 0) + (-2 : ℝ) * (v 2 * v 3 * h 0) + (20 : ℝ) * ((v 2) ^ 2 * h 1) + -(v 1 * v 3 * h 0) + (-10 : ℝ) * (v 1 * v 2 * h 1) + (-10 : ℝ) * (v 1 * v 2 * h 0) + ((1 : ℝ) / 2) * ((v 1) ^ 2 * h 1) + (-10 : ℝ) * (v 0 * v 2 * h 1) + (5 : ℝ) * (v 0 * v 1 * h 1)) * g0 +
      (((-11 : ℝ) / 4) * (v 3 * v 4 * h 1) + (-4 : ℝ) * ((v 3) ^ 2 * h 1) + -((v 3) ^ 2 * h 0) + (-4 : ℝ) * (v 2 * v 4 * h 1) + (-3 : ℝ) * (v 2 * v 3 * h 1) + (-10 : ℝ) * (v 2 * v 3 * h 0) + (20 : ℝ) * ((v 2) ^ 2 * h 1) + (-24 : ℝ) * ((v 2) ^ 2 * h 0) + ((1 : ℝ) / 2) * (v 1 * v 4 * h 1) + ((15 : ℝ) / 2) * (v 1 * v 3 * h 1) + (10 : ℝ) * (v 0 * v 3 * h 1) + (10 : ℝ) * (v 0 * v 2 * h 1) + (5 : ℝ) * (v 0 * v 1 * h 1)) * g1 +
      ((10 : ℝ) * ((v 3) ^ 2 * h 1) + (-40 : ℝ) * ((v 2) ^ 2 * h 1)) * g2 +
      ((2 : ℝ) * (v 2 * v 3 * h 0) + (8 : ℝ) * ((v 2) ^ 2 * h 0) + ((1 : ℝ) / 2) * (v 1 * v 4 * h 1) + (15 : ℝ) * (v 1 * v 3 * h 1) + (10 : ℝ) * (v 0 * v 3 * h 1) + (10 : ℝ) * (v 0 * v 1 * h 1)) * g3 +
      ((2 : ℝ) * (v 3 * (v 4) ^ 2) + (-4 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + (-2 : ℝ) * (v 1 * v 3 * v 4) + (2 : ℝ) * (v 1 * (v 3) ^ 2) + (4 : ℝ) * (v 1 * v 2 * v 4) + (-4 : ℝ) * (v 1 * v 2 * v 3) + (-4 : ℝ) * ((v 1) ^ 2 * v 2)) * g4 +
      (((-1 : ℝ) / 2) * (v 3) + v 1) * g5 +
      (((-1 : ℝ) / 2) * (v 3 * v 4) + ((1 : ℝ) / 2) * ((v 3) ^ 2) + -(v 1 * v 3) + (-4 : ℝ) * (v 1 * v 2)) * g6 +
      (((-1 : ℝ) / 2) * (v 3 * v 4) + (-2 : ℝ) * (v 1 * v 3) + (-10 : ℝ) * (v 1 * v 2)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork58, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork58, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
        (v 1 * v 4 * h 1 + -(v 1 * v 3 * h 1) + (-2 : ℝ) * (v 1 * v 2 * h 0)) * g1 +
      ((2 : ℝ) * (v 2 * v 4 * h 0) + (-4 : ℝ) * (v 2 * v 3 * h 0) + v 1 * v 4 * h 0 + v 1 * v 3 * h 1 + (-2 : ℝ) * (v 1 * v 3 * h 0) + -((v 1) ^ 2 * h 1)) * g2 +
      ((-6 : ℝ) * (v 2 * v 4 * h 0) + (8 : ℝ) * (v 2 * v 3 * h 0) + v 1 * v 3 * h 1) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork58_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork58.toNetwork := by
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
  simp [cubicResidualNetwork58, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork58_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork58.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork58_jacobianNonzero
    cubicResidualNetwork58_fourCharts

def cubicResidualNetwork59 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .xx), (.xx, .zero), (.xy, .y), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork59_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork59.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork59, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g2 : (-4 : ℝ) * (v 2 * v 4) + -(v 1 * v 4) + v 1 * v 3 + (4 : ℝ) * (v 1 * v 2) = 0 := by
      nlinarith [hdet]
    have g3 : (-12 : ℝ) * (v 2 * (v 4) ^ 3) + (-24 : ℝ) * (v 2 * v 3 * (v 4) ^ 2) + (-12 : ℝ) * (v 2 * (v 3) ^ 2 * v 4) + (-32 : ℝ) * ((v 2) ^ 2 * (v 4) ^ 2) + (-32 : ℝ) * ((v 2) ^ 2 * v 3 * v 4) + (32 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (32 : ℝ) * (v 1 * v 2 * v 3 * v 4) + (64 : ℝ) * (v 1 * (v 2) ^ 2 * v 4) + (-16 : ℝ) * ((v 1) ^ 2 * v 2 * v 4) = 0 := by
      nlinarith [hfold]
    have g5 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + (-4 : ℝ) * (v 3 * (v 4) ^ 2) + (-2 : ℝ) * ((v 3) ^ 2 * v 4) + (-8 : ℝ) * (v 2 * (v 4) ^ 2) + (-8 : ℝ) * (v 2 * v 3 * v 4) + -(v 1 * h 1) + (4 : ℝ) * (v 1 * (v 4) ^ 2) + (4 : ℝ) * (v 1 * v 3 * v 4) + (16 : ℝ) * (v 1 * v 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork59, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (16 : ℝ) * ((v 2) ^ 2 * v 4 * h 0) + (8 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 0) = 0 := by
      linear_combination
        ((-10 : ℝ) * (v 2 * v 4 * h 1) + (2 : ℝ) * (v 2 * v 4 * h 0) + (-10 : ℝ) * (v 2 * v 3 * h 1) + (2 : ℝ) * (v 2 * v 3 * h 0) + (-32 : ℝ) * ((v 2) ^ 2 * h 1) + (8 : ℝ) * ((v 2) ^ 2 * h 0) + (4 : ℝ) * (v 1 * v 2 * h 1)) * g1 +
      ((-4 : ℝ) * (v 2 * h 1) + (2 : ℝ) * (v 2 * h 0)) * g2 +
      (-(v 4) + -(v 3) + (-4 : ℝ) * (v 2)) * g3 +
      ((6 : ℝ) * (v 2 * v 4) + (6 : ℝ) * (v 2 * v 3) + (16 : ℝ) * ((v 2) ^ 2) + (-4 : ℝ) * (v 1 * v 2)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork59, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork59, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (4 : ℝ) * (v 2 * v 3 * v 4 * h 0) + v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + -(v 1 * (v 3) ^ 2 * h 1) + v 1 * (v 3) ^ 2 * h 0 + (-16 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + (2 : ℝ) * ((v 1) ^ 2 * v 3 * h 1) + (8 : ℝ) * ((v 1) ^ 2 * v 2 * h 0) = 0 := by
      linear_combination
        (-((v 3) ^ 2 * h 1) + (v 3) ^ 2 * h 0 + (4 : ℝ) * (v 2 * v 4 * h 0) + (4 : ℝ) * (v 2 * v 3 * h 0) + v 1 * v 4 * h 1 + -(v 1 * v 4 * h 0) + (2 : ℝ) * (v 1 * v 3 * h 1) + (-8 : ℝ) * (v 1 * v 2 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * h 1)) * g1 +
      ((v 3) ^ 2 * h 1 + -((v 3) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 3 * h 1) + (-8 : ℝ) * (v 1 * v 2 * h 0)) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork59, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g5 : (-12 : ℝ) * (v 2 * (v 4) ^ 3) + (16 : ℝ) * (v 1 * v 2 * (v 4) ^ 2) + (-4 : ℝ) * ((v 1) ^ 2 * v 2 * v 4) = 0 := by
      nlinarith [hfold]
    have g7 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + -(v 1 * h 1) + (2 : ℝ) * (v 1 * (v 4) ^ 2) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork59, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (4 : ℝ) * (v 1 * v 2 * v 4 * h 0) = 0 := by
      linear_combination
        ((10 : ℝ) * (v 2 * v 4 * h 1) + (-2 : ℝ) * (v 2 * v 4 * h 0) + (-2 : ℝ) * (v 1 * v 2 * h 1)) * g3 +
      (v 4) * g5 +
      ((-6 : ℝ) * (v 2 * v 4) + (2 : ℝ) * (v 1 * v 2)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork59, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork59, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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

theorem cubicResidualNetwork59_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork59.toNetwork := by
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
  simp [cubicResidualNetwork59, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork59_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork59.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork59_jacobianNonzero
    cubicResidualNetwork59_fourCharts

def cubicResidualNetwork60 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .xy), (.y, .yy), (.xx, .zero), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork60_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork60.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork60, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : -(v 4) + v 2 = 0 := by
      nlinarith [heq1]
    have g2 : (4 : ℝ) * (v 3 * v 4) + -(v 2 * v 4) + (-4 : ℝ) * (v 2 * v 3) + v 1 * v 4 = 0 := by
      nlinarith [hdet]
    have g3 : (12 : ℝ) * (v 3 * (v 4) ^ 3) + (32 : ℝ) * ((v 3) ^ 2 * (v 4) ^ 2) + (-16 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (-32 : ℝ) * (v 1 * (v 3) ^ 2 * v 4) + (4 : ℝ) * ((v 1) ^ 2 * v 3 * v 4) = 0 := by
      nlinarith [hfold]
    have g5 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (8 : ℝ) * (v 3 * (v 4) ^ 2) + v 2 * h 1 + (-2 : ℝ) * (v 1 * (v 4) ^ 2) + (-8 : ℝ) * (v 1 * v 3 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork60, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
        ((-10 : ℝ) * (v 3 * v 4 * h 1) + (2 : ℝ) * (v 3 * v 4 * h 0) + (-32 : ℝ) * ((v 3) ^ 2 * h 1) + (8 : ℝ) * ((v 3) ^ 2 * h 0) + (2 : ℝ) * (v 1 * v 3 * h 1)) * g1 +
      ((-4 : ℝ) * (v 3 * h 1) + (2 : ℝ) * (v 3 * h 0)) * g2 +
      (-(v 4) + (-4 : ℝ) * (v 3)) * g3 +
      ((6 : ℝ) * (v 3 * v 4) + (16 : ℝ) * ((v 3) ^ 2) + (-2 : ℝ) * (v 1 * v 3)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork60, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork60, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * (v 3 * (v 4) ^ 2 * h 0) + v 2 * (v 4) ^ 2 * h 1 + -(v 2 * (v 4) ^ 2 * h 0) + -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + (8 : ℝ) * (v 1 * v 3 * v 4 * h 0) + -(v 1 * v 2 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (v 1) ^ 2 * v 4 * h 1 = 0 := by
      linear_combination
        ((4 : ℝ) * (v 3 * v 4 * h 0) + -(v 2 * v 4 * h 1) + v 2 * v 4 * h 0 + v 1 * v 4 * h 1 + -(v 1 * v 4 * h 0) + (-4 : ℝ) * (v 1 * v 3 * h 0) + v 1 * v 2 * h 1 + -((v 1) ^ 2 * h 1)) * g1 +
      ((-4 : ℝ) * (v 1 * v 3 * h 0)) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork60, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g3 : -(v 4) + v 2 = 0 := by
      nlinarith [heq1]
    have g4 : (4 : ℝ) * (v 3 * v 4) + -(v 2 * v 4) + (-4 : ℝ) * (v 2 * v 3) + v 1 * v 4 = 0 := by
      nlinarith [hdet]
    have g5 : (12 : ℝ) * (v 3 * (v 4) ^ 3) + (-16 : ℝ) * (v 2 * v 3 * (v 4) ^ 2) + (4 : ℝ) * ((v 2) ^ 2 * v 3 * v 4) = 0 := by
      nlinarith [hfold]
    have g6 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (-4 : ℝ) * (v 3 * h 0) + (-4 : ℝ) * (v 3 * (v 4) ^ 2) + (-2 : ℝ) * (v 2 * (v 4) ^ 2) + (8 : ℝ) * (v 2 * v 3 * v 4) + (-4 : ℝ) * ((v 2) ^ 2 * v 3) + v 1 * h 1 = 0 := by
      nlinarith [hc0]
    have g7 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + v 2 * h 1 + (-2 : ℝ) * (v 2 * (v 4) ^ 2) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork60, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 3 * (v 4) ^ 2 * h 1) + (-8 : ℝ) * (v 3 * (v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (4 : ℝ) * (v 2 * v 3 * v 4 * h 0) = 0 := by
      linear_combination
        (((-3 : ℝ) / 2) * ((v 4) ^ 2 * h 1) + (-2 : ℝ) * (v 3 * v 4 * h 0) + ((1 : ℝ) / 2) * ((v 2) ^ 2 * h 1) + ((3 : ℝ) / 2) * (v 1 * v 4 * h 1) + v 1 * v 4 * h 0 + (-2 : ℝ) * (v 1 * v 3 * h 0) + ((-1 : ℝ) / 2) * (v 1 * v 2 * h 1) + -(v 1 * v 2 * h 0)) * g0 +
      (((3 : ℝ) / 2) * ((v 4) ^ 2 * h 1) + ((1 : ℝ) / 2) * ((v 4) ^ 2 * h 0) + (-8 : ℝ) * ((v 3) ^ 2 * h 0) + ((-1 : ℝ) / 2) * (v 2 * v 4 * h 1) + -(v 2 * v 4 * h 0) + (-4 : ℝ) * (v 2 * v 3 * h 0) + ((1 : ℝ) / 2) * (v 1 * v 4 * h 1)) * g1 +
      (((-1 : ℝ) / 2) * ((v 4) ^ 2 * h 0) + (-8 : ℝ) * (v 3 * v 4 * h 1) + (2 : ℝ) * (v 2 * v 3 * h 1) + (-2 : ℝ) * (v 1 * v 3 * h 1)) * g3 +
      ((v 4) ^ 3 + (4 : ℝ) * (v 3 * (v 4) ^ 2) + -(v 2 * (v 4) ^ 2) + (-4 : ℝ) * (v 2 * v 3 * v 4)) * g4 +
      ((-2 : ℝ) * (v 4) + ((-1 : ℝ) / 2) * (v 1)) * g5 +
      ((4 : ℝ) * (v 3 * v 4) + ((-1 : ℝ) / 2) * (v 1 * v 4)) * g6 +
      ((6 : ℝ) * (v 3 * v 4) + ((1 : ℝ) / 2) * (v 2 * v 4)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork60, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g2 : -(v 4) = 0 := by
      nlinarith [hg2]
    simp [-mul_eq_zero, cubicResidualNetwork60, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * (v 3 * (v 4) ^ 2 * h 0) + v 2 * (v 4) ^ 2 * h 1 + -(v 2 * (v 4) ^ 2 * h 0) + (8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + -((v 2) ^ 2 * v 4 * h 1) + (-4 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + -(v 1 * (v 4) ^ 2 * h 1) + v 1 * (v 4) ^ 2 * h 0 + v 1 * v 2 * v 4 * h 1 = 0 := by
      linear_combination
        ((v 2) ^ 2 * h 0) * g0 +
      ((4 : ℝ) * (v 3 * v 4 * h 0) + -(v 2 * v 4 * h 1) + v 2 * v 4 * h 0 + (-8 : ℝ) * (v 2 * v 3 * h 0) + (v 2) ^ 2 * h 1 + -((v 2) ^ 2 * h 0) + v 1 * v 4 * h 1 + -(v 1 * v 4 * h 0) + -(v 1 * v 2 * h 1)) * g2
    nlinarith [hcertificate]

theorem cubicResidualNetwork60_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork60.toNetwork := by
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
  simp [cubicResidualNetwork60, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork60_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork60.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork60_jacobianNonzero
    cubicResidualNetwork60_fourCharts

def cubicResidualNetwork61 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .xy), (.xx, .zero), (.xy, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork61_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork61.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork61, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork61, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (4 : ℝ) * (v 2 * (v 3) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + (16 : ℝ) * ((v 2) ^ 2 * v 4 * h 0) + (-16 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + (4 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (-4 : ℝ) * (v 1 * v 2 * v 3 * h 1) + (4 : ℝ) * (v 1 * v 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 2 * v 4 * h 1) + (8 : ℝ) * (v 2 * v 4 * h 0) + (-4 : ℝ) * (v 2 * v 3 * h 1) + (8 : ℝ) * (v 2 * v 3 * h 0) + (16 : ℝ) * ((v 2) ^ 2 * h 0) + (4 : ℝ) * (v 1 * v 2 * h 1) + (-4 : ℝ) * (v 1 * v 2 * h 0)) * g1
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork61, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork61, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + -(v 1 * (v 3) ^ 2 * h 1) + v 1 * (v 3) ^ 2 * h 0 + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (8 : ℝ) * (v 1 * v 2 * v 3 * h 0) + -((v 1) ^ 2 * v 4 * h 1) + (v 1) ^ 2 * v 3 * h 1 = 0 := by
      linear_combination
        ((4 : ℝ) * (v 2 * v 4 * h 0) + (4 : ℝ) * (v 2 * v 3 * h 0) + v 1 * v 4 * h 1 + v 1 * v 3 * h 1) * g1 +
      (-(v 1 * v 4 * h 0) + -(v 1 * v 3 * h 0) + (-8 : ℝ) * (v 1 * v 2 * h 0) + -((v 1) ^ 2 * h 1)) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork61, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork61, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-8 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (16 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (4 : ℝ) * (v 2 * (v 3) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) = 0 := by
      linear_combination
        ((4 : ℝ) * (v 2 * v 4 * h 1) + (-8 : ℝ) * (v 2 * v 4 * h 0) + (-4 : ℝ) * (v 2 * v 3 * h 1) + (8 : ℝ) * (v 2 * v 3 * h 0)) * g3
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork61, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork61, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
        ((4 : ℝ) * (v 2 * v 3 * h 0) + -(v 1 * v 4 * h 1) + v 1 * v 4 * h 0 + v 1 * v 3 * h 1) * g2 +
      ((-4 : ℝ) * (v 2 * v 4 * h 0) + -(v 1 * v 3 * h 0)) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork61_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork61.toNetwork := by
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
  simp [cubicResidualNetwork61, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork61_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork61.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork61_jacobianNonzero
    cubicResidualNetwork61_fourCharts

def cubicResidualNetwork62 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .xy), (.xx, .zero), (.xy, .x), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork62_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork62.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork62, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork62, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (4 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (-8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (16 : ℝ) * ((v 2) ^ 2 * v 4 * h 0) + (-16 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) + (4 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (-4 : ℝ) * (v 1 * v 2 * v 3 * h 1) + (4 : ℝ) * (v 1 * v 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 2 * v 4 * h 1) + (8 : ℝ) * (v 2 * v 4 * h 0) + (16 : ℝ) * ((v 2) ^ 2 * h 0) + (4 : ℝ) * (v 1 * v 2 * h 1) + (-4 : ℝ) * (v 1 * v 2 * h 0)) * g1
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork62, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork62, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 2 * v 3 * v 4 * h 0) + v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + -(v 1 * v 3 * v 4 * h 1) + v 1 * v 3 * v 4 * h 0 + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (8 : ℝ) * (v 1 * v 2 * v 3 * h 0) + -((v 1) ^ 2 * v 4 * h 1) + (v 1) ^ 2 * v 3 * h 1 = 0 := by
      linear_combination
        ((4 : ℝ) * (v 2 * v 4 * h 0) + v 1 * v 4 * h 1 + -(v 1 * v 4 * h 0) + (-8 : ℝ) * (v 1 * v 2 * h 0)) * g1 +
      (-((v 1) ^ 2 * h 1)) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork62, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + (-4 : ℝ) * (v 2) = 0 := by
      nlinarith [hg0]
    have g3 : v 4 + -(v 3) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork62, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-8 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (16 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (4 : ℝ) * (v 2 * (v 3) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) = 0 := by
      linear_combination
        ((-2 : ℝ) * (v 3 * v 4 * h 0) + (2 : ℝ) * ((v 3) ^ 2 * h 0)) * g0 +
      ((-2 : ℝ) * (v 3 * v 4 * h 0) + (4 : ℝ) * (v 2 * v 4 * h 1) + (-8 : ℝ) * (v 2 * v 4 * h 0) + (-4 : ℝ) * (v 2 * v 3 * h 1)) * g3
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork62, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + (-4 : ℝ) * (v 2) = 0 := by
      nlinarith [hg0]
    have g1 : -(v 4) + v 1 = 0 := by
      nlinarith [hg1]
    have g2 : v 4 + -(v 3) = 0 := by
      nlinarith [hg2]
    have g4 : v 4 + -(v 3) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork62, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
        (-(v 3 * v 4 * h 1) + -(v 3 * v 4 * h 0) + (4 : ℝ) * (v 2 * v 3 * h 0) + -(v 1 * v 4 * h 0) + (2 : ℝ) * (v 1 * v 3 * h 0) + (-4 : ℝ) * (v 1 * v 2 * h 0) + (v 1) ^ 2 * h 1) * g0 +
      ((2 : ℝ) * (v 3 * v 4 * h 1) + -((v 3) ^ 2 * h 1) + (v 3) ^ 2 * h 0 + (4 : ℝ) * (v 2 * v 3 * h 1) + (-16 : ℝ) * ((v 2) ^ 2 * h 0) + v 1 * v 4 * h 1 + (4 : ℝ) * (v 1 * v 2 * h 1)) * g1 +
      (-(v 3 * v 4 * h 0) + (-4 : ℝ) * (v 2 * v 4 * h 0) + (4 : ℝ) * (v 2 * v 3 * h 0) + (-8 : ℝ) * (v 1 * v 2 * h 0)) * g2 +
      (v 3 * v 4 * h 1 + (-16 : ℝ) * ((v 2) ^ 2 * h 0) + (4 : ℝ) * (v 1 * v 2 * h 1)) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork62_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork62.toNetwork := by
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
  simp [cubicResidualNetwork62, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork62_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork62.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork62_jacobianNonzero
    cubicResidualNetwork62_fourCharts

def cubicResidualNetwork63 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .xy), (.xx, .zero), (.xy, .xx), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork63_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork63.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork63, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork63, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
        ((-4 : ℝ) * (v 2 * v 4 * h 1) + (8 : ℝ) * (v 2 * v 4 * h 0) + (4 : ℝ) * (v 2 * v 3 * h 1) + (-8 : ℝ) * (v 2 * v 3 * h 0) + (16 : ℝ) * ((v 2) ^ 2 * h 0) + (4 : ℝ) * (v 1 * v 2 * h 1) + (-4 : ℝ) * (v 1 * v 2 * h 0)) * g1
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork63, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + v 3 + (-4 : ℝ) * (v 2) = 0 := by
      nlinarith [hg0]
    have g1 : v 4 + -(v 3) = 0 := by
      nlinarith [hg1]
    have g3 : v 4 + -(v 3) = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork63, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (4 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 3 * v 4 * h 0) + v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (8 : ℝ) * (v 1 * v 2 * v 3 * h 0) + -((v 1) ^ 2 * v 4 * h 1) + (v 1) ^ 2 * v 3 * h 1 = 0 := by
      linear_combination
        ((2 : ℝ) * (v 1 * v 4 * h 0) + (-2 : ℝ) * (v 1 * v 3 * h 0)) * g0 +
      (v 1 * v 4 * h 1 + -((v 1) ^ 2 * h 1)) * g1 +
      ((4 : ℝ) * (v 2 * v 4 * h 0) + (-4 : ℝ) * (v 2 * v 3 * h 0) + v 1 * v 4 * h 0 + -(v 1 * v 3 * h 1) + -(v 1 * v 3 * h 0)) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork63, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + v 3 + (-4 : ℝ) * (v 2) = 0 := by
      nlinarith [hg0]
    have g1 : -(v 4) + v 3 + v 1 = 0 := by
      nlinarith [hg1]
    have g3 : v 4 + -(v 3) = 0 := by
      nlinarith [heq1]
    have g5 : (-12 : ℝ) * (v 2 * (v 4) ^ 3) + (36 : ℝ) * (v 2 * v 3 * (v 4) ^ 2) + (-36 : ℝ) * (v 2 * (v 3) ^ 2 * v 4) + (12 : ℝ) * (v 2 * (v 3) ^ 3) = 0 := by
      nlinarith [hfold]
    have g6 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + v 3 * h 1 + v 3 * h 0 + (-6 : ℝ) * (v 3 * (v 4) ^ 2) + (6 : ℝ) * ((v 3) ^ 2 * v 4) + (-2 : ℝ) * ((v 3) ^ 3) + (-4 : ℝ) * (v 2 * h 0) + (-4 : ℝ) * (v 2 * (v 4) ^ 2) + (8 : ℝ) * (v 2 * v 3 * v 4) + (-4 : ℝ) * (v 2 * (v 3) ^ 2) + v 1 * h 1 = 0 := by
      nlinarith [hc0]
    have g7 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + -(v 3 * h 1) + -(v 3 * h 0) + (6 : ℝ) * (v 3 * (v 4) ^ 2) + (-6 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork63, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-8 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (16 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (4 : ℝ) * (v 2 * (v 3) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) = 0 := by
      linear_combination
        ((-3 : ℝ) * ((h 0) ^ 2)) * g0 +
      ((-3 : ℝ) * (h 0 * h 1)) * g1 +
      ((-3 : ℝ) * (h 0 * h 1) + (-3 : ℝ) * ((h 0) ^ 2)) * g3 +
      (((-2 : ℝ) / 3) * (v 4) + ((2 : ℝ) / 3) * (v 3)) * g5 +
      ((3 : ℝ) * (h 0)) * g6 +
      ((3 : ℝ) * (h 0) + (4 : ℝ) * (v 2 * v 4) + (-4 : ℝ) * (v 2 * v 3)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork63, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 4) + v 3 + (-4 : ℝ) * (v 2) = 0 := by
      nlinarith [hg0]
    have g1 : -(v 4) + v 3 + v 1 = 0 := by
      nlinarith [hg1]
    have g2 : v 4 + -(v 3) = 0 := by
      nlinarith [hg2]
    have g4 : v 4 + -(v 3) = 0 := by
      nlinarith [heq1]
    have g5 : (-4 : ℝ) * (v 2 * v 4) + (4 : ℝ) * (v 2 * v 3) + -(v 1 * v 4) + v 1 * v 3 = 0 := by
      nlinarith [hdet]
    have g6 : (-4 : ℝ) * (v 2 * (v 4) ^ 3) + (12 : ℝ) * (v 2 * v 3 * (v 4) ^ 2) + (-12 : ℝ) * (v 2 * (v 3) ^ 2 * v 4) + (4 : ℝ) * (v 2 * (v 3) ^ 3) + (2 : ℝ) * (v 1 * (v 4) ^ 3) + (-6 : ℝ) * (v 1 * v 3 * (v 4) ^ 2) + (6 : ℝ) * (v 1 * (v 3) ^ 2 * v 4) + (-2 : ℝ) * (v 1 * (v 3) ^ 3) = 0 := by
      nlinarith [hfold]
    have g7 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + v 3 * h 1 + v 3 * h 0 + (-6 : ℝ) * (v 3 * (v 4) ^ 2) + (6 : ℝ) * ((v 3) ^ 2 * v 4) + (-2 : ℝ) * ((v 3) ^ 3) + (-4 : ℝ) * (v 2 * h 0) + (-4 : ℝ) * (v 2 * (v 4) ^ 2) + (8 : ℝ) * (v 2 * v 3 * v 4) + (-4 : ℝ) * (v 2 * (v 3) ^ 2) + v 1 * h 1 = 0 := by
      nlinarith [hc0]
    have g8 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + -(v 3 * h 1) + -(v 3 * h 0) + (6 : ℝ) * (v 3 * (v 4) ^ 2) + (-6 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork63, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
        ((-3 : ℝ) * ((h 0) ^ 2)) * g0 +
      ((-3 : ℝ) * (h 0 * h 1)) * g1 +
      ((-3 : ℝ) * ((h 0) ^ 2)) * g2 +
      ((-3 : ℝ) * (h 0 * h 1)) * g4 +
      (((1 : ℝ) / 3) * (v 4 * h 1) + ((-5 : ℝ) / 3) * (v 4 * h 0) + ((-1 : ℝ) / 3) * (v 3 * h 1) + ((5 : ℝ) / 3) * (v 3 * h 0)) * g5 +
      (((-2 : ℝ) / 3) * (v 4) + ((2 : ℝ) / 3) * (v 3)) * g6 +
      ((3 : ℝ) * (h 0)) * g7 +
      ((3 : ℝ) * (h 0) + ((4 : ℝ) / 3) * (v 2 * v 4) + ((-4 : ℝ) / 3) * (v 2 * v 3) + ((-2 : ℝ) / 3) * (v 1 * v 4) + ((2 : ℝ) / 3) * (v 1 * v 3)) * g8
    nlinarith [hcertificate]

theorem cubicResidualNetwork63_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork63.toNetwork := by
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
  simp [cubicResidualNetwork63, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork63_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork63.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork63_jacobianNonzero
    cubicResidualNetwork63_fourCharts

def cubicResidualNetwork64 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xy, .zero), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork64_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork64.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork64, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : -(v 4) + -(v 3) + v 1 = 0 := by
      nlinarith [heq1]
    have g2 : (4 : ℝ) * (v 2 * v 4) + (4 : ℝ) * (v 2 * v 3) + v 1 * v 4 + -(v 1 * v 3) + (-4 : ℝ) * (v 1 * v 2) = 0 := by
      nlinarith [hdet]
    have g3 : (12 : ℝ) * (v 2 * (v 4) ^ 3) + (-12 : ℝ) * (v 2 * v 3 * (v 4) ^ 2) + (-12 : ℝ) * (v 2 * (v 3) ^ 2 * v 4) + (12 : ℝ) * (v 2 * (v 3) ^ 3) + (-32 : ℝ) * ((v 2) ^ 2 * (v 4) ^ 2) + (32 : ℝ) * ((v 2) ^ 2 * (v 3) ^ 2) = 0 := by
      nlinarith [hfold]
    have g5 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + -(v 3 * h 1) + -(v 3 * h 0) + (-2 : ℝ) * (v 3 * (v 4) ^ 2) + (-2 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + (-8 : ℝ) * (v 2 * (v 4) ^ 2) + (8 : ℝ) * (v 2 * (v 3) ^ 2) + v 1 * h 1 = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork64, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (4 : ℝ) * (v 2 * (v 3) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + (-16 : ℝ) * ((v 2) ^ 2 * v 4 * h 0) + (-16 : ℝ) * ((v 2) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((10 : ℝ) * (v 2 * v 4 * h 1) + (-2 : ℝ) * (v 2 * v 4 * h 0) + (-10 : ℝ) * (v 2 * v 3 * h 1) + (2 : ℝ) * (v 2 * v 3 * h 0) + (-32 : ℝ) * ((v 2) ^ 2 * h 1) + (8 : ℝ) * ((v 2) ^ 2 * h 0)) * g1 +
      (((3 : ℝ) / 2) * (v 4 * h 1) + ((3 : ℝ) / 2) * (v 4 * h 0) + ((3 : ℝ) / 2) * (v 3 * h 1) + ((3 : ℝ) / 2) * (v 3 * h 0) + (-4 : ℝ) * (v 2 * h 1) + (2 : ℝ) * (v 2 * h 0) + ((-3 : ℝ) / 2) * (v 1 * h 1) + (-3 : ℝ) * ((v 4) ^ 3) + (3 : ℝ) * (v 3 * (v 4) ^ 2) + (3 : ℝ) * ((v 3) ^ 2 * v 4) + (-3 : ℝ) * ((v 3) ^ 3) + (12 : ℝ) * (v 2 * (v 4) ^ 2) + (-12 : ℝ) * (v 2 * (v 3) ^ 2)) * g2 +
      (v 4 + -(v 3) + (-4 : ℝ) * (v 2)) * g3 +
      ((12 : ℝ) * (v 2 * v 3) + (16 : ℝ) * ((v 2) ^ 2) + ((3 : ℝ) / 2) * (v 1 * v 4) + ((-3 : ℝ) / 2) * (v 1 * v 3) + (-6 : ℝ) * (v 1 * v 2)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork64, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : v 4 + -(v 3) + (-4 : ℝ) * (v 2) = 0 := by
      nlinarith [hg0]
    have g1 : -(v 4) + -(v 3) = 0 := by
      nlinarith [hg1]
    have g2 : v 4 + -(v 3) + (-2 : ℝ) * (v 2) + v 0 = 0 := by
      nlinarith [heq0]
    have g3 : -(v 4) + -(v 3) + v 1 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork64, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 3 * v 4 * h 0) + v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) = 0 := by
      linear_combination
        ((-2 : ℝ) * (v 1 * v 4 * h 0) + (6 : ℝ) * (v 1 * v 3 * h 1) + (4 : ℝ) * (v 1 * v 2 * h 1)) * g0 +
      ((4 : ℝ) * (v 2 * v 4 * h 0) + (4 : ℝ) * (v 2 * v 3 * h 0) + -(v 1 * v 4 * h 1) + -(v 1 * v 4 * h 0) + v 1 * v 3 * h 1 + v 1 * v 3 * h 0 + (-4 : ℝ) * (v 1 * v 2 * h 1) + (-4 : ℝ) * (v 0 * v 1 * h 1) + (-4 : ℝ) * ((v 0) ^ 2 * h 1)) * g1 +
      ((-8 : ℝ) * (v 1 * v 3 * h 1) + (-8 : ℝ) * (v 1 * v 2 * h 1) + (-4 : ℝ) * (v 0 * v 1 * h 1)) * g2 +
      ((-8 : ℝ) * (v 2 * v 4 * h 0) + (4 : ℝ) * ((v 0) ^ 2 * h 1)) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork64, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : v 4 + -(v 3) + (-4 : ℝ) * (v 2) = 0 := by
      nlinarith [hg0]
    have g1 : v 4 + -(v 3) = 0 := by
      nlinarith [hg1]
    have g3 : -(v 4) + -(v 3) + v 1 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork64, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (8 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (-16 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (4 : ℝ) * (v 2 * (v 3) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 3) ^ 2 * h 0) + (-4 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (4 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (-4 : ℝ) * (v 1 * v 2 * v 3 * h 1) + (4 : ℝ) * (v 1 * v 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((v 1) ^ 2 * h 0) * g0 +
      ((-4 : ℝ) * (v 2 * v 4 * h 1) + (8 : ℝ) * (v 2 * v 4 * h 0) + (-4 : ℝ) * (v 2 * v 3 * h 1) + (8 : ℝ) * (v 2 * v 3 * h 0) + (4 : ℝ) * (v 1 * v 2 * h 1) + (-8 : ℝ) * (v 1 * v 2 * h 0) + -((v 1) ^ 2 * h 0)) * g1 +
      ((-8 : ℝ) * (v 2 * v 4 * h 1) + (16 : ℝ) * (v 2 * v 4 * h 0) + (4 : ℝ) * (v 1 * v 2 * h 0)) * g3
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork64, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork64, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
        ((-4 : ℝ) * (v 2 * v 4 * h 0) + (-4 : ℝ) * (v 2 * v 3 * h 0) + (v 1) ^ 2 * h 1) * g1 +
      ((8 : ℝ) * (v 2 * v 3 * h 0) + v 1 * v 4 * h 1 + -(v 1 * v 4 * h 0) + -(v 1 * v 3 * h 1) + v 1 * v 3 * h 0 + (-4 : ℝ) * (v 1 * v 2 * h 0)) * g2 +
      ((-4 : ℝ) * (v 1 * v 2 * h 0)) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork64_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork64.toNetwork := by
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
  simp [cubicResidualNetwork64, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork64_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork64.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork64_jacobianNonzero
    cubicResidualNetwork64_fourCharts

def cubicResidualNetwork65 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xy, .y), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork65_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork65.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork65, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : -(v 4) + v 1 = 0 := by
      nlinarith [heq1]
    have g2 : (4 : ℝ) * (v 2 * v 4) + v 1 * v 4 + -(v 1 * v 3) + (-4 : ℝ) * (v 1 * v 2) = 0 := by
      nlinarith [hdet]
    have g3 : (12 : ℝ) * (v 2 * (v 4) ^ 3) + (-24 : ℝ) * (v 2 * v 3 * (v 4) ^ 2) + (12 : ℝ) * (v 2 * (v 3) ^ 2 * v 4) + (-32 : ℝ) * ((v 2) ^ 2 * (v 4) ^ 2) + (32 : ℝ) * ((v 2) ^ 2 * v 3 * v 4) = 0 := by
      nlinarith [hfold]
    have g4 : v 4 * h 1 + v 4 * h 0 + (-2 : ℝ) * ((v 4) ^ 3) + -(v 3 * h 1) + -(v 3 * h 0) + (6 : ℝ) * (v 3 * (v 4) ^ 2) + (-6 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + (-4 : ℝ) * (v 2 * h 0) + (4 : ℝ) * (v 2 * (v 4) ^ 2) + (-8 : ℝ) * (v 2 * v 3 * v 4) + (4 : ℝ) * (v 2 * (v 3) ^ 2) = 0 := by
      nlinarith [hc0]
    have g5 : -(v 4 * h 1) + -(v 4 * h 0) + (2 : ℝ) * ((v 4) ^ 3) + (-4 : ℝ) * (v 3 * (v 4) ^ 2) + (2 : ℝ) * ((v 3) ^ 2 * v 4) + (-8 : ℝ) * (v 2 * (v 4) ^ 2) + (8 : ℝ) * (v 2 * v 3 * v 4) + v 1 * h 1 = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork65, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (4 : ℝ) * (v 2 * v 3 * v 4 * h 1) + (-8 : ℝ) * (v 2 * v 3 * v 4 * h 0) + (-16 : ℝ) * ((v 2) ^ 2 * v 4 * h 0) = 0 := by
      linear_combination
        ((10 : ℝ) * (v 2 * v 4 * h 1) + (-2 : ℝ) * (v 2 * v 4 * h 0) + (-10 : ℝ) * (v 2 * v 3 * h 1) + (2 : ℝ) * (v 2 * v 3 * h 0) + (-32 : ℝ) * ((v 2) ^ 2 * h 1) + (8 : ℝ) * ((v 2) ^ 2 * h 0)) * g1 +
      ((-10 : ℝ) * (v 2 * h 1) + (2 : ℝ) * (v 2 * h 0)) * g2 +
      (v 4 + -(v 3) + (2 : ℝ) * (v 2)) * g3 +
      ((6 : ℝ) * (v 2 * v 4)) * g4 +
      ((-8 : ℝ) * ((v 2) ^ 2)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork65, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork65, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 2 * v 3 * v 4 * h 0) + v 1 * (v 4) ^ 2 * h 1 + -(v 1 * (v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 3 * v 4 * h 0) + v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) = 0 := by
      linear_combination
        (-((v 3) ^ 2 * h 1) + (v 3) ^ 2 * h 0 + (-4 : ℝ) * (v 2 * v 4 * h 0) + (4 : ℝ) * (v 2 * v 3 * h 0) + -(v 1 * v 4 * h 1) + v 1 * v 4 * h 0 + (2 : ℝ) * (v 1 * v 3 * h 1) + (-2 : ℝ) * (v 1 * v 3 * h 0)) * g1 +
      ((v 3) ^ 2 * h 1 + -((v 3) ^ 2 * h 0)) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork65, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : v 4 + -(v 3) + (-4 : ℝ) * (v 2) = 0 := by
      nlinarith [hg0]
    have g1 : v 4 + -(v 3) = 0 := by
      nlinarith [hg1]
    have g3 : -(v 4) + v 1 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork65, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 2 * (v 4) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * (v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (4 : ℝ) * (v 1 * v 2 * v 4 * h 0) = 0 := by
      linear_combination
        ((v 3) ^ 2 * h 0) * g0 +
      (-((v 3) ^ 2 * h 0) + (4 : ℝ) * (v 2 * v 4 * h 1) + (-8 : ℝ) * (v 2 * v 4 * h 0) + (-4 : ℝ) * (v 2 * v 3 * h 0) + (-4 : ℝ) * (v 1 * v 2 * h 1) + (4 : ℝ) * (v 1 * v 2 * h 0)) * g1 +
      ((-4 : ℝ) * (v 2 * v 3 * h 1) + (4 : ℝ) * (v 2 * v 3 * h 0)) * g3
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork65, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork65, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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

theorem cubicResidualNetwork65_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork65.toNetwork := by
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
  simp [cubicResidualNetwork65, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork65_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork65.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork65_jacobianNonzero
    cubicResidualNetwork65_fourCharts

end SmallCusp

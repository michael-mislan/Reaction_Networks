import proofs.SmallCusp.Obstruction.CubicDegeneracy
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

def cubicResidualNetwork116 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xy), (.xx, .xy), (.xy, .xx), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork116_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork116.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork116, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g2 : v 1 * v 3 + (-2 : ℝ) * (v 1 * v 2) + (4 : ℝ) * (v 0 * v 4) + v 0 * v 3 = 0 := by
      nlinarith [hdet]
    have g3 : (4 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (2 : ℝ) * (v 0 * (v 3) ^ 3) + (32 : ℝ) * (v 0 * v 2 * (v 4) ^ 2) + (16 : ℝ) * (v 0 * v 2 * v 3 * v 4) + (-2 : ℝ) * (v 0 * v 2 * (v 3) ^ 2) + (-16 : ℝ) * (v 0 * (v 2) ^ 2 * v 4) + (2 : ℝ) * (v 0 * v 1 * (v 3) ^ 2) + (16 : ℝ) * (v 0 * v 1 * v 2 * v 4) + (2 : ℝ) * (v 0 * (v 1) ^ 2 * v 2) + (-2 : ℝ) * ((v 0) ^ 2 * (v 3) ^ 2) + (-16 : ℝ) * ((v 0) ^ 2 * v 2 * v 4) + (-2 : ℝ) * ((v 0) ^ 2 * v 1 * v 3) + (-4 : ℝ) * ((v 0) ^ 3 * v 4) = 0 := by
      nlinarith [hfold]
    have g4 : (4 : ℝ) * (v 4 * h 1) + v 3 * h 1 + v 3 * h 0 + (-4 : ℝ) * ((v 3) ^ 2 * v 4) + (-2 : ℝ) * ((v 3) ^ 3) + (-2 : ℝ) * (v 2 * h 0) + (-32 : ℝ) * (v 2 * (v 4) ^ 2) + (-16 : ℝ) * (v 2 * v 3 * v 4) + (2 : ℝ) * (v 2 * (v 3) ^ 2) + (16 : ℝ) * ((v 2) ^ 2 * v 4) + v 1 * h 1 + (-2 : ℝ) * (v 1 * (v 3) ^ 2) + (-16 : ℝ) * (v 1 * v 2 * v 4) + (-2 : ℝ) * ((v 1) ^ 2 * v 2) + -(v 0 * h 0) + (2 : ℝ) * (v 0 * (v 3) ^ 2) + (16 : ℝ) * (v 0 * v 2 * v 4) + (2 : ℝ) * (v 0 * v 1 * v 3) + (4 : ℝ) * ((v 0) ^ 2 * v 4) = 0 := by
      nlinarith [hc0]
    have g5 : (-4 : ℝ) * (v 4 * h 1) + -(v 3 * h 1) + -(v 3 * h 0) + (4 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + (2 : ℝ) * (v 2 * h 0) + (32 : ℝ) * (v 2 * (v 4) ^ 2) + (16 : ℝ) * (v 2 * v 3 * v 4) + (-2 : ℝ) * (v 2 * (v 3) ^ 2) + (-16 : ℝ) * ((v 2) ^ 2 * v 4) + (2 : ℝ) * (v 1 * (v 3) ^ 2) + (16 : ℝ) * (v 1 * v 2 * v 4) + (2 : ℝ) * ((v 1) ^ 2 * v 2) + (-2 : ℝ) * (v 0 * (v 3) ^ 2) + (-16 : ℝ) * (v 0 * v 2 * v 4) + (-2 : ℝ) * (v 0 * v 1 * v 3) + (-4 : ℝ) * ((v 0) ^ 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork116, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 + (-8 : ℝ) * (v 0 * v 2 * v 4 * h 1) + (8 : ℝ) * (v 0 * v 2 * v 4 * h 0) + -(v 0 * v 1 * v 3 * h 1) + (2 : ℝ) * (v 0 * v 1 * v 2 * h 0) + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) + -((v 0) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        (-(v 3 * v 4 * h 1) + -((v 2) ^ 2 * h 1) + -(v 0 * v 3 * h 1) + v 0 * v 3 * h 0) * g0 +
      (-(v 3 * v 4 * h 1) + -((v 2) ^ 2 * h 1) + (-2 : ℝ) * (v 1 * v 4 * h 1) + (-2 : ℝ) * (v 0 * v 4 * h 1) + (2 : ℝ) * (v 0 * v 4 * h 0) + -(v 0 * v 2 * h 1) + (-3 : ℝ) * (v 0 * v 2 * h 0) + (-2 : ℝ) * (v 0 * v 1 * h 1)) * g1 +
      (-(v 4 * h 1) + -(v 0 * h 1)) * g2 +
      ((-2 : ℝ) * (v 2) + -(v 1)) * g3 +
      ((-4 : ℝ) * ((v 4) ^ 2) + (v 2) ^ 2) * g4 +
      ((-4 : ℝ) * ((v 4) ^ 2) + (v 2) ^ 2 + (2 : ℝ) * (v 0 * v 2) + v 0 * v 1) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork116, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : -(v 3) + (2 : ℝ) * (v 2) = 0 := by
      nlinarith [hg1]
    have g2 : (2 : ℝ) * (v 4) + v 3 + -(v 2) + v 1 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : (-2 : ℝ) * (v 4) + -(v 3) + v 2 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork116, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + (8 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (v 1) ^ 2 * v 3 * h 1 + (-2 : ℝ) * ((v 1) ^ 2 * v 2 * h 0) + (4 : ℝ) * (v 0 * v 1 * v 4 * h 1) + v 0 * v 1 * v 3 * h 0 = 0 := by
      linear_combination
        ((4 : ℝ) * (v 1 * v 4 * h 1) + v 1 * v 3 * h 1 + v 1 * v 3 * h 0 + (-2 : ℝ) * (v 1 * v 2 * h 0) + (v 1) ^ 2 * h 1 + -(v 0 * v 1 * h 0)) * g1 +
      ((-4 : ℝ) * (v 1 * v 4 * h 1) + (-2 : ℝ) * (v 1 * v 2 * h 0)) * g2 +
      ((-4 : ℝ) * (v 1 * v 4 * h 1) + (-2 : ℝ) * (v 1 * v 3 * h 1) + (2 : ℝ) * (v 1 * v 2 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * h 1)) * g3
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork116, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : (4 : ℝ) * (v 4) + v 3 + v 1 = 0 := by
      nlinarith [hg1]
    have g2 : (2 : ℝ) * (v 4) + v 3 + -(v 2) + v 1 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : (-2 : ℝ) * (v 4) + -(v 3) + v 2 = 0 := by
      nlinarith [heq1]
    have g4 : v 1 * v 3 + (-2 : ℝ) * (v 1 * v 2) + (4 : ℝ) * (v 0 * v 4) + v 0 * v 3 = 0 := by
      nlinarith [hdet]
    have g5 : (4 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (2 : ℝ) * (v 0 * (v 3) ^ 3) + (32 : ℝ) * (v 0 * v 2 * (v 4) ^ 2) + (16 : ℝ) * (v 0 * v 2 * v 3 * v 4) + (-2 : ℝ) * (v 0 * v 2 * (v 3) ^ 2) + (-16 : ℝ) * (v 0 * (v 2) ^ 2 * v 4) = 0 := by
      nlinarith [hfold]
    have g7 : (-4 : ℝ) * (v 4 * h 1) + -(v 3 * h 1) + -(v 3 * h 0) + (4 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + (2 : ℝ) * (v 2 * h 0) + (32 : ℝ) * (v 2 * (v 4) ^ 2) + (16 : ℝ) * (v 2 * v 3 * v 4) + (-2 : ℝ) * (v 2 * (v 3) ^ 2) + (-16 : ℝ) * ((v 2) ^ 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork116, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 0 * (v 3) ^ 2 * h 1 + -(v 0 * (v 3) ^ 2 * h 0) + (8 : ℝ) * (v 0 * v 2 * v 4 * h 1) + (-8 : ℝ) * (v 0 * v 2 * v 4 * h 0) = 0 := by
      linear_combination
        ((-2 : ℝ) * ((v 3) ^ 2 * h 1) + -(v 1 * v 3 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * h 0) + v 0 * v 3 * h 0 + (-2 : ℝ) * (v 0 * v 2 * h 0) + v 0 * v 1 * h 0) * g0 +
      ((-2 : ℝ) * ((v 3) ^ 2 * h 1) + (2 : ℝ) * (v 1 * v 3 * h 0) + (-4 : ℝ) * (v 1 * v 2 * h 0) + (4 : ℝ) * (v 0 * v 4 * h 0) + -((v 0) ^ 2 * h 0)) * g1 +
      ((-4 : ℝ) * (v 3 * v 4 * h 1) + (2 : ℝ) * (v 2 * v 3 * h 1) + (-2 : ℝ) * (v 0 * v 1 * h 0)) * g2 +
      ((-4 : ℝ) * (v 3 * v 4 * h 1) + (-4 : ℝ) * ((v 3) ^ 2 * h 1) + (2 : ℝ) * (v 2 * v 3 * h 1) + (-2 : ℝ) * (v 1 * v 3 * h 1) + (-8 : ℝ) * (v 0 * v 4 * h 0) + (-2 : ℝ) * ((v 0) ^ 2 * h 0)) * g3 +
      ((-8 : ℝ) * (v 4 * h 0) + -(v 3 * h 0)) * g4 +
      (-(v 3) + (2 : ℝ) * (v 2)) * g5 +
      (v 0 * v 3 + (-2 : ℝ) * (v 0 * v 2)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork116, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g2 : -(v 3) + (2 : ℝ) * (v 2) = 0 := by
      nlinarith [hg2]
    have g4 : (-2 : ℝ) * (v 4) + -(v 3) + v 2 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork116, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -(v 1 * (v 3) ^ 2 * h 1) + v 1 * (v 3) ^ 2 * h 0 + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (8 : ℝ) * (v 1 * v 2 * v 4 * h 0) = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 1 * v 4 * h 1) + -(v 1 * v 3 * h 1) + -(v 1 * v 3 * h 0) + (2 : ℝ) * (v 1 * v 2 * h 0)) * g2 +
      ((2 : ℝ) * (v 1 * v 3 * h 1) + (-4 : ℝ) * (v 1 * v 2 * h 0)) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork116_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork116.toNetwork := by
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
  simp [cubicResidualNetwork116, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork116_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork116.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork116_jacobianNonzero
    cubicResidualNetwork116_fourCharts

def cubicResidualNetwork117 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xy), (.xx, .xy), (.xy, .yy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork117_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork117.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork117, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g2 : -(v 1 * v 3) + (-2 : ℝ) * (v 1 * v 2) + (4 : ℝ) * (v 0 * v 4) + -(v 0 * v 3) = 0 := by
      nlinarith [hdet]
    have g3 : (4 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (-2 : ℝ) * (v 0 * (v 3) ^ 3) + (32 : ℝ) * (v 0 * v 2 * (v 4) ^ 2) + (-16 : ℝ) * (v 0 * v 2 * v 3 * v 4) + (-2 : ℝ) * (v 0 * v 2 * (v 3) ^ 2) + (-16 : ℝ) * (v 0 * (v 2) ^ 2 * v 4) + (2 : ℝ) * (v 0 * v 1 * (v 3) ^ 2) + (16 : ℝ) * (v 0 * v 1 * v 2 * v 4) + (2 : ℝ) * (v 0 * (v 1) ^ 2 * v 2) + (-2 : ℝ) * ((v 0) ^ 2 * (v 3) ^ 2) + (-16 : ℝ) * ((v 0) ^ 2 * v 2 * v 4) + (2 : ℝ) * ((v 0) ^ 2 * v 1 * v 3) + (-4 : ℝ) * ((v 0) ^ 3 * v 4) = 0 := by
      nlinarith [hfold]
    have g4 : (4 : ℝ) * (v 4 * h 1) + -(v 3 * h 1) + -(v 3 * h 0) + (-4 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + (-2 : ℝ) * (v 2 * h 0) + (-32 : ℝ) * (v 2 * (v 4) ^ 2) + (16 : ℝ) * (v 2 * v 3 * v 4) + (2 : ℝ) * (v 2 * (v 3) ^ 2) + (16 : ℝ) * ((v 2) ^ 2 * v 4) + v 1 * h 1 + (-2 : ℝ) * (v 1 * (v 3) ^ 2) + (-16 : ℝ) * (v 1 * v 2 * v 4) + (-2 : ℝ) * ((v 1) ^ 2 * v 2) + -(v 0 * h 0) + (2 : ℝ) * (v 0 * (v 3) ^ 2) + (16 : ℝ) * (v 0 * v 2 * v 4) + (-2 : ℝ) * (v 0 * v 1 * v 3) + (4 : ℝ) * ((v 0) ^ 2 * v 4) = 0 := by
      nlinarith [hc0]
    have g5 : (-4 : ℝ) * (v 4 * h 1) + v 3 * h 1 + v 3 * h 0 + (4 : ℝ) * ((v 3) ^ 2 * v 4) + (-2 : ℝ) * ((v 3) ^ 3) + (2 : ℝ) * (v 2 * h 0) + (32 : ℝ) * (v 2 * (v 4) ^ 2) + (-16 : ℝ) * (v 2 * v 3 * v 4) + (-2 : ℝ) * (v 2 * (v 3) ^ 2) + (-16 : ℝ) * ((v 2) ^ 2 * v 4) + (2 : ℝ) * (v 1 * (v 3) ^ 2) + (16 : ℝ) * (v 1 * v 2 * v 4) + (2 : ℝ) * ((v 1) ^ 2 * v 2) + (-2 : ℝ) * (v 0 * (v 3) ^ 2) + (-16 : ℝ) * (v 0 * v 2 * v 4) + (2 : ℝ) * (v 0 * v 1 * v 3) + (-4 : ℝ) * ((v 0) ^ 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork117, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 + (-8 : ℝ) * (v 0 * v 2 * v 4 * h 1) + (8 : ℝ) * (v 0 * v 2 * v 4 * h 0) + v 0 * v 1 * v 3 * h 1 + (2 : ℝ) * (v 0 * v 1 * v 2 * h 0) + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) + (v 0) ^ 2 * v 3 * h 0 = 0 := by
      linear_combination
        (-(v 3 * v 4 * h 1) + (v 2) ^ 2 * h 1 + v 0 * v 3 * h 1 + -(v 0 * v 3 * h 0)) * g0 +
      (-(v 3 * v 4 * h 1) + (v 2) ^ 2 * h 1 + ((-1 : ℝ) / 2) * (v 1 * v 3 * h 1) + (-6 : ℝ) * (v 0 * v 4 * h 1) + ((1 : ℝ) / 2) * (v 0 * v 3 * h 0) + v 0 * v 2 * h 1 + -(v 0 * v 2 * h 0) + (-2 : ℝ) * (v 0 * v 1 * h 1)) * g1 +
      (-(v 0 * h 1)) * g2 +
      ((-3 : ℝ) * (v 4) + -(v 1)) * g3 +
      (((1 : ℝ) / 2) * ((v 3) ^ 2) + ((1 : ℝ) / 2) * (v 2 * v 3) + -((v 2) ^ 2)) * g4 +
      (((1 : ℝ) / 2) * ((v 3) ^ 2) + ((1 : ℝ) / 2) * (v 2 * v 3) + -((v 2) ^ 2) + (3 : ℝ) * (v 0 * v 4) + v 0 * v 1) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork117, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : v 3 + (2 : ℝ) * (v 2) = 0 := by
      nlinarith [hg1]
    have g2 : (2 : ℝ) * (v 4) + -(v 3) + -(v 2) + v 1 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : (-2 : ℝ) * (v 4) + v 3 + v 2 = 0 := by
      nlinarith [heq1]
    have g4 : -(v 1 * v 3) + (-2 : ℝ) * (v 1 * v 2) + (4 : ℝ) * (v 0 * v 4) + -(v 0 * v 3) = 0 := by
      nlinarith [hdet]
    simp [-mul_eq_zero, cubicResidualNetwork117, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + (8 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 0) + -((v 1) ^ 2 * v 3 * h 1) + (-2 : ℝ) * ((v 1) ^ 2 * v 2 * h 0) + (4 : ℝ) * (v 0 * v 1 * v 4 * h 1) + -(v 0 * v 1 * v 3 * h 0) = 0 := by
      linear_combination
        ((4 : ℝ) * (v 1 * v 4 * h 1) + -(v 1 * v 3 * h 1) + -(v 1 * v 3 * h 0) + (-2 : ℝ) * (v 1 * v 2 * h 0) + (v 1) ^ 2 * h 1 + -(v 0 * v 1 * h 0)) * g1 +
      (-(v 1 * v 3 * h 1) + (-2 : ℝ) * (v 1 * v 2 * h 0)) * g2 +
      (v 1 * v 3 * h 1 + (2 : ℝ) * (v 1 * v 2 * h 0)) * g3 +
      (v 1 * h 1) * g4
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork117, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : (4 : ℝ) * (v 4) + -(v 3) + v 1 = 0 := by
      nlinarith [hg1]
    have g2 : (2 : ℝ) * (v 4) + -(v 3) + -(v 2) + v 1 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : (-2 : ℝ) * (v 4) + v 3 + v 2 = 0 := by
      nlinarith [heq1]
    have g5 : (4 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (-2 : ℝ) * (v 0 * (v 3) ^ 3) + (32 : ℝ) * (v 0 * v 2 * (v 4) ^ 2) + (-16 : ℝ) * (v 0 * v 2 * v 3 * v 4) + (-2 : ℝ) * (v 0 * v 2 * (v 3) ^ 2) + (-16 : ℝ) * (v 0 * (v 2) ^ 2 * v 4) = 0 := by
      nlinarith [hfold]
    have g7 : (-4 : ℝ) * (v 4 * h 1) + v 3 * h 1 + v 3 * h 0 + (4 : ℝ) * ((v 3) ^ 2 * v 4) + (-2 : ℝ) * ((v 3) ^ 3) + (2 : ℝ) * (v 2 * h 0) + (32 : ℝ) * (v 2 * (v 4) ^ 2) + (-16 : ℝ) * (v 2 * v 3 * v 4) + (-2 : ℝ) * (v 2 * (v 3) ^ 2) + (-16 : ℝ) * ((v 2) ^ 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork117, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 0 * (v 3) ^ 2 * h 1 + -(v 0 * (v 3) ^ 2 * h 0) + (8 : ℝ) * (v 0 * v 2 * v 4 * h 1) + (-8 : ℝ) * (v 0 * v 2 * v 4 * h 0) = 0 := by
      linear_combination
        ((-16 : ℝ) * ((v 4) ^ 2 * h 1) + (16 : ℝ) * (v 3 * v 4 * h 1) + (8 : ℝ) * (v 2 * v 4 * h 0) + (-4 : ℝ) * (v 2 * v 3 * h 0) + (4 : ℝ) * ((v 2) ^ 2 * h 1) + (-4 : ℝ) * ((v 2) ^ 2 * h 0) + (v 1) ^ 2 * h 1 + (-4 : ℝ) * (v 0 * v 2 * h 1)) * g0 +
      ((4 : ℝ) * ((v 3) ^ 2 * h 1) + (-8 : ℝ) * (v 2 * v 4 * h 1) + (4 : ℝ) * (v 2 * v 3 * h 1) + (4 : ℝ) * ((v 2) ^ 2 * h 1) + (-4 : ℝ) * (v 0 * v 4 * h 1) + (2 : ℝ) * (v 0 * v 3 * h 1) + (-2 : ℝ) * (v 0 * v 2 * h 1) + v 0 * v 1 * h 1) * g1 +
      ((-4 : ℝ) * ((v 3) ^ 2 * h 1) + v 1 * v 3 * h 1 + (2 : ℝ) * (v 1 * v 2 * h 1) + (4 : ℝ) * (v 0 * v 2 * h 1)) * g2 +
      ((8 : ℝ) * (v 3 * v 4 * h 1) + (-4 : ℝ) * (v 2 * v 3 * h 0) + (8 : ℝ) * ((v 2) ^ 2 * h 1) + (-8 : ℝ) * ((v 2) ^ 2 * h 0) + v 1 * v 3 * h 1 + (-2 : ℝ) * (v 1 * v 2 * h 1)) * g3 +
      (v 3 + (2 : ℝ) * (v 2)) * g5 +
      (-(v 0 * v 3) + (-2 : ℝ) * (v 0 * v 2)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork117, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g2 : v 3 + (2 : ℝ) * (v 2) = 0 := by
      nlinarith [hg2]
    have g4 : (-2 : ℝ) * (v 4) + v 3 + v 2 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork117, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -(v 1 * (v 3) ^ 2 * h 1) + v 1 * (v 3) ^ 2 * h 0 + (-8 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (8 : ℝ) * (v 1 * v 2 * v 4 * h 0) = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 1 * v 4 * h 1) + v 1 * v 3 * h 1 + v 1 * v 3 * h 0 + (2 : ℝ) * (v 1 * v 2 * h 0)) * g2 +
      ((-2 : ℝ) * (v 1 * v 3 * h 1) + (-4 : ℝ) * (v 1 * v 2 * h 0)) * g4
    nlinarith [hcertificate]

theorem cubicResidualNetwork117_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork117.toNetwork := by
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
  simp [cubicResidualNetwork117, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork117_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork117.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork117_jacobianNonzero
    cubicResidualNetwork117_fourCharts

def cubicResidualNetwork118 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xy), (.xx, .xy), (.yy, .xx), (.yy, .xy)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork118_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork118.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork118, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : v 4 + (2 : ℝ) * (v 3) + -(v 2) + v 1 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g1 : -(v 4) + (-2 : ℝ) * (v 3) + v 2 = 0 := by
      nlinarith [heq1]
    have g2 : (-2 : ℝ) * (v 1 * v 2) + (2 : ℝ) * (v 0 * v 4) + (4 : ℝ) * (v 0 * v 3) = 0 := by
      nlinarith [hdet]
    have g3 : (8 : ℝ) * (v 0 * v 2 * (v 4) ^ 2) + (32 : ℝ) * (v 0 * v 2 * v 3 * v 4) + (32 : ℝ) * (v 0 * v 2 * (v 3) ^ 2) + (-8 : ℝ) * (v 0 * (v 2) ^ 2 * v 4) + (-16 : ℝ) * (v 0 * (v 2) ^ 2 * v 3) + (8 : ℝ) * (v 0 * v 1 * v 2 * v 4) + (16 : ℝ) * (v 0 * v 1 * v 2 * v 3) + (2 : ℝ) * (v 0 * (v 1) ^ 2 * v 2) + (-8 : ℝ) * ((v 0) ^ 2 * v 2 * v 4) + (-16 : ℝ) * ((v 0) ^ 2 * v 2 * v 3) + (-2 : ℝ) * ((v 0) ^ 3 * v 4) + (-4 : ℝ) * ((v 0) ^ 3 * v 3) = 0 := by
      nlinarith [hfold]
    have g5 : (-2 : ℝ) * (v 4 * h 1) + (-4 : ℝ) * (v 3 * h 1) + (2 : ℝ) * (v 2 * h 0) + (8 : ℝ) * (v 2 * (v 4) ^ 2) + (32 : ℝ) * (v 2 * v 3 * v 4) + (32 : ℝ) * (v 2 * (v 3) ^ 2) + (-8 : ℝ) * ((v 2) ^ 2 * v 4) + (-16 : ℝ) * ((v 2) ^ 2 * v 3) + (8 : ℝ) * (v 1 * v 2 * v 4) + (16 : ℝ) * (v 1 * v 2 * v 3) + (2 : ℝ) * ((v 1) ^ 2 * v 2) + (-8 : ℝ) * (v 0 * v 2 * v 4) + (-16 : ℝ) * (v 0 * v 2 * v 3) + (-2 : ℝ) * ((v 0) ^ 2 * v 4) + (-4 : ℝ) * ((v 0) ^ 2 * v 3) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork118, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * (v 0 * v 2 * v 4 * h 1) + (4 : ℝ) * (v 0 * v 2 * v 4 * h 0) + (-8 : ℝ) * (v 0 * v 2 * v 3 * h 1) + (8 : ℝ) * (v 0 * v 2 * v 3 * h 0) + (2 : ℝ) * (v 0 * v 1 * v 2 * h 0) + (-2 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) + (-4 : ℝ) * ((v 0) ^ 2 * v 3 * h 1) = 0 := by
      linear_combination
        ((-2 : ℝ) * (v 1 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 3 * h 1) + (2 : ℝ) * (v 1 * v 2 * h 1)) * g0 +
      ((-2 : ℝ) * (v 1 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 3 * h 1) + (-2 : ℝ) * (v 1 * v 2 * h 1) + (-2 : ℝ) * ((v 1) ^ 2 * h 1)) * g1 +
      ((-2 : ℝ) * (v 2 * h 1) + (2 : ℝ) * (v 2 * h 0) + -(v 0 * h 1) + (8 : ℝ) * (v 2 * (v 4) ^ 2) + (32 : ℝ) * (v 2 * v 3 * v 4) + (32 : ℝ) * (v 2 * (v 3) ^ 2) + (-8 : ℝ) * ((v 2) ^ 2 * v 4) + (-16 : ℝ) * ((v 2) ^ 2 * v 3) + (8 : ℝ) * (v 1 * v 2 * v 4) + (16 : ℝ) * (v 1 * v 2 * v 3) + (2 : ℝ) * ((v 1) ^ 2 * v 2) + (-8 : ℝ) * (v 0 * v 2 * v 4) + (-16 : ℝ) * (v 0 * v 2 * v 3) + (-2 : ℝ) * ((v 0) ^ 2 * v 4) + (-4 : ℝ) * ((v 0) ^ 2 * v 3)) * g2 +
      ((-2 : ℝ) * (v 4) + (-4 : ℝ) * (v 3) + -(v 1)) * g3 +
      ((2 : ℝ) * (v 1 * v 2) + v 0 * v 1) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork118, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : (-2 : ℝ) * (v 2) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : (2 : ℝ) * (v 2) = 0 := by
      nlinarith [hg1]
    simp [-mul_eq_zero, cubicResidualNetwork118, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (8 : ℝ) * (v 1 * v 2 * v 3 * h 1) + (-8 : ℝ) * (v 1 * v 2 * v 3 * h 0) + (-2 : ℝ) * ((v 1) ^ 2 * v 2 * h 0) + (2 : ℝ) * (v 0 * v 1 * v 4 * h 1) + (4 : ℝ) * (v 0 * v 1 * v 3 * h 1) = 0 := by
      linear_combination
        ((-2 : ℝ) * (v 1 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 3 * h 1)) * g0 +
      ((-2 : ℝ) * (v 1 * v 4 * h 0) + (-4 : ℝ) * (v 1 * v 3 * h 0) + -((v 1) ^ 2 * h 0)) * g1
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork118, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : (-2 : ℝ) * (v 2) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : (2 : ℝ) * (v 4) + (4 : ℝ) * (v 3) + v 1 = 0 := by
      nlinarith [hg1]
    have g2 : v 4 + (2 : ℝ) * (v 3) + -(v 2) + v 1 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : -(v 4) + (-2 : ℝ) * (v 3) + v 2 = 0 := by
      nlinarith [heq1]
    have g4 : (-2 : ℝ) * (v 1 * v 2) + (2 : ℝ) * (v 0 * v 4) + (4 : ℝ) * (v 0 * v 3) = 0 := by
      nlinarith [hdet]
    have g6 : (2 : ℝ) * (v 4 * h 1) + (4 : ℝ) * (v 3 * h 1) + (-2 : ℝ) * (v 2 * h 0) + (-8 : ℝ) * (v 2 * (v 4) ^ 2) + (-32 : ℝ) * (v 2 * v 3 * v 4) + (-32 : ℝ) * (v 2 * (v 3) ^ 2) + (8 : ℝ) * ((v 2) ^ 2 * v 4) + (16 : ℝ) * ((v 2) ^ 2 * v 3) + v 1 * h 1 + -(v 0 * h 0) = 0 := by
      nlinarith [hc0]
    have g7 : (-2 : ℝ) * (v 4 * h 1) + (-4 : ℝ) * (v 3 * h 1) + (2 : ℝ) * (v 2 * h 0) + (8 : ℝ) * (v 2 * (v 4) ^ 2) + (32 : ℝ) * (v 2 * v 3 * v 4) + (32 : ℝ) * (v 2 * (v 3) ^ 2) + (-8 : ℝ) * ((v 2) ^ 2 * v 4) + (-16 : ℝ) * ((v 2) ^ 2 * v 3) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork118, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (4 : ℝ) * (v 0 * v 2 * v 4 * h 1) + (-4 : ℝ) * (v 0 * v 2 * v 4 * h 0) + (8 : ℝ) * (v 0 * v 2 * v 3 * h 1) + (-8 : ℝ) * (v 0 * v 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((-16 : ℝ) * ((v 3) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 3 * h 1) + (-4 : ℝ) * (v 1 * v 3 * h 0) + (2 : ℝ) * (v 1 * v 2 * h 1) + -((v 1) ^ 2 * h 0) + (-2 : ℝ) * (v 0 * v 4 * h 1) + (-4 : ℝ) * (v 0 * v 3 * h 1) + (8 : ℝ) * (v 0 * v 3 * h 0) + -(v 0 * v 1 * h 1) + (v 0) ^ 2 * h 1) * g0 +
      ((-16 : ℝ) * ((v 3) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 4 * h 0) + -((v 1) ^ 2 * h 1)) * g1 +
      ((4 : ℝ) * ((v 4) ^ 2 * h 0) + (-4 : ℝ) * (v 1 * v 3 * h 0) + (-8 : ℝ) * (v 0 * v 3 * h 0) + -((v 0) ^ 2 * h 1)) * g2 +
      ((4 : ℝ) * ((v 4) ^ 2 * h 0) + (-32 : ℝ) * ((v 3) ^ 2 * h 0) + (-12 : ℝ) * (v 1 * v 3 * h 0) + (4 : ℝ) * (v 1 * v 2 * h 1) + (-2 : ℝ) * ((v 1) ^ 2 * h 1) + (-2 : ℝ) * ((v 1) ^ 2 * h 0) + (-4 : ℝ) * (v 0 * v 4 * h 0) + (v 0) ^ 2 * h 1) * g3 +
      (-(v 1 * h 1)) * g4 +
      ((v 1) ^ 2) * g6 +
      ((v 1) ^ 2) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork118, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g2 : (2 : ℝ) * (v 2) = 0 := by
      nlinarith [hg2]
    simp [-mul_eq_zero, cubicResidualNetwork118, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * (v 1 * v 2 * v 4 * h 1) + (4 : ℝ) * (v 1 * v 2 * v 4 * h 0) + (-8 : ℝ) * (v 1 * v 2 * v 3 * h 1) + (8 : ℝ) * (v 1 * v 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((-2 : ℝ) * (v 1 * v 4 * h 1) + (2 : ℝ) * (v 1 * v 4 * h 0) + (-4 : ℝ) * (v 1 * v 3 * h 1) + (4 : ℝ) * (v 1 * v 3 * h 0)) * g2
    nlinarith [hcertificate]

theorem cubicResidualNetwork118_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork118.toNetwork := by
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
  simp [cubicResidualNetwork118, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork118_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork118.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork118_jacobianNonzero
    cubicResidualNetwork118_fourCharts

def cubicResidualNetwork119 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xy, .yy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork119_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork119.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork119, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : (2 : ℝ) * (v 4) + -(v 3) + v 1 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g1 : (-2 : ℝ) * (v 4) + v 3 + v 2 + -(v 1) = 0 := by
      nlinarith [heq1]
    have g2 : -(v 2 * v 3) + (4 : ℝ) * (v 0 * v 4) + -(v 0 * v 3) + -(v 0 * v 2) + v 0 * v 1 = 0 := by
      nlinarith [hdet]
    have g3 : (4 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (-2 : ℝ) * (v 0 * (v 3) ^ 3) + (2 : ℝ) * (v 0 * v 1 * (v 3) ^ 2) + (-2 : ℝ) * ((v 0) ^ 2 * (v 3) ^ 2) + (2 : ℝ) * ((v 0) ^ 2 * v 1 * v 3) + (-4 : ℝ) * ((v 0) ^ 3 * v 4) = 0 := by
      nlinarith [hfold]
    have g4 : (4 : ℝ) * (v 4 * h 1) + -(v 3 * h 1) + -(v 3 * h 0) + (-4 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + v 1 * h 1 + (-2 : ℝ) * (v 1 * (v 3) ^ 2) + -(v 0 * h 0) + (2 : ℝ) * (v 0 * (v 3) ^ 2) + (-2 : ℝ) * (v 0 * v 1 * v 3) + (4 : ℝ) * ((v 0) ^ 2 * v 4) = 0 := by
      nlinarith [hc0]
    simp [-mul_eq_zero, cubicResidualNetwork119, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 + v 0 * v 1 * v 3 * h 1 + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) + (v 0) ^ 2 * v 3 * h 0 = 0 := by
      linear_combination
        ((-4 : ℝ) * ((v 4) ^ 2 * h 0) + (2 : ℝ) * (v 3 * v 4 * h 1) + ((3 : ℝ) / 2) * (v 2 * v 3 * h 0) + (v 2) ^ 2 * h 0 + (-4 : ℝ) * (v 1 * v 4 * h 0) + -((v 1) ^ 2 * h 0) + v 0 * v 3 * h 1 + ((-1 : ℝ) / 2) * (v 0 * v 3 * h 0) + v 0 * v 2 * h 1 + ((1 : ℝ) / 2) * (v 0 * v 2 * h 0) + -(v 0 * v 1 * h 1) + ((-1 : ℝ) / 2) * (v 0 * v 1 * h 0)) * g0 +
      ((-4 : ℝ) * ((v 4) ^ 2 * h 0) + (2 : ℝ) * (v 3 * v 4 * h 1) + (-2 : ℝ) * (v 2 * v 4 * h 0) + v 2 * v 3 * h 0 + (-4 : ℝ) * (v 1 * v 4 * h 0) + -(v 1 * v 2 * h 0) + -((v 1) ^ 2 * h 0) + v 0 * v 2 * h 0 + -(v 0 * v 1 * h 1)) * g1 +
      ((2 : ℝ) * (v 4 * h 1) + -(v 4 * h 0) + ((-1 : ℝ) / 2) * (v 3 * h 0) + ((-1 : ℝ) / 2) * (v 1 * h 0) + -(v 0 * h 1) + ((-1 : ℝ) / 2) * (v 0 * h 0)) * g2 +
      ((-2 : ℝ) * (v 4)) * g3 +
      ((-2 : ℝ) * (v 0 * v 4)) * g4
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork119, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : v 3 = 0 := by
      nlinarith [hg1]
    simp [-mul_eq_zero, cubicResidualNetwork119, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 2 * (v 3) ^ 2 * h 1 + -(v 2 * (v 3) ^ 2 * h 0) + -(v 1 * v 2 * v 3 * h 1) + (4 : ℝ) * (v 0 * v 2 * v 4 * h 1) + -(v 0 * v 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 2 * v 4 * h 1)) * g0 +
      ((-4 : ℝ) * (v 2 * v 4 * h 1) + v 2 * v 3 * h 1 + -(v 2 * v 3 * h 0) + -(v 1 * v 2 * h 1) + -(v 0 * v 2 * h 0)) * g1
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork119, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : (4 : ℝ) * (v 4) + -(v 3) + v 1 = 0 := by
      nlinarith [hg1]
    have g2 : (2 : ℝ) * (v 4) + -(v 3) + v 1 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : (-2 : ℝ) * (v 4) + v 3 + v 2 + -(v 1) = 0 := by
      nlinarith [heq1]
    have g6 : (4 : ℝ) * (v 4 * h 1) + -(v 3 * h 1) + -(v 3 * h 0) + (-4 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + (2 : ℝ) * (v 2 * (v 3) ^ 2) + v 1 * h 1 + (-2 : ℝ) * (v 1 * (v 3) ^ 2) + -(v 0 * h 0) = 0 := by
      nlinarith [hc0]
    have g7 : (-4 : ℝ) * (v 4 * h 1) + v 3 * h 1 + v 3 * h 0 + (4 : ℝ) * ((v 3) ^ 2 * v 4) + (-2 : ℝ) * ((v 3) ^ 3) + v 2 * h 1 + (-2 : ℝ) * (v 2 * (v 3) ^ 2) + -(v 1 * h 1) + (2 : ℝ) * (v 1 * (v 3) ^ 2) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork119, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 0 * (v 3) ^ 2 * h 1 + -(v 0 * (v 3) ^ 2 * h 0) + v 0 * v 2 * v 3 * h 1 + -(v 0 * v 1 * v 3 * h 1) = 0 := by
      linear_combination
        (-((v 3) ^ 2 * h 1) + -((v 3) ^ 2 * h 0) + (-4 : ℝ) * (v 2 * v 4 * h 1) + -(v 2 * v 3 * h 1) + v 1 * v 3 * h 1 + v 1 * v 3 * h 0 + (-2 : ℝ) * (v 1 * v 2 * h 1) + (2 : ℝ) * (v 0 * v 2 * h 1)) * g0 +
      (-((v 3) ^ 2 * h 1) + -((v 3) ^ 2 * h 0) + -(v 2 * v 3 * h 1)) * g1 +
      ((2 : ℝ) * ((v 3) ^ 2 * h 0) + (-2 : ℝ) * (v 0 * v 2 * h 1)) * g2 +
      ((-2 : ℝ) * ((v 3) ^ 2 * h 1)) * g3 +
      (-(v 1 * v 3)) * g6 +
      (-(v 1 * v 3)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork119, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork119, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -(v 2 * (v 3) ^ 2 * h 1) + v 2 * (v 3) ^ 2 * h 0 + -((v 2) ^ 2 * v 3 * h 1) + v 1 * v 2 * v 3 * h 1 = 0 := by
      linear_combination
        (-(v 2 * v 3 * h 1) + v 2 * v 3 * h 0 + -((v 2) ^ 2 * h 1) + v 1 * v 2 * h 1) * g2
    nlinarith [hcertificate]

theorem cubicResidualNetwork119_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork119.toNetwork := by
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
  simp [cubicResidualNetwork119, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork119_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork119.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork119_jacobianNonzero
    cubicResidualNetwork119_fourCharts

def cubicResidualNetwork120 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xy, .yy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork120_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork120.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork120, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : (2 : ℝ) * (v 4) + -(v 3) + (2 : ℝ) * (v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g1 : (-2 : ℝ) * (v 4) + v 3 + v 2 + -(v 1) = 0 := by
      nlinarith [heq1]
    have g2 : -(v 2 * v 3) + -(v 1 * v 3) + (4 : ℝ) * (v 0 * v 4) + -(v 0 * v 3) + -(v 0 * v 2) + v 0 * v 1 = 0 := by
      nlinarith [hdet]
    have g3 : (4 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (-2 : ℝ) * (v 0 * (v 3) ^ 3) + (4 : ℝ) * (v 0 * v 1 * (v 3) ^ 2) + (-2 : ℝ) * ((v 0) ^ 2 * (v 3) ^ 2) + (4 : ℝ) * ((v 0) ^ 2 * v 1 * v 3) + (-4 : ℝ) * ((v 0) ^ 3 * v 4) = 0 := by
      nlinarith [hfold]
    have g4 : (4 : ℝ) * (v 4 * h 1) + -(v 3 * h 1) + -(v 3 * h 0) + (-4 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + (2 : ℝ) * (v 1 * h 1) + (-4 : ℝ) * (v 1 * (v 3) ^ 2) + -(v 0 * h 0) + (2 : ℝ) * (v 0 * (v 3) ^ 2) + (-4 : ℝ) * (v 0 * v 1 * v 3) + (4 : ℝ) * ((v 0) ^ 2 * v 4) = 0 := by
      nlinarith [hc0]
    have g5 : (-4 : ℝ) * (v 4 * h 1) + v 3 * h 1 + v 3 * h 0 + (4 : ℝ) * ((v 3) ^ 2 * v 4) + (-2 : ℝ) * ((v 3) ^ 3) + v 2 * h 1 + -(v 1 * h 1) + (4 : ℝ) * (v 1 * (v 3) ^ 2) + (-2 : ℝ) * (v 0 * (v 3) ^ 2) + (4 : ℝ) * (v 0 * v 1 * v 3) + (-4 : ℝ) * ((v 0) ^ 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork120, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 + (2 : ℝ) * (v 0 * v 1 * v 3 * h 1) + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) + (v 0) ^ 2 * v 3 * h 0 = 0 := by
      linear_combination
        ((-4 : ℝ) * ((v 4) ^ 2 * h 1) + (6 : ℝ) * (v 3 * v 4 * h 1) + (-2 : ℝ) * ((v 3) ^ 2 * h 0) + (4 : ℝ) * (v 2 * v 4 * h 1) + -(v 1 * v 2 * h 1) + -((v 1) ^ 2 * h 1) + (4 : ℝ) * (v 0 * v 4 * h 1) + ((-1 : ℝ) / 2) * (v 0 * v 3 * h 1) + ((-5 : ℝ) / 2) * (v 0 * v 3 * h 0) + -(v 0 * v 2 * h 1) + -(v 0 * v 2 * h 0) + (2 : ℝ) * (v 0 * v 1 * h 0) + ((1 : ℝ) / 2) * ((v 0) ^ 2 * h 0)) * g0 +
      ((-4 : ℝ) * ((v 4) ^ 2 * h 1) + (6 : ℝ) * (v 3 * v 4 * h 1) + (-2 : ℝ) * ((v 3) ^ 2 * h 0) + (2 : ℝ) * (v 2 * v 4 * h 1) + (-2 : ℝ) * (v 1 * v 4 * h 1) + (6 : ℝ) * (v 0 * v 4 * h 1) + ((-1 : ℝ) / 2) * (v 0 * v 3 * h 1) + ((-9 : ℝ) / 2) * (v 0 * v 3 * h 0) + v 0 * v 1 * h 1 + (2 : ℝ) * (v 0 * v 1 * h 0) + -((v 0) ^ 2 * h 1) + ((-5 : ℝ) / 2) * ((v 0) ^ 2 * h 0)) * g1 +
      (v 3 * h 1 + -(v 3 * h 0) + ((-1 : ℝ) / 2) * (v 0 * h 1) + ((-3 : ℝ) / 2) * (v 0 * h 0) + (4 : ℝ) * ((v 3) ^ 2 * v 4) + (-2 : ℝ) * ((v 3) ^ 3) + (4 : ℝ) * (v 1 * (v 3) ^ 2) + (-2 : ℝ) * (v 0 * (v 3) ^ 2) + (4 : ℝ) * (v 0 * v 1 * v 3) + (-4 : ℝ) * ((v 0) ^ 2 * v 4)) * g2 +
      ((-4 : ℝ) * (v 4) + v 3 + v 2 + -(v 1)) * g3 +
      ((-2 : ℝ) * (v 2 * v 4) + -(v 2 * v 3) + (2 : ℝ) * ((v 1) ^ 2) + ((-1 : ℝ) / 2) * ((v 0) ^ 2)) * g4 +
      ((-2 : ℝ) * (v 2 * v 4) + v 1 * v 3 + (2 : ℝ) * ((v 1) ^ 2) + ((-1 : ℝ) / 2) * ((v 0) ^ 2)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork120, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : v 3 = 0 := by
      nlinarith [hg1]
    simp [-mul_eq_zero, cubicResidualNetwork120, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 2 * (v 3) ^ 2 * h 1 + -(v 2 * (v 3) ^ 2 * h 0) + v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 2 * v 3 * h 1) + (-2 : ℝ) * ((v 1) ^ 2 * v 3 * h 1) + (4 : ℝ) * (v 0 * v 2 * v 4 * h 1) + -(v 0 * v 2 * v 3 * h 0) + (4 : ℝ) * (v 0 * v 1 * v 4 * h 1) + -(v 0 * v 1 * v 3 * h 0) = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 2 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 4 * h 1)) * g0 +
      ((-4 : ℝ) * (v 2 * v 4 * h 1) + v 2 * v 3 * h 1 + -(v 2 * v 3 * h 0) + (-4 : ℝ) * (v 1 * v 4 * h 1) + v 1 * v 3 * h 1 + -(v 1 * v 3 * h 0) + (-2 : ℝ) * (v 1 * v 2 * h 1) + (-2 : ℝ) * ((v 1) ^ 2 * h 1) + -(v 0 * v 2 * h 0) + -(v 0 * v 1 * h 0)) * g1
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork120, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : (4 : ℝ) * (v 4) + -(v 3) + (2 : ℝ) * (v 1) = 0 := by
      nlinarith [hg1]
    have g2 : (2 : ℝ) * (v 4) + -(v 3) + (2 : ℝ) * (v 1) + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : (-2 : ℝ) * (v 4) + v 3 + v 2 + -(v 1) = 0 := by
      nlinarith [heq1]
    have g6 : (4 : ℝ) * (v 4 * h 1) + -(v 3 * h 1) + -(v 3 * h 0) + (-4 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + (2 : ℝ) * (v 2 * (v 3) ^ 2) + (2 : ℝ) * (v 1 * h 1) + (-2 : ℝ) * (v 1 * (v 3) ^ 2) + -(v 0 * h 0) = 0 := by
      nlinarith [hc0]
    have g7 : (-4 : ℝ) * (v 4 * h 1) + v 3 * h 1 + v 3 * h 0 + (4 : ℝ) * ((v 3) ^ 2 * v 4) + (-2 : ℝ) * ((v 3) ^ 3) + v 2 * h 1 + (-2 : ℝ) * (v 2 * (v 3) ^ 2) + -(v 1 * h 1) + (2 : ℝ) * (v 1 * (v 3) ^ 2) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork120, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 0 * (v 3) ^ 2 * h 1 + -(v 0 * (v 3) ^ 2 * h 0) + v 0 * v 2 * v 3 * h 1 + -(v 0 * v 1 * v 3 * h 1) = 0 := by
      linear_combination
        ((-2 : ℝ) * (v 3 * v 4 * h 1) + -((v 3) ^ 2 * h 1) + (v 3) ^ 2 * h 0 + (-8 : ℝ) * (v 2 * v 4 * h 1) + (-4 : ℝ) * (v 2 * v 4 * h 0) + -(v 2 * v 3 * h 1) + (4 : ℝ) * (v 2 * v 3 * h 0) + -(v 1 * v 3 * h 1) + (-4 : ℝ) * (v 1 * v 2 * h 1) + (-4 : ℝ) * (v 1 * v 2 * h 0) + (2 : ℝ) * (v 0 * v 4 * h 1) + (2 : ℝ) * (v 0 * v 2 * h 1) + (2 : ℝ) * (v 0 * v 1 * h 1) + -((v 0) ^ 2 * h 1)) * g0 +
      ((-2 : ℝ) * ((v 3) ^ 2 * h 1) + (v 3) ^ 2 * h 0 + (-2 : ℝ) * (v 2 * v 3 * h 1) + (-2 : ℝ) * (v 0 * v 2 * h 0)) * g1 +
      ((4 : ℝ) * (v 2 * v 4 * h 1) + (-2 : ℝ) * (v 2 * v 3 * h 0) + (-2 : ℝ) * (v 0 * v 2 * h 1) + (v 0) ^ 2 * h 1) * g2 +
      ((-3 : ℝ) * ((v 3) ^ 2 * h 1) + (2 : ℝ) * ((v 3) ^ 2 * h 0) + (4 : ℝ) * (v 2 * v 4 * h 1)) * g3 +
      ((-4 : ℝ) * (v 2 * v 4)) * g6 +
      ((-4 : ℝ) * (v 2 * v 4)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork120, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork120, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -(v 2 * (v 3) ^ 2 * h 1) + v 2 * (v 3) ^ 2 * h 0 + -((v 2) ^ 2 * v 3 * h 1) + -(v 1 * (v 3) ^ 2 * h 1) + v 1 * (v 3) ^ 2 * h 0 + (v 1) ^ 2 * v 3 * h 1 = 0 := by
      linear_combination
        (-(v 2 * v 3 * h 1) + v 2 * v 3 * h 0 + -((v 2) ^ 2 * h 1) + -(v 1 * v 3 * h 1) + v 1 * v 3 * h 0 + (v 1) ^ 2 * h 1) * g2
    nlinarith [hcertificate]

theorem cubicResidualNetwork120_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork120.toNetwork := by
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
  simp [cubicResidualNetwork120, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork120_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork120.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork120_jacobianNonzero
    cubicResidualNetwork120_fourCharts

def cubicResidualNetwork121 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xy), (.xy, .xx), (.xy, .yy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork121_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork121.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork121, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g2 : -(v 1 * v 3) + v 1 * v 2 + (4 : ℝ) * (v 0 * v 4) + -(v 0 * v 3) + v 0 * v 2 = 0 := by
      nlinarith [hdet]
    have g4 : (4 : ℝ) * (v 4 * h 1) + -(v 3 * h 1) + -(v 3 * h 0) + (-4 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + v 2 * h 1 + v 2 * h 0 + (8 : ℝ) * (v 2 * v 3 * v 4) + (-6 : ℝ) * (v 2 * (v 3) ^ 2) + (-4 : ℝ) * ((v 2) ^ 2 * v 4) + (6 : ℝ) * ((v 2) ^ 2 * v 3) + (-2 : ℝ) * ((v 2) ^ 3) + v 1 * h 1 + (-2 : ℝ) * (v 1 * (v 3) ^ 2) + (4 : ℝ) * (v 1 * v 2 * v 3) + (-2 : ℝ) * (v 1 * (v 2) ^ 2) + -(v 0 * h 0) + (2 : ℝ) * (v 0 * (v 3) ^ 2) + (-4 : ℝ) * (v 0 * v 2 * v 3) + (2 : ℝ) * (v 0 * (v 2) ^ 2) + (-2 : ℝ) * (v 0 * v 1 * v 3) + (2 : ℝ) * (v 0 * v 1 * v 2) + (4 : ℝ) * ((v 0) ^ 2 * v 4) = 0 := by
      nlinarith [hc0]
    have g5 : (-4 : ℝ) * (v 4 * h 1) + v 3 * h 1 + v 3 * h 0 + (4 : ℝ) * ((v 3) ^ 2 * v 4) + (-2 : ℝ) * ((v 3) ^ 3) + -(v 2 * h 1) + -(v 2 * h 0) + (-8 : ℝ) * (v 2 * v 3 * v 4) + (6 : ℝ) * (v 2 * (v 3) ^ 2) + (4 : ℝ) * ((v 2) ^ 2 * v 4) + (-6 : ℝ) * ((v 2) ^ 2 * v 3) + (2 : ℝ) * ((v 2) ^ 3) + (2 : ℝ) * (v 1 * (v 3) ^ 2) + (-4 : ℝ) * (v 1 * v 2 * v 3) + (2 : ℝ) * (v 1 * (v 2) ^ 2) + (-2 : ℝ) * (v 0 * (v 3) ^ 2) + (4 : ℝ) * (v 0 * v 2 * v 3) + (-2 : ℝ) * (v 0 * (v 2) ^ 2) + (2 : ℝ) * (v 0 * v 1 * v 3) + (-2 : ℝ) * (v 0 * v 1 * v 2) + (-4 : ℝ) * ((v 0) ^ 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork121, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 + (2 : ℝ) * (v 0 * v 2 * v 3 * h 1) + (-2 : ℝ) * (v 0 * v 2 * v 3 * h 0) + -(v 0 * (v 2) ^ 2 * h 1) + v 0 * (v 2) ^ 2 * h 0 + v 0 * v 1 * v 3 * h 1 + -(v 0 * v 1 * v 2 * h 1) + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) + (v 0) ^ 2 * v 3 * h 0 + -((v 0) ^ 2 * v 2 * h 0) = 0 := by
      linear_combination
        ((-2 : ℝ) * (v 2 * v 4 * h 1)) * g0 +
      ((-2 : ℝ) * (v 2 * v 4 * h 1) + (-2 : ℝ) * (v 1 * v 4 * h 1) + -(v 1 * v 3 * h 1) + -((v 1) ^ 2 * h 1) + (2 : ℝ) * (v 0 * v 4 * h 0) + (-2 : ℝ) * (v 0 * v 3 * h 1) + v 0 * v 3 * h 0 + v 0 * v 2 * h 1 + -(v 0 * v 2 * h 0) + (-2 : ℝ) * (v 0 * v 1 * h 1) + v 0 * v 1 * h 0 + (-2 : ℝ) * ((v 0) ^ 2 * h 1) + (2 : ℝ) * ((v 0) ^ 2 * h 0)) * g1 +
      (-(v 3 * h 1) + -(v 1 * h 1) + (-2 : ℝ) * (v 0 * h 1) + v 0 * h 0) * g2 +
      ((-4 : ℝ) * ((v 4) ^ 2) + (-2 : ℝ) * (v 1 * v 4)) * g4 +
      ((-4 : ℝ) * ((v 4) ^ 2) + (-2 : ℝ) * (v 1 * v 4)) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork121, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : v 3 + -(v 2) = 0 := by
      nlinarith [hg1]
    simp [-mul_eq_zero, cubicResidualNetwork121, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + (-2 : ℝ) * (v 1 * v 2 * v 3 * h 1) + (2 : ℝ) * (v 1 * v 2 * v 3 * h 0) + v 1 * (v 2) ^ 2 * h 1 + -(v 1 * (v 2) ^ 2 * h 0) + -((v 1) ^ 2 * v 3 * h 1) + (v 1) ^ 2 * v 2 * h 1 + (4 : ℝ) * (v 0 * v 1 * v 4 * h 1) + -(v 0 * v 1 * v 3 * h 0) + v 0 * v 1 * v 2 * h 0 = 0 := by
      linear_combination
        ((-4 : ℝ) * (v 1 * v 4 * h 1)) * g0 +
      ((-4 : ℝ) * (v 1 * v 4 * h 1) + v 1 * v 3 * h 1 + -(v 1 * v 3 * h 0) + -(v 1 * v 2 * h 1) + v 1 * v 2 * h 0 + -((v 1) ^ 2 * h 1) + -(v 0 * v 1 * h 0)) * g1
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork121, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g3 : (-2 : ℝ) * (v 4) + v 3 + -(v 2) = 0 := by
      nlinarith [heq1]
    have g5 : (4 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (-2 : ℝ) * (v 0 * (v 3) ^ 3) + (-8 : ℝ) * (v 0 * v 2 * v 3 * v 4) + (6 : ℝ) * (v 0 * v 2 * (v 3) ^ 2) + (4 : ℝ) * (v 0 * (v 2) ^ 2 * v 4) + (-6 : ℝ) * (v 0 * (v 2) ^ 2 * v 3) + (2 : ℝ) * (v 0 * (v 2) ^ 3) = 0 := by
      nlinarith [hfold]
    have g7 : (-4 : ℝ) * (v 4 * h 1) + v 3 * h 1 + v 3 * h 0 + (4 : ℝ) * ((v 3) ^ 2 * v 4) + (-2 : ℝ) * ((v 3) ^ 3) + -(v 2 * h 1) + -(v 2 * h 0) + (-8 : ℝ) * (v 2 * v 3 * v 4) + (6 : ℝ) * (v 2 * (v 3) ^ 2) + (4 : ℝ) * ((v 2) ^ 2 * v 4) + (-6 : ℝ) * ((v 2) ^ 2 * v 3) + (2 : ℝ) * ((v 2) ^ 3) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork121, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 0 * (v 3) ^ 2 * h 1 + -(v 0 * (v 3) ^ 2 * h 0) + (-2 : ℝ) * (v 0 * v 2 * v 3 * h 1) + (2 : ℝ) * (v 0 * v 2 * v 3 * h 0) + v 0 * (v 2) ^ 2 * h 1 + -(v 0 * (v 2) ^ 2 * h 0) = 0 := by
      linear_combination
        ((4 : ℝ) * (v 0 * v 4 * h 1) + v 0 * v 3 * h 1 + -(v 0 * v 3 * h 0) + -(v 0 * v 2 * h 1) + v 0 * v 2 * h 0) * g3 +
      ((2 : ℝ) * (v 4)) * g5 +
      ((-2 : ℝ) * (v 0 * v 4)) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork121, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g2 : v 3 + -(v 2) = 0 := by
      nlinarith [hg2]
    simp [-mul_eq_zero, cubicResidualNetwork121, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -(v 1 * (v 3) ^ 2 * h 1) + v 1 * (v 3) ^ 2 * h 0 + (2 : ℝ) * (v 1 * v 2 * v 3 * h 1) + (-2 : ℝ) * (v 1 * v 2 * v 3 * h 0) + -(v 1 * (v 2) ^ 2 * h 1) + v 1 * (v 2) ^ 2 * h 0 = 0 := by
      linear_combination
        (-(v 1 * v 3 * h 1) + v 1 * v 3 * h 0 + v 1 * v 2 * h 1 + -(v 1 * v 2 * h 0)) * g2
    nlinarith [hcertificate]

theorem cubicResidualNetwork121_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork121.toNetwork := by
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
  simp [cubicResidualNetwork121, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork121_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork121.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork121_jacobianNonzero
    cubicResidualNetwork121_fourCharts

def cubicResidualNetwork122 : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xy), (.xy, .yy), (.yy, .xx), (.yy, .xy)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork122_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork122.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork122, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : v 4 + (2 : ℝ) * (v 3) + -(v 2) + v 1 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g1 : -(v 4) + (-2 : ℝ) * (v 3) + v 2 = 0 := by
      nlinarith [heq1]
    have g2 : -(v 1 * v 2) + (2 : ℝ) * (v 0 * v 4) + (4 : ℝ) * (v 0 * v 3) + -(v 0 * v 2) = 0 := by
      nlinarith [hdet]
    have g3 : (2 : ℝ) * (v 0 * (v 2) ^ 2 * v 4) + (4 : ℝ) * (v 0 * (v 2) ^ 2 * v 3) + (-2 : ℝ) * (v 0 * (v 2) ^ 3) + (2 : ℝ) * (v 0 * v 1 * (v 2) ^ 2) + (-2 : ℝ) * ((v 0) ^ 2 * (v 2) ^ 2) + (2 : ℝ) * ((v 0) ^ 2 * v 1 * v 2) + (-2 : ℝ) * ((v 0) ^ 3 * v 4) + (-4 : ℝ) * ((v 0) ^ 3 * v 3) = 0 := by
      nlinarith [hfold]
    have g4 : (2 : ℝ) * (v 4 * h 1) + (4 : ℝ) * (v 3 * h 1) + -(v 2 * h 1) + -(v 2 * h 0) + (-2 : ℝ) * ((v 2) ^ 2 * v 4) + (-4 : ℝ) * ((v 2) ^ 2 * v 3) + (2 : ℝ) * ((v 2) ^ 3) + v 1 * h 1 + (-2 : ℝ) * (v 1 * (v 2) ^ 2) + -(v 0 * h 0) + (2 : ℝ) * (v 0 * (v 2) ^ 2) + (-2 : ℝ) * (v 0 * v 1 * v 2) + (2 : ℝ) * ((v 0) ^ 2 * v 4) + (4 : ℝ) * ((v 0) ^ 2 * v 3) = 0 := by
      nlinarith [hc0]
    have g5 : (-2 : ℝ) * (v 4 * h 1) + (-4 : ℝ) * (v 3 * h 1) + v 2 * h 1 + v 2 * h 0 + (2 : ℝ) * ((v 2) ^ 2 * v 4) + (4 : ℝ) * ((v 2) ^ 2 * v 3) + (-2 : ℝ) * ((v 2) ^ 3) + (2 : ℝ) * (v 1 * (v 2) ^ 2) + (-2 : ℝ) * (v 0 * (v 2) ^ 2) + (2 : ℝ) * (v 0 * v 1 * v 2) + (-2 : ℝ) * ((v 0) ^ 2 * v 4) + (-4 : ℝ) * ((v 0) ^ 2 * v 3) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork122, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -(v 0 * (v 2) ^ 2 * h 1) + v 0 * (v 2) ^ 2 * h 0 + v 0 * v 1 * v 2 * h 1 + (-2 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) + (-4 : ℝ) * ((v 0) ^ 2 * v 3 * h 1) + (v 0) ^ 2 * v 2 * h 0 = 0 := by
      linear_combination
        (-((v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 3 * v 4 * h 0) + (-2 : ℝ) * (v 1 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 3 * h 1) + (2 : ℝ) * (v 1 * v 2 * h 1)) * g0 +
      (-((v 4) ^ 2 * h 0) + (-2 : ℝ) * (v 3 * v 4 * h 0) + (-3 : ℝ) * (v 1 * v 4 * h 1) + -(v 1 * v 4 * h 0) + (-2 : ℝ) * (v 1 * v 3 * h 1) + v 1 * v 2 * h 1 + (-2 : ℝ) * ((v 1) ^ 2 * h 1) + (-2 : ℝ) * (v 0 * v 3 * h 0) + (-2 : ℝ) * (v 0 * v 2 * h 1) + v 0 * v 2 * h 0 + (-2 : ℝ) * ((v 0) ^ 2 * h 1) + (2 : ℝ) * ((v 0) ^ 2 * h 0)) * g1 +
      (-(v 4 * h 0) + -(v 2 * h 1) + (-2 : ℝ) * (v 0 * h 1) + v 0 * h 0) * g2 +
      (-(v 1)) * g3 +
      (-((v 4) ^ 2) + (4 : ℝ) * ((v 3) ^ 2) + (-4 : ℝ) * (v 2 * v 3)) * g4 +
      (-((v 4) ^ 2) + (4 : ℝ) * ((v 3) ^ 2) + (-4 : ℝ) * (v 2 * v 3) + v 0 * v 1) * g5
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork122, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 2) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : v 2 = 0 := by
      nlinarith [hg1]
    simp [-mul_eq_zero, cubicResidualNetwork122, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 1 * (v 2) ^ 2 * h 1 + -(v 1 * (v 2) ^ 2 * h 0) + -((v 1) ^ 2 * v 2 * h 1) + (2 : ℝ) * (v 0 * v 1 * v 4 * h 1) + (4 : ℝ) * (v 0 * v 1 * v 3 * h 1) + -(v 0 * v 1 * v 2 * h 0) = 0 := by
      linear_combination
        ((-2 : ℝ) * (v 1 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 3 * h 1)) * g0 +
      ((-2 : ℝ) * (v 1 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 3 * h 1) + v 1 * v 2 * h 1 + -(v 1 * v 2 * h 0) + -((v 1) ^ 2 * h 1) + -(v 0 * v 1 * h 0)) * g1
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork122, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 2) + -(v 0) = 0 := by
      nlinarith [hg0]
    have g1 : (2 : ℝ) * (v 4) + (4 : ℝ) * (v 3) + -(v 2) + v 1 = 0 := by
      nlinarith [hg1]
    have g2 : v 4 + (2 : ℝ) * (v 3) + -(v 2) + v 1 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : -(v 4) + (-2 : ℝ) * (v 3) + v 2 = 0 := by
      nlinarith [heq1]
    have g5 : (2 : ℝ) * (v 0 * (v 2) ^ 2 * v 4) + (4 : ℝ) * (v 0 * (v 2) ^ 2 * v 3) + (-2 : ℝ) * (v 0 * (v 2) ^ 3) = 0 := by
      nlinarith [hfold]
    have g7 : (-2 : ℝ) * (v 4 * h 1) + (-4 : ℝ) * (v 3 * h 1) + v 2 * h 1 + v 2 * h 0 + (2 : ℝ) * ((v 2) ^ 2 * v 4) + (4 : ℝ) * ((v 2) ^ 2 * v 3) + (-2 : ℝ) * ((v 2) ^ 3) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork122, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : v 0 * (v 2) ^ 2 * h 1 + -(v 0 * (v 2) ^ 2 * h 0) = 0 := by
      linear_combination
        ((v 4) ^ 2 * h 0 + (2 : ℝ) * (v 3 * v 4 * h 0) + (4 : ℝ) * ((v 3) ^ 2 * h 0) + v 2 * v 4 * h 1 + -(v 2 * v 4 * h 0) + (2 : ℝ) * (v 2 * v 3 * h 1) + -((v 2) ^ 2 * h 1) + (-2 : ℝ) * (v 1 * v 4 * h 1) + v 1 * v 4 * h 0 + (-4 : ℝ) * (v 1 * v 3 * h 1) + (2 : ℝ) * (v 1 * v 3 * h 0) + (2 : ℝ) * (v 1 * v 2 * h 1) + -(v 0 * v 4 * h 1) + -(v 0 * v 4 * h 0) + (-2 : ℝ) * (v 0 * v 3 * h 1) + (-2 : ℝ) * (v 0 * v 3 * h 0) + v 0 * v 2 * h 0 + -(v 0 * v 1 * h 1) + (v 0) ^ 2 * h 1) * g0 +
      ((4 : ℝ) * ((v 3) ^ 2 * h 0)) * g1 +
      (-((v 4) ^ 2 * h 0) + (2 : ℝ) * (v 2 * v 4 * h 0) + -((v 0) ^ 2 * h 1)) * g2 +
      (-((v 4) ^ 2 * h 0) + (8 : ℝ) * ((v 3) ^ 2 * h 0) + v 2 * v 4 * h 0 + -((v 2) ^ 2 * h 1) + -(v 1 * v 4 * h 0) + (2 : ℝ) * (v 1 * v 3 * h 0) + (2 : ℝ) * (v 1 * v 2 * h 1) + (-2 : ℝ) * (v 0 * v 3 * h 0) + -(v 0 * v 1 * h 0) + (v 0) ^ 2 * h 0) * g3 +
      (-(v 1)) * g5 +
      (v 0 * v 1) * g7
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork122, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g2 : v 2 = 0 := by
      nlinarith [hg2]
    simp [-mul_eq_zero, cubicResidualNetwork122, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -(v 1 * (v 2) ^ 2 * h 1) + v 1 * (v 2) ^ 2 * h 0 = 0 := by
      linear_combination
        (-(v 1 * v 2 * h 1) + v 1 * v 2 * h 0) * g2
    nlinarith [hcertificate]

theorem cubicResidualNetwork122_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork122.toNetwork := by
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
  simp [cubicResidualNetwork122, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork122_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork122.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork122_jacobianNonzero
    cubicResidualNetwork122_fourCharts

def cubicResidualNetwork123 : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .xx), (.y, .yy), (.xy, .zero), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork123_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork123.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork123, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : (-2 : ℝ) * (v 4) + -(v 3) + v 2 + v 0 = 0 := by
      nlinarith [heq1]
    have g2 : (4 : ℝ) * (v 3 * v 4) + -(v 2 * v 3) + (-4 : ℝ) * (v 1 * v 4) + -(v 1 * v 3) + v 1 * v 2 + (4 : ℝ) * (v 0 * v 4) + (2 : ℝ) * (v 0 * v 3) + -(v 0 * v 2) = 0 := by
      nlinarith [hdet]
    simp [-mul_eq_zero, cubicResidualNetwork123, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * ((v 3) ^ 2 * v 4 * h 1) + (8 : ℝ) * (v 1 * v 3 * v 4 * h 1) + -(v 1 * (v 3) ^ 2 * h 1) + v 1 * (v 3) ^ 2 * h 0 + (-4 : ℝ) * ((v 1) ^ 2 * v 4 * h 1) + -((v 1) ^ 2 * v 3 * h 0) + (-8 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (2 : ℝ) * (v 0 * (v 3) ^ 2 * h 1) + (-2 : ℝ) * (v 0 * (v 3) ^ 2 * h 0) + (8 : ℝ) * (v 0 * v 1 * v 4 * h 1) + (3 : ℝ) * (v 0 * v 1 * v 3 * h 0) + (-4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) + (-2 : ℝ) * ((v 0) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((-8 : ℝ) * ((v 4) ^ 2 * h 0) + (8 : ℝ) * (v 3 * v 4 * h 1) + (-8 : ℝ) * (v 3 * v 4 * h 0) + (6 : ℝ) * (v 2 * v 4 * h 0) + -(v 2 * v 3 * h 1) + (2 : ℝ) * (v 2 * v 3 * h 0) + -((v 2) ^ 2 * h 0) + (4 : ℝ) * (v 1 * v 4 * h 0) + (2 : ℝ) * (v 1 * v 3 * h 1) + (-2 : ℝ) * (v 1 * v 2 * h 1) + -(v 1 * v 2 * h 0) + (4 : ℝ) * (v 0 * v 4 * h 1) + (-2 : ℝ) * (v 0 * v 1 * h 1)) * g0 +
      ((-2 : ℝ) * (v 1 * v 3 * h 1) + v 1 * v 3 * h 0 + (2 : ℝ) * ((v 1) ^ 2 * h 1) + (-2 : ℝ) * (v 0 * v 3 * h 0) + (-2 : ℝ) * (v 0 * v 1 * h 1)) * g1 +
      ((-2 : ℝ) * (v 4 * h 0) + v 3 * h 1 + (-2 : ℝ) * (v 3 * h 0) + v 2 * h 0 + v 1 * h 0) * g2
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork123, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : -(v 3) + v 0 = 0 := by
      nlinarith [hg1]
    have g2 : -(v 3) + v 1 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g5 : (-12 : ℝ) * ((v 3) ^ 3 * v 4) + (2 : ℝ) * (v 2 * (v 3) ^ 3) + (16 : ℝ) * (v 1 * (v 3) ^ 2 * v 4) + (-2 : ℝ) * (v 1 * v 2 * (v 3) ^ 2) + (-4 : ℝ) * ((v 1) ^ 2 * v 3 * v 4) + (-16 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (2 : ℝ) * (v 0 * v 2 * (v 3) ^ 2) + (8 : ℝ) * (v 0 * v 1 * v 3 * v 4) + (-4 : ℝ) * ((v 0) ^ 2 * v 3 * v 4) = 0 := by
      nlinarith [hfold]
    have g6 : -(v 3 * h 1) + -(v 3 * h 0) + (2 : ℝ) * ((v 3) ^ 3) + v 1 * h 0 + (-2 : ℝ) * (v 1 * (v 3) ^ 2) + -(v 0 * h 0) + (2 : ℝ) * (v 0 * (v 3) ^ 2) = 0 := by
      nlinarith [hc0]
    have g7 : (-4 : ℝ) * (v 4 * h 1) + -(v 3 * h 1) + -(v 3 * h 0) + (-4 : ℝ) * ((v 3) ^ 2 * v 4) + (2 : ℝ) * ((v 3) ^ 3) + v 2 * h 1 + (8 : ℝ) * (v 1 * v 3 * v 4) + (-2 : ℝ) * (v 1 * (v 3) ^ 2) + (-4 : ℝ) * ((v 1) ^ 2 * v 4) + v 0 * h 0 + (-8 : ℝ) * (v 0 * v 3 * v 4) + (2 : ℝ) * (v 0 * (v 3) ^ 2) + (8 : ℝ) * (v 0 * v 1 * v 4) + (-4 : ℝ) * ((v 0) ^ 2 * v 4) = 0 := by
      nlinarith [hc1]
    simp [-mul_eq_zero, cubicResidualNetwork123, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
        ((-16 : ℝ) * (v 3 * v 4 * h 0) + (2 : ℝ) * (v 1 * v 4 * h 0)) * g0 +
      ((6 : ℝ) * (v 3 * v 4 * h 0) + (2 : ℝ) * (v 2 * v 3 * h 0) + (-2 : ℝ) * (v 1 * v 4 * h 0) + -(v 1 * v 2 * h 0) + (2 : ℝ) * (v 0 * v 4 * h 0) + v 0 * v 2 * h 0) * g1 +
      ((-16 : ℝ) * ((v 4) ^ 2 * h 0) + (2 : ℝ) * (v 3 * v 4 * h 1) + (v 2) ^ 2 * h 0 + v 0 * v 2 * h 0) * g2 +
      ((4 : ℝ) * (v 4) + v 3 + v 2) * g5 +
      ((16 : ℝ) * ((v 4) ^ 2) + (10 : ℝ) * (v 3 * v 4) + -((v 2) ^ 2) + (-2 : ℝ) * (v 1 * v 4) + (2 : ℝ) * (v 0 * v 4)) * g6 +
      ((-4 : ℝ) * (v 3 * v 4) + -(v 2 * v 3)) * g7
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork123, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g1 : -(v 3) = 0 := by
      nlinarith [hg1]
    have g2 : -(v 3) + v 1 + -(v 0) = 0 := by
      nlinarith [heq0]
    have g3 : (-2 : ℝ) * (v 4) + -(v 3) + v 2 + v 0 = 0 := by
      nlinarith [heq1]
    simp [-mul_eq_zero, cubicResidualNetwork123, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * ((v 3) ^ 2 * v 4 * h 1) + -(v 1 * (v 3) ^ 2 * h 1) + v 1 * (v 3) ^ 2 * h 0 + v 1 * v 2 * v 3 * h 1 + (8 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (2 : ℝ) * (v 0 * (v 3) ^ 2 * h 1) + (-2 : ℝ) * (v 0 * (v 3) ^ 2 * h 0) + (-2 : ℝ) * (v 0 * v 2 * v 3 * h 1) + (-4 : ℝ) * (v 0 * v 1 * v 4 * h 1) + -(v 0 * v 1 * v 3 * h 0) + (4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) + (2 : ℝ) * ((v 0) ^ 2 * v 3 * h 0) = 0 := by
      linear_combination
        ((4 : ℝ) * (v 1 * v 4 * h 1) + (-2 : ℝ) * (v 1 * v 2 * h 1) + (-2 : ℝ) * (v 0 * v 1 * h 1)) * g0 +
      ((4 : ℝ) * (v 3 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 4 * h 1) + v 1 * v 3 * h 1 + -(v 1 * v 3 * h 0) + v 1 * v 2 * h 1 + (-2 : ℝ) * ((v 1) ^ 2 * h 1) + (-8 : ℝ) * (v 0 * v 4 * h 1) + (-2 : ℝ) * (v 0 * v 3 * h 1) + (2 : ℝ) * (v 0 * v 3 * h 0) + (4 : ℝ) * (v 0 * v 2 * h 1) + (2 : ℝ) * (v 0 * v 1 * h 1) + v 0 * v 1 * h 0 + (4 : ℝ) * ((v 0) ^ 2 * h 1) + (-2 : ℝ) * ((v 0) ^ 2 * h 0)) * g1 +
      ((-2 : ℝ) * (v 0 * v 2 * h 1) + (-2 : ℝ) * ((v 0) ^ 2 * h 1)) * g2 +
      ((2 : ℝ) * ((v 1) ^ 2 * h 1) + (-2 : ℝ) * ((v 0) ^ 2 * h 1)) * g3
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork123, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork123, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-16 : ℝ) * (v 3 * (v 4) ^ 2 * h 1) + (-8 : ℝ) * ((v 3) ^ 2 * v 4 * h 1) + (4 : ℝ) * ((v 3) ^ 2 * v 4 * h 0) + (8 : ℝ) * (v 2 * v 3 * v 4 * h 1) + v 2 * (v 3) ^ 2 * h 1 + -(v 2 * (v 3) ^ 2 * h 0) + -((v 2) ^ 2 * v 3 * h 1) + (4 : ℝ) * (v 0 * v 3 * v 4 * h 1) + (-4 : ℝ) * (v 0 * v 3 * v 4 * h 0) + v 0 * v 2 * v 3 * h 0 = 0 := by
      linear_combination
        ((16 : ℝ) * ((v 4) ^ 2 * h 1) + (8 : ℝ) * (v 3 * v 4 * h 1) + (-4 : ℝ) * (v 3 * v 4 * h 0) + (-8 : ℝ) * (v 2 * v 4 * h 1) + -(v 2 * v 3 * h 1) + v 2 * v 3 * h 0 + (v 2) ^ 2 * h 1 + (-4 : ℝ) * (v 0 * v 4 * h 1) + (4 : ℝ) * (v 0 * v 4 * h 0) + -(v 0 * v 2 * h 0)) * g1
    nlinarith [hcertificate]

theorem cubicResidualNetwork123_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork123.toNetwork := by
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
  simp [cubicResidualNetwork123, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork123_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork123.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork123_jacobianNonzero
    cubicResidualNetwork123_fourCharts

def cubicResidualNetwork124 : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .xx), (.y, .yy), (.xy, .x), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork124_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork124.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork124, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork124, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
        ((-4 : ℝ) * (v 1 * v 4 * h 1) + -(v 1 * v 3 * h 0) + (4 : ℝ) * (v 0 * v 4 * h 1) + v 0 * v 3 * h 0) * g0
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork124, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork124, CodedBimolNetwork.toNetwork,
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
    simp [-mul_eq_zero, cubicResidualNetwork124, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork124, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : -(v 1 * (v 3) ^ 2 * h 1) + v 1 * (v 3) ^ 2 * h 0 + v 1 * v 2 * v 3 * h 1 + v 0 * (v 3) ^ 2 * h 1 + -(v 0 * (v 3) ^ 2 * h 0) + -(v 0 * v 2 * v 3 * h 1) + (-4 : ℝ) * (v 0 * v 1 * v 4 * h 1) + -(v 0 * v 1 * v 3 * h 0) + (4 : ℝ) * ((v 0) ^ 2 * v 4 * h 1) + (v 0) ^ 2 * v 3 * h 0 = 0 := by
      linear_combination
        (-((v 3) ^ 2 * h 1) + (-4 : ℝ) * (v 0 * v 4 * h 1) + -(v 0 * v 3 * h 0)) * g0 +
      ((v 3) ^ 2 * h 0 + v 2 * v 3 * h 1) * g2
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork124, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork124, CodedBimolNetwork.toNetwork,
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

theorem cubicResidualNetwork124_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork124.toNetwork := by
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
  simp [cubicResidualNetwork124, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork124_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork124.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork124_jacobianNonzero
    cubicResidualNetwork124_fourCharts

def cubicResidualNetwork125 : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.x, .xy), (.y, .yy), (.xy, .zero), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

theorem cubicResidualNetwork125_fourCharts :
    FourChartCubicDegenerate cubicResidualNetwork125.toNetwork := by
  intro r l
  cases r <;> cases l <;>
    intro v h hv heq hdet hrg hlg hfold hcenter
  all_goals
    have heq0 := heq 0
    have heq1 := heq 1
    have hc0 := hcenter 0
    have hc1 := hcenter 1
    simp [-mul_eq_zero, cubicResidualNetwork125, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 3) + v 0 = 0 := by
      nlinarith [heq0]
    have g2 : (4 : ℝ) * (v 3 * v 4) + -(v 2 * v 3) + v 1 * v 3 + (-4 : ℝ) * (v 0 * v 4) + -(v 0 * v 3) + v 0 * v 2 = 0 := by
      nlinarith [hdet]
    simp [-mul_eq_zero, cubicResidualNetwork125, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
        ((8 : ℝ) * (v 3 * v 4 * h 1) + -(v 2 * v 3 * h 1) + v 1 * v 3 * h 0 + (-4 : ℝ) * (v 0 * v 4 * h 1) + -(v 0 * v 3 * h 0)) * g0 +
      (v 3 * h 1) * g2
    nlinarith [hcertificate]
  case false.true =>
    have hg0 := hlg.1
    have hg1 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork125, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g0 : -(v 3) + v 0 = 0 := by
      nlinarith [hg0]
    have g1 : -(v 3) + v 1 = 0 := by
      nlinarith [hg1]
    have g2 : -(v 3) + v 0 = 0 := by
      nlinarith [heq0]
    have g5 : (-12 : ℝ) * ((v 3) ^ 3 * v 4) + (2 : ℝ) * (v 2 * (v 3) ^ 3) + (16 : ℝ) * (v 0 * (v 3) ^ 2 * v 4) + (-2 : ℝ) * (v 0 * v 2 * (v 3) ^ 2) + (-4 : ℝ) * ((v 0) ^ 2 * v 3 * v 4) = 0 := by
      nlinarith [hfold]
    have g6 : -(v 3 * h 1) + -(v 3 * h 0) + (2 : ℝ) * ((v 3) ^ 3) + v 0 * h 0 + (-2 : ℝ) * (v 0 * (v 3) ^ 2) = 0 := by
      nlinarith [hc0]
    simp [-mul_eq_zero, cubicResidualNetwork125, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
        ((-10 : ℝ) * (v 1 * v 4 * h 0) + (2 : ℝ) * (v 1 * v 2 * h 0) + (2 : ℝ) * (v 0 * v 4 * h 0)) * g0 +
      ((2 : ℝ) * (v 3 * v 4 * h 1) + (-10 : ℝ) * (v 3 * v 4 * h 0) + (2 : ℝ) * (v 2 * v 3 * h 0) + (-2 : ℝ) * (v 0 * v 4 * h 1) + (10 : ℝ) * (v 0 * v 4 * h 0) + (-2 : ℝ) * (v 0 * v 2 * h 0)) * g1 +
      ((2 : ℝ) * (v 1 * v 4 * h 1)) * g2 +
      (v 3) * g5 +
      ((6 : ℝ) * (v 3 * v 4) + -(v 2 * v 3) + (-2 : ℝ) * (v 0 * v 4)) * g6
    nlinarith [hcertificate]
  case true.false =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    simp [-mul_eq_zero, cubicResidualNetwork125, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    have g2 : -(v 3) + v 0 = 0 := by
      nlinarith [heq0]
    simp [-mul_eq_zero, cubicResidualNetwork125, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-4 : ℝ) * ((v 3) ^ 2 * v 4 * h 1) + (8 : ℝ) * (v 1 * v 3 * v 4 * h 1) + v 1 * (v 3) ^ 2 * h 1 + -(v 1 * (v 3) ^ 2 * h 0) + -(v 1 * v 2 * v 3 * h 1) + (v 1) ^ 2 * v 3 * h 0 + -(v 0 * (v 3) ^ 2 * h 1) + v 0 * (v 3) ^ 2 * h 0 + v 0 * v 2 * v 3 * h 1 + (-4 : ℝ) * (v 0 * v 1 * v 4 * h 1) + -(v 0 * v 1 * v 3 * h 0) = 0 := by
      linear_combination
        ((4 : ℝ) * (v 3 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 4 * h 1) + -(v 1 * v 3 * h 1) + v 1 * v 3 * h 0 + v 1 * v 2 * h 1 + -((v 1) ^ 2 * h 0) + v 0 * v 3 * h 1 + -(v 0 * v 3 * h 0) + -(v 0 * v 2 * h 1) + v 0 * v 1 * h 0) * g1 +
      ((-4 : ℝ) * (v 1 * v 4 * h 1)) * g2
    nlinarith [hcertificate]
  case true.true =>
    have hg0 := hrg.1
    have hg1 := hrg.2
    have hg2 := hlg.2
    simp [-mul_eq_zero, cubicResidualNetwork125, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
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
    simp [-mul_eq_zero, cubicResidualNetwork125, CodedBimolNetwork.toNetwork,
      chartRightKernel, chartLeftKernel, rightChartGuard, leftChartGuard,
      alternateRightKernel, alternateLeftKernel,
      canonicalRightKernel, canonicalLeftKernel,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, BimolComplexCode.decode, unitState,
      unitJacobianDet, dot, Fin.sum_univ_succ, Fin.prod_univ_two]
    have hcertificate : (-16 : ℝ) * (v 3 * (v 4) ^ 2 * h 1) + (-8 : ℝ) * ((v 3) ^ 2 * v 4 * h 1) + (4 : ℝ) * ((v 3) ^ 2 * v 4 * h 0) + (8 : ℝ) * (v 2 * v 3 * v 4 * h 1) + v 2 * (v 3) ^ 2 * h 1 + -(v 2 * (v 3) ^ 2 * h 0) + -((v 2) ^ 2 * v 3 * h 1) + (4 : ℝ) * (v 1 * v 3 * v 4 * h 1) + (-4 : ℝ) * (v 1 * v 3 * v 4 * h 0) + v 1 * v 2 * v 3 * h 0 = 0 := by
      linear_combination
        ((16 : ℝ) * ((v 4) ^ 2 * h 1) + (8 : ℝ) * (v 3 * v 4 * h 1) + (-4 : ℝ) * (v 3 * v 4 * h 0) + (-8 : ℝ) * (v 2 * v 4 * h 1) + -(v 2 * v 3 * h 1) + v 2 * v 3 * h 0 + (v 2) ^ 2 * h 1 + (-4 : ℝ) * (v 1 * v 4 * h 1) + (4 : ℝ) * (v 1 * v 4 * h 0) + -(v 1 * v 2 * h 0)) * g1
    nlinarith [hcertificate]

theorem cubicResidualNetwork125_jacobianNonzero :
    PositiveEquilibriumJacobianNonzero cubicResidualNetwork125.toNetwork := by
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
  simp [cubicResidualNetwork125, CodedBimolNetwork.toNetwork,
    SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    BimolComplexCode.decode, unitState, Fin.sum_univ_succ,
    Fin.prod_univ_two] at heq0 heq1 hJ
  nlinarith

theorem cubicResidualNetwork125_noCusp :
    ¬ AdmitsTransverseCusp cubicResidualNetwork125.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp _
    cubicResidualNetwork125_jacobianNonzero
    cubicResidualNetwork125_fourCharts

end SmallCusp

import proofs.SmallCusp.Obstruction.FewReactantAggregate
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

open scoped BigOperators

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def codedAggregate (C : CodedBimolNetwork) (v : Fin 5 → ℝ)
    (c : BimolComplexCode) (i : Species) : ℝ :=
  ∑ r : Fin 5, if (C.reaction r).1 = c then
    (C.toNetwork.stoich i r : ℝ) * v r else 0

def codedReactantSupport (C : CodedBimolNetwork) : Finset BimolComplexCode :=
  Finset.univ.image fun r : Fin 5 => (C.reaction r).1

private theorem sum_reactant_buckets (C : CodedBimolNetwork)
    (f : Fin 5 → ℝ) (g : BimolComplexCode → ℝ) :
    (∑ r : Fin 5, if (C.reaction r).1 = .zero then f r else 0) * g .zero +
    (∑ r : Fin 5, if (C.reaction r).1 = .x then f r else 0) * g .x +
    (∑ r : Fin 5, if (C.reaction r).1 = .y then f r else 0) * g .y +
    (∑ r : Fin 5, if (C.reaction r).1 = .xx then f r else 0) * g .xx +
    (∑ r : Fin 5, if (C.reaction r).1 = .xy then f r else 0) * g .xy +
    (∑ r : Fin 5, if (C.reaction r).1 = .yy then f r else 0) * g .yy =
      ∑ r : Fin 5, f r * g (C.reaction r).1 := by
  simp_rw [Finset.sum_mul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  generalize (C.reaction r).1 = c
  cases c <;> simp

private theorem coded_monomial_unit (C : CodedBimolNetwork) (r : Fin 5) :
    C.toNetwork.monomial r unitState = 1 := by
  simp [SmallPlanarNetwork.monomial, unitState]

private theorem coded_unit_derivative (C : CodedBimolNetwork)
    (r : Fin 5) (j : Species) :
    C.toNetwork.multiDerivativeMonomial r
      (SmallPlanarNetwork.unitMultiIndex j) unitState =
        ((C.reaction r).1.decode j : ℝ) := by
  cases h : (C.reaction r).1 <;> fin_cases j <;>
    norm_num [CodedBimolNetwork.toNetwork,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, BimolComplexCode.decode,
      unitState, Fin.prod_univ_two, h]

private theorem coded_pair_derivative_sum (C : CodedBimolNetwork)
    (r : Fin 5) (q h : Species → ℝ) :
    (∑ j : Species, ∑ l : Species,
      C.toNetwork.multiDerivativeMonomial r
        (SmallPlanarNetwork.pairMultiIndex j l) unitState * q j * h l) =
      aggregateHessianScalar (C.reaction r).1 q h := by
  cases hc : (C.reaction r).1 <;>
    norm_num [CodedBimolNetwork.toNetwork,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.pairMultiIndex, aggregateHessianScalar,
      BimolComplexCode.decode, unitState, Fin.prod_univ_two,
      Fin.sum_univ_two, hc] <;> ring

theorem aggregateMass_coded (C : CodedBimolNetwork) (v : Fin 5 → ℝ)
    (i : Species) :
    aggregateMass (codedAggregate C v) i =
      C.toNetwork.massAction v unitState i := by
  unfold aggregateMass codedAggregate
  have h := sum_reactant_buckets C
    (fun r => (C.toNetwork.stoich i r : ℝ) * v r) (fun _ => 1)
  simp only [mul_one] at h
  rw [h]
  simp [SmallPlanarNetwork.massAction, coded_monomial_unit]

theorem aggregateJacobian_coded (C : CodedBimolNetwork) (v : Fin 5 → ℝ)
    (i j : Species) :
    aggregateJacobian (codedAggregate C v) i j =
      C.toNetwork.jacobian v unitState i j := by
  unfold aggregateJacobian codedAggregate
  rw [sum_reactant_buckets C
    (fun r => (C.toNetwork.stoich i r : ℝ) * v r)
    (fun c => (c.decode j : ℝ))]
  simp_rw [SmallPlanarNetwork.jacobian, coded_unit_derivative]

theorem aggregateDet_coded (C : CodedBimolNetwork) (v : Fin 5 → ℝ) :
    aggregateDet (codedAggregate C v) = unitJacobianDet C.toNetwork v := by
  simp [aggregateDet, unitJacobianDet, aggregateJacobian_coded]

theorem aggregateHessianApply_coded (C : CodedBimolNetwork) (v : Fin 5 → ℝ)
    (q h : Species → ℝ) (i : Species) :
    aggregateHessianApply (codedAggregate C v) q h i =
      C.toNetwork.hessianApply v unitState q h i := by
  unfold aggregateHessianApply codedAggregate
  rw [sum_reactant_buckets C
    (fun r => (C.toNetwork.stoich i r : ℝ) * v r)
    (fun c => aggregateHessianScalar c q h)]
  simp_rw [← coded_pair_derivative_sum C]
  simp [SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    Fin.sum_univ_succ]
  ring

theorem codedAggregate_support (C : CodedBimolNetwork) (v : Fin 5 → ℝ)
    (c : BimolComplexCode) (hc : c ∉ codedReactantSupport C) :
    codedAggregate C v c = 0 := by
  funext i
  simp only [codedAggregate]
  apply Finset.sum_eq_zero
  intro r _
  simp only [ite_eq_right_iff]
  intro hrc
  apply False.elim
  apply hc
  simp [codedReactantSupport, ← hrc]

theorem coded_fewReactant_fourChart (C : CodedBimolNetwork)
    (hcard : (codedReactantSupport C).card ≤ 3) :
    FourChartCubicDegenerate C.toNetwork := by
  intro ra la v h _hv heq hdet _hrguard _hlguard _hfold _hcenter
  have hs : FewReactantAggregateSupport (codedAggregate C v) :=
    fewReactantAggregateSupport_of_card_le_three _ _ hcard
      (codedAggregate_support C v)
  have heq0 : aggregateMass (codedAggregate C v) 0 = 0 := by
    rw [aggregateMass_coded]
    exact heq 0
  have heq1 : aggregateMass (codedAggregate C v) 1 = 0 := by
    rw [aggregateMass_coded]
    exact heq 1
  have hdet' : aggregateDet (codedAggregate C v) = 0 := by
    rw [aggregateDet_coded]
    exact hdet
  have hmixed : aggregateMixed (codedAggregate C v) ra la h = 0 := by
    cases ra <;> cases la
    · exact fewReactantAggregate_00 _ _ hs heq0 heq1 hdet'
    · exact fewReactantAggregate_01 _ _ hs heq0 heq1 hdet'
    · exact fewReactantAggregate_10 _ _ hs heq0 heq1 hdet'
    · exact fewReactantAggregate_11 _ _ hs heq0 heq1 hdet'
  cases ra <;> cases la <;>
    simp [aggregateMixed, aggregateLeftKernel, aggregateRightKernel,
      chartLeftKernel, chartRightKernel, canonicalLeftKernel,
      canonicalRightKernel, alternateLeftKernel, alternateRightKernel,
      aggregateJacobian_coded, aggregateHessianApply_coded,
      SmallPlanarNetwork.hessianApply, dot, Fin.sum_univ_two] at hmixed ⊢ <;>
    nlinarith

theorem coded_fewReactant_excludes_cusp (C : CodedBimolNetwork)
    (hcard : (codedReactantSupport C).card ≤ 3) :
    ¬ AdmitsTransverseCusp C.toNetwork :=
  fourChartCubicDegenerate_excludes_cusp_intrinsic C.toNetwork
    (coded_fewReactant_fourChart C hcard)

noncomputable def encodeBimolNetwork (Q : SmallPlanarNetwork 5)
    (hr : Q.ReactantsAtMost 2) (hp : Q.ProductsAtMost 2) : CodedBimolNetwork where
  reaction r := (encodeBimolComplex (Q.reactant r),
    encodeBimolComplex (Q.product r))
  noSelf := by
    intro r h
    apply Q.noSelfReaction r
    calc
      Q.reactant r = (encodeBimolComplex (Q.reactant r)).decode :=
        (decode_encodeBimolComplex _ (hr r)).symm
      _ = (encodeBimolComplex (Q.product r)).decode := congrArg _ h
      _ = Q.product r := decode_encodeBimolComplex _ (hp r)
  injective := by
    intro r s h
    apply Q.reactionInjective
    apply Prod.ext
    · exact (decode_encodeBimolComplex _ (hr r)).symm.trans
        ((congrArg (fun e => e.1.decode) h).trans
          (decode_encodeBimolComplex _ (hr s)))
    · exact (decode_encodeBimolComplex _ (hp r)).symm.trans
        ((congrArg (fun e => e.2.decode) h).trans
          (decode_encodeBimolComplex _ (hp s)))

theorem encodeBimolNetwork_toNetwork (Q : SmallPlanarNetwork 5)
    (hr : Q.ReactantsAtMost 2) (hp : Q.ProductsAtMost 2) :
    (encodeBimolNetwork Q hr hp).toNetwork = Q := by
  cases Q with
  | mk reactant product hno hinj =>
    simp only [encodeBimolNetwork, CodedBimolNetwork.toNetwork]
    congr
    · funext r
      exact decode_encodeBimolComplex _ (hr r)
    · funext r
      exact decode_encodeBimolComplex _ (hp r)

theorem bimolecular_cusp_requires_four_reactants (Q : SmallPlanarNetwork 5)
    (hQ : IsPlanarBimolecular252 Q) (hcusp : AdmitsTransverseCusp Q) :
    4 ≤ (codedReactantSupport
      (encodeBimolNetwork Q hQ.1 hQ.2.1)).card := by
  by_contra h
  have hcard : (codedReactantSupport
      (encodeBimolNetwork Q hQ.1 hQ.2.1)).card ≤ 3 := by omega
  have hnot := coded_fewReactant_excludes_cusp
    (encodeBimolNetwork Q hQ.1 hQ.2.1) hcard
  apply hnot
  simpa [encodeBimolNetwork_toNetwork Q hQ.1 hQ.2.1] using hcusp

end SmallCusp

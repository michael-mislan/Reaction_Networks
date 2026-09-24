import proofs.RAFReactionCriticality.SecondOrder

namespace RAFReactionCriticality.ExposureVariance
open FiniteThinning FiniteProductDerivative
open scoped BigOperators
variable {R I : Type*} [Fintype R] [DecidableEq R] [Fintype I]

noncomputable def indicator (E : Finset R) (m : R → Bool) : ℝ := by
  classical
  exact if Contains E m then 1 else 0

noncomputable def variance (p : ℝ) (X : (R → Bool) → ℝ) : ℝ :=
  expectation (fun m => X m ^ 2) p - (expectation X p)^2

theorem expectation_sum (X : I → (R → Bool) → ℝ) (p : ℝ) :
    expectation (fun m => ∑ i, X i m) p = ∑ i, expectation (X i) p := by
  unfold expectation
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

theorem indicator_mean (E : Finset R) (p : ℝ) :
    expectation (indicator E) p = p^E.card := by
  have he : expectation (indicator E) p = probability p (Contains E) := by
    unfold expectation probability indicator
    apply Finset.sum_congr rfl
    intro m _
    split <;> simp_all
  rw [he,contains_probability]

omit [Fintype R] in
theorem joint_indicator (E G : Finset R) (m : R → Bool) :
    indicator E m * indicator G m = indicator (E ∪ G) m := by
  classical
  unfold indicator
  rw [contains_union]
  by_cases h : Contains E m <;> by_cases k : Contains G m <;> simp [h,k]

/-- Exact variance of the number of retained exposure witnesses. -/
theorem exposure_variance (E : I → Finset R) (p : ℝ) :
    variance p (fun m => ∑ i, indicator (E i) m) =
      ∑ i, ∑ j, (p^(E i ∪ E j).card - p^((E i).card+(E j).card)) := by
  have hs : (fun m => (∑ i, indicator (E i) m)^2) =
      (fun m => ∑ i, ∑ j, indicator (E i ∪ E j) m) := by
    funext m
    simp only [pow_two,Finset.sum_mul,Finset.mul_sum,joint_indicator]
    exact Finset.sum_comm
  unfold variance
  rw [hs,expectation_sum]
  simp_rw [expectation_sum,indicator_mean]
  simp only [pow_two,Finset.sum_mul,Finset.mul_sum,Finset.sum_sub_distrib,pow_add]
  congr 1
  exact Finset.sum_comm

end RAFReactionCriticality.ExposureVariance

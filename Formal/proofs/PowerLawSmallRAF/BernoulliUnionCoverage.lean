import proofs.PowerLawSmallRAF.BernoulliUnionLaw

namespace PowerLawSmallRAF
open scoped BigOperators
noncomputable section
variable {I : Type*} [Fintype I]

theorem bernoulliUnionParameter_bounds (p : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    0 ≤ bernoulliUnionParameter p ∧ bernoulliUnionParameter p ≤ 1 := by
  have h0 : 0 ≤ ∏ i, (1-p i) := Finset.prod_nonneg (fun i _ => sub_nonneg.mpr (hp1 i))
  have h1 : (∏ i, (1-p i)) ≤ 1 := Finset.prod_le_one
    (fun i _ => sub_nonneg.mpr (hp1 i)) (fun i _ => by linarith [hp i])
  unfold bernoulliUnionParameter
  constructor <;> linarith

theorem bernoulliUnionParameter_ge_exp (p : I → ℝ) (hp1 : ∀ i, p i ≤ 1) :
    1-Real.exp (-(∑ i, p i)) ≤ bernoulliUnionParameter p := by
  have hprod : (∏ i, (1-p i)) ≤ ∏ i, Real.exp (-p i) := by
    apply Finset.prod_le_prod
    · intro i _
      exact sub_nonneg.mpr (hp1 i)
    · intro i _
      linarith only [Real.add_one_le_exp (-p i)]
  have he : (∏ i, Real.exp (-p i)) = Real.exp (-(∑ i, p i)) := by
    rw [← Real.exp_sum, Finset.sum_neg_distrib]
  rw [he] at hprod
  unfold bernoulliUnionParameter
  linarith

end
end PowerLawSmallRAF

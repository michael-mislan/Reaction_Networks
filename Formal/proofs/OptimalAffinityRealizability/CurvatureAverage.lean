import proofs.OptimalAffinityRealizability.SharpCapacity

namespace OptimalAffinityRealizability

open scoped BigOperators
noncomputable section

def curvatureProbability {n : ℕ} (lambda g : Fin n → ℝ) : Fin n → ℝ :=
  fun i => lambda i * g i / dotProduct lambda g

theorem curvatureProbability_nonnegative {n : ℕ} (lambda g : Fin n → ℝ)
    (hlambda : ∀ i, 0 ≤ lambda i) (hg : ∀ i, 0 < g i)
    (hdenom : 0 < dotProduct lambda g) :
    ∀ i, 0 ≤ curvatureProbability lambda g i := by
  intro i
  exact div_nonneg (mul_nonneg (hlambda i) (le_of_lt (hg i)))
    (le_of_lt hdenom)

theorem curvatureProbability_sum_one {n : ℕ} (lambda g : Fin n → ℝ)
    (hdenom : dotProduct lambda g ≠ 0) :
    ∑ i, curvatureProbability lambda g i = 1 := by
  unfold curvatureProbability dotProduct
  rw [← Finset.sum_div]
  exact div_self hdenom

theorem curvatureQuotient_eq_weightedAverage {n : ℕ}
    (source : SquareSource n) (g u lambda : Fin n → ℝ) :
    dotProduct lambda (curvatureWeight source g u) /
        dotProduct lambda g =
      ∑ i, curvatureProbability lambda g i *
        (source.reactant.transpose.mulVec u i *
          source.product.transpose.mulVec u i) := by
  unfold dotProduct curvatureWeight curvatureProbability
  calc
    (∑ i, lambda i *
        (g i * source.reactant.transpose.mulVec u i *
          source.product.transpose.mulVec u i)) /
        (∑ i, lambda i * g i) =
      (∑ i, (lambda i * g i) *
        (source.reactant.transpose.mulVec u i *
          source.product.transpose.mulVec u i)) /
        (∑ i, lambda i * g i) := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = ∑ i, ((lambda i * g i) *
        (source.reactant.transpose.mulVec u i *
          source.product.transpose.mulVec u i)) /
        (∑ i, lambda i * g i) := by rw [Finset.sum_div]
    _ = ∑ i, lambda i * g i / (∑ i, lambda i * g i) *
        (source.reactant.transpose.mulVec u i *
          source.product.transpose.mulVec u i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring

/-- The normalized negative curvature is exactly a probability-weighted
average of the reactionwise response products. -/
theorem normalizedCurvature_eq_weightedAverage {n : ℕ}
    (source : SquareSource n) (J J₂ : ℝ)
    (g q u v lambda : Fin n → ℝ)
    (hJ : J ≠ 0)
    (hq : ∀ i, 1 < q i)
    (hratio : ∀ i, source.product.transpose.mulVec u i =
      q i * source.reactant.transpose.mulVec u i)
    (hannih : ∀ w : Fin n → ℝ,
      dotProduct lambda
        ((literalCurrentJacobian source J g q).mulVec w) = 0)
    (hcoupled : reactionCurrentSecondJet source J g q u v = J₂ • g)
    (hdenom : dotProduct lambda g ≠ 0) :
    -J₂ / J =
      ∑ i, curvatureProbability lambda g i *
        (source.reactant.transpose.mulVec u i *
          source.product.transpose.mulVec u i) := by
  have hformula := leftNull_curvature_formula source J J₂ g q u v lambda
    hq hratio hannih hcoupled hdenom
  rw [hformula]
  calc
    -(-J * dotProduct lambda (curvatureWeight source g u) /
          dotProduct lambda g) / J =
        dotProduct lambda (curvatureWeight source g u) /
          dotProduct lambda g := by
            field_simp [hJ, hdenom]
    _ = _ := curvatureQuotient_eq_weightedAverage source g u lambda

theorem weightedAverage_between {n : ℕ} (mu x : Fin n → ℝ)
    (lower upper : ℝ) (hmu : ∀ i, 0 ≤ mu i)
    (hsum : ∑ i, mu i = 1)
    (hlower : ∀ i, lower ≤ x i) (hupper : ∀ i, x i ≤ upper) :
    lower ≤ ∑ i, mu i * x i ∧ ∑ i, mu i * x i ≤ upper := by
  constructor
  · calc
      lower = ∑ i, mu i * lower := by rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ ∑ i, mu i * x i := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hlower i) (hmu i)
  · calc
      ∑ i, mu i * x i ≤ ∑ i, mu i * upper := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hupper i) (hmu i)
      _ = upper := by rw [← Finset.sum_mul, hsum, one_mul]

/-- Immediate min/max-style bounds for the normalized curvature, stated with
arbitrary certified lower and upper reactionwise bounds. -/
theorem normalizedCurvature_between {n : ℕ}
    (source : SquareSource n) (J J₂ : ℝ)
    (g q u v lambda : Fin n → ℝ) (lower upper : ℝ)
    (hJ : J ≠ 0) (hg : ∀ i, 0 < g i)
    (hlambda : ∀ i, 0 ≤ lambda i) (hlambda0 : lambda ≠ 0)
    (hq : ∀ i, 1 < q i)
    (hratio : ∀ i, source.product.transpose.mulVec u i =
      q i * source.reactant.transpose.mulVec u i)
    (hannih : ∀ w : Fin n → ℝ,
      dotProduct lambda
        ((literalCurrentJacobian source J g q).mulVec w) = 0)
    (hcoupled : reactionCurrentSecondJet source J g q u v = J₂ • g)
    (hlower : ∀ i, lower ≤ source.reactant.transpose.mulVec u i *
      source.product.transpose.mulVec u i)
    (hupper : ∀ i, source.reactant.transpose.mulVec u i *
      source.product.transpose.mulVec u i ≤ upper) :
    lower ≤ -J₂ / J ∧ -J₂ / J ≤ upper := by
  have hdenom : 0 < dotProduct lambda g :=
    dotProduct_pos_of_nonnegative_nonzero_left lambda g hlambda hlambda0 hg
  rw [normalizedCurvature_eq_weightedAverage source J J₂ g q u v lambda
    hJ hq hratio hannih hcoupled (ne_of_gt hdenom)]
  exact weightedAverage_between (curvatureProbability lambda g)
    (fun i => source.reactant.transpose.mulVec u i *
      source.product.transpose.mulVec u i) lower upper
    (curvatureProbability_nonnegative lambda g hlambda hg hdenom)
    (curvatureProbability_sum_one lambda g (ne_of_gt hdenom)) hlower hupper

end
end OptimalAffinityRealizability

import proofs.OptimalAffinityRealizability.ResponseLaplacian

namespace OptimalAffinityRealizability

open Matrix
open scoped BigOperators
noncomputable section

/-- The response transport normalized by its positive profile and response ratio. -/
def routingMatrix {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ)
    (q f : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => T.transpose i j * f j / (q i * f i)

/-- The convention needed below: every row has total mass one. -/
def RowStochastic {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i, ∑ j, P i j = 1

theorem routingMatrix_rowStochastic {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℝ) (q f h : Fin n → ℝ)
    (hresponse : T.transpose.mulVec f = h)
    (hratio : ∀ i, h i = q i * f i)
    (hf : ∀ i, 0 < f i) (hq : ∀ i, 0 < q i) :
    RowStochastic (routingMatrix T q f) := by
  intro i
  unfold routingMatrix
  rw [← Finset.sum_div]
  change T.transpose.mulVec f i / (q i * f i) = 1
  rw [hresponse, hratio i]
  exact div_self (mul_ne_zero (ne_of_gt (hq i)) (ne_of_gt (hf i)))

theorem responseLaplacian_routing_factorization {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℝ) (q f : Fin n → ℝ)
    (hf : ∀ i, 0 < f i) (hq : ∀ i, 0 < q i) :
    responseLaplacian T q =
      Matrix.diagonal (fun i => q i * f i) *
        (1 - routingMatrix T q f) *
          Matrix.diagonal (fun i => (f i)⁻¹) := by
  ext i j
  simp [responseLaplacian, routingMatrix]
  by_cases hij : i = j
  · subst j
    simp
    field_simp [ne_of_gt (hf i), ne_of_gt (hq i)]
  · simp [hij]
    field_simp [ne_of_gt (hf i), ne_of_gt (hf j), ne_of_gt (hq i)]

end
end OptimalAffinityRealizability

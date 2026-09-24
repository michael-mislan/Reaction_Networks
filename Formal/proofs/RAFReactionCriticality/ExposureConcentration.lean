import proofs.RAFReactionCriticality.ExposureVariance

namespace RAFReactionCriticality.ExposureVariance
open FiniteThinning FiniteProductDerivative
open scoped BigOperators
variable {R I : Type*} [Fintype R] [DecidableEq R] [Fintype I]

omit [Fintype R] in
theorem covariance_bounds (E G : Finset R) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ p^(E ∪ G).card-p^(E.card+G.card) ∧
      p^(E ∪ G).card-p^(E.card+G.card) ≤ if (E ∩ G).Nonempty then 1 else 0 := by
  classical
  constructor
  · exact sub_nonneg.mpr (pow_le_pow_of_le_one hp hp1 (Finset.card_union_le E G))
  · by_cases h : (E ∩ G).Nonempty
    · rw [if_pos h]
      have h1 : p^(E ∪ G).card ≤ 1 := pow_le_one₀ hp hp1
      have h0 : 0 ≤ p^(E.card+G.card) := pow_nonneg hp _
      linarith
    · rw [if_neg h]
      have hc := Finset.card_union_add_card_inter E G
      have he : (E ∩ G).card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp h)
      rw [he,Nat.add_zero] at hc
      rw [hc,sub_self]

theorem exposure_bounds (E : I → Finset R) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ variance p (fun m => ∑ i, indicator (E i) m) ∧
      variance p (fun m => ∑ i, indicator (E i) m) ≤
      ∑ i, ∑ j, if (E i ∩ E j).Nonempty then (1 : ℝ) else 0 := by
  classical
  rw [exposure_variance]
  constructor
  · exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => (covariance_bounds (E i) (E j) hp hp1).1))
  · exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => (covariance_bounds (E i) (E j) hp hp1).2))

end RAFReactionCriticality.ExposureVariance

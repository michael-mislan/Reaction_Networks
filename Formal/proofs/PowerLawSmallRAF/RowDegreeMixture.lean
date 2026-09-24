import proofs.PowerLawSmallRAF.ProductRowCoupling
import proofs.PowerLawSmallRAF.PowerLawFibreModel

namespace PowerLawSmallRAF

open scoped BigOperators
noncomputable section

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [Fintype I] [DecidableEq I] [DecidableEq J] in
theorem uniformFixedRowWeight_degree_mixture (mu : Nat → ℝ) (T : Finset J) :
    (∑ d : Fin (Fintype.card J + 1), mu d * uniformFixedRowWeight d T) =
      subsetDegreeWeight mu T := by
  classical
  let k : Fin (Fintype.card J + 1) := ⟨T.card, Nat.lt_succ_of_le (Finset.card_le_univ T)⟩
  rw [Finset.sum_eq_single k]
  · simp [uniformFixedRowWeight, subsetDegreeWeight, k, div_eq_mul_inv]
  · intro d _ hdk
    have hne : T.card ≠ d.val := by
      intro h
      apply hdk
      apply Fin.ext
      exact h.symm
    simp [uniformFixedRowWeight, hne]
  · simp

omit [DecidableEq J] in
theorem uniformFixedRowsWeight_degree_mixture (mu : I → Nat → ℝ) (T : I → Finset J) :
    (∑ d : I → Fin (Fintype.card J + 1),
      (∏ i, mu i (d i)) * uniformFixedRowsWeight (fun i => d i) T) =
      ∏ i, subsetDegreeWeight (mu i) (T i) := by
  simp only [uniformFixedRowsWeight, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (d : Fin (Fintype.card J + 1)) =>
    mu i d * uniformFixedRowWeight d (T i))]
  apply Finset.prod_congr rfl
  intro i _
  exact uniformFixedRowWeight_degree_mixture (mu i) (T i)

theorem bernoulliRows_degree_mixture_event_le (mu : I → Nat → ℝ)
    (hmu : ∀ i d, 0 ≤ mu i d)
    (p : (I → Fin (Fintype.card J + 1)) → I → ℝ)
    (hp : ∀ d i, 0 ≤ p d i) (hp1 : ∀ d i, p d i ≤ 1)
    (F : (I → Finset J) → Prop) [DecidablePred F]
    (hmono : ∀ B T, (∀ i, B i ⊆ T i) → F B → F T) :
    (∑ d : I → Fin (Fintype.card J + 1), (∏ i, mu i (d i)) *
      ∑ B : I → Finset J, if F B then bernoulliRowsWeight (p d) B else 0) ≤
      (∑ T : I → Finset J, if F T then ∏ i, subsetDegreeWeight (mu i) (T i) else 0) +
      ∑ d : I → Fin (Fintype.card J + 1), (∏ i, mu i (d i)) *
        ∑ i, bernoulliRowOverflowMass (J := J) (p d i) (d i) := by
  classical
  have hsource :
      (∑ d : I → Fin (Fintype.card J + 1), (∏ i, mu i (d i)) *
        ∑ T : I → Finset J, if F T then uniformFixedRowsWeight (fun i => d i) T else 0) =
      ∑ T : I → Finset J, if F T then ∏ i, subsetDegreeWeight (mu i) (T i) else 0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro T _
    by_cases hT : F T
    · simp only [if_pos hT]
      exact uniformFixedRowsWeight_degree_mixture mu T
    · simp [hT]
  calc
    _ ≤ ∑ d : I → Fin (Fintype.card J + 1), (∏ i, mu i (d i)) *
        ((∑ T : I → Finset J, if F T then uniformFixedRowsWeight (fun i => d i) T else 0) +
          ∑ i, bernoulliRowOverflowMass (J := J) (p d i) (d i)) := by
      apply Finset.sum_le_sum
      intro d _
      apply mul_le_mul_of_nonneg_left
      · exact bernoulliRows_increasing_event_le_uniform_tail (p d) (fun i => d i)
          (hp d) (hp1 d) (fun i => Nat.le_of_lt_succ (d i).isLt) F hmono
      · exact Finset.prod_nonneg (fun i _ => hmu i (d i))
    _ = _ := by simp only [mul_add, Finset.sum_add_distrib, hsource]

end
end PowerLawSmallRAF

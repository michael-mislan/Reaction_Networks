import Mathlib

namespace RAF.Frankl

open scoped BigOperators

variable {X U V : Type*} [Fintype U] [DecidableEq U]
  [Fintype V] [DecidableEq V]

/-- Fibrewise occupancy bounds imply a single global abundant coordinate. -/
theorem exists_frequency_of_fibre_average [Nonempty U]
    (F : Finset X) (left : X → Finset U) (right : X → V)
    (h : ∀ t : V,
      (F.filter (fun x => right x = t)).card * Fintype.card U ≤
        2 * ∑ x ∈ F.filter (fun x => right x = t), (left x).card) :
    ∃ r : U, F.card ≤ 2 * (F.filter (fun x => r ∈ left x)).card := by
  classical
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun t _ => h t)
  have hc : (∑ t : V, (F.filter (fun x => right x = t)).card) = F.card := by
    simpa using Finset.sum_card_fiberwise_eq_card_filter F (Finset.univ : Finset V) right
  have hs : (∑ t : V, ∑ x ∈ F.filter (fun x => right x = t), (left x).card) =
      ∑ x ∈ F, (left x).card := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    simp
  simp only [← Finset.sum_mul, ← Finset.mul_sum] at hsum
  rw [hc,hs] at hsum
  have hi : (∑ x ∈ F, (left x).card) =
      ∑ r : U, (F.filter (fun x => r ∈ left x)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    simp
  rw [hi, Finset.mul_sum] at hsum
  by_contra hn
  push Not at hn
  have hlt : (∑ r : U, 2 * (F.filter (fun x => r ∈ left x)).card) <
      ∑ _r : U, F.card :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun r _ => hn r)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hlt
  rw [Nat.mul_comm (Fintype.card U) F.card] at hlt
  omega

end RAF.Frankl

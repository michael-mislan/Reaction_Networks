import Mathlib

namespace RAFReactionCriticality.FiniteThinning
open scoped BigOperators
variable {R : Type*} [Fintype R] [DecidableEq R]

def weight (p : ℝ) (mask : R → Bool) : ℝ :=
  ∏ r, if mask r then p else 1-p

def Contains (O : Finset R) (mask : R → Bool) : Prop := ∀ r ∈ O, mask r = true

noncomputable def probability (p : ℝ) (event : (R → Bool) → Prop) : ℝ := by
  classical
  exact ∑ mask, if event mask then weight p mask else 0

theorem contains_probability (p : ℝ) (O : Finset R) :
    probability p (Contains O) = p ^ O.card := by
  classical
  let g : R → Bool → ℝ := fun r b =>
    if r ∈ O ∧ b = false then 0 else if b then p else 1-p
  have term (mask : R → Bool) :
      (if Contains O mask then weight p mask else 0) = ∏ r, g r (mask r) := by
    by_cases h : Contains O mask
    · rw [if_pos h]
      apply Finset.prod_congr rfl
      intro r _
      have hn : ¬ (r ∈ O ∧ mask r = false) := by
        rintro ⟨hr, hb⟩
        have ht := h r hr
        simp [hb] at ht
      simp [g, hn]
    · rw [if_neg h]
      symm
      simp only [Contains, not_forall] at h
      obtain ⟨r, hr, hb⟩ := h
      have hf : mask r = false := Bool.eq_false_iff.mpr hb
      exact Finset.prod_eq_zero (Finset.mem_univ r) (by simp [g, hr, hf])
  unfold probability
  simp_rw [term]
  rw [← Fintype.prod_sum]
  have factor (r : R) : (∑ b : Bool, g r b) = if r ∈ O then p else 1 := by
    by_cases hr : r ∈ O <;> simp [g, hr]
  simp_rw [factor]
  rw [Finset.prod_ite_mem_eq]
  simp

omit [Fintype R] in
theorem contains_union (O T : Finset R) (mask : R → Bool) :
    Contains (O ∪ T) mask ↔ Contains O mask ∧ Contains T mask := by
  constructor
  · intro h
    exact ⟨fun r hr => h r (Finset.mem_union_left T hr),
      fun r hr => h r (Finset.mem_union_right O hr)⟩
  · rintro ⟨ho, ht⟩ r hr
    exact (Finset.mem_union.mp hr).elim (ho r) (ht r)

theorem two_witness_probability (p : ℝ) (O T : Finset R) :
    probability p (fun mask => Contains O mask ∨ Contains T mask) =
      p^O.card + p^T.card - p^(O ∪ T).card := by
  classical
  calc
    probability p (fun mask => Contains O mask ∨ Contains T mask) =
        ∑ mask, ((if Contains O mask then weight p mask else 0) +
          (if Contains T mask then weight p mask else 0) -
          (if Contains (O ∪ T) mask then weight p mask else 0)) :=
      Finset.sum_congr rfl (fun mask _ => by
        by_cases ho : Contains O mask <;> by_cases ht : Contains T mask <;>
          simp [ho, ht, contains_union])
    _ = probability p (Contains O) + probability p (Contains T) -
        probability p (Contains (O ∪ T)) := by
      simp only [probability, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ = _ := by rw [contains_probability, contains_probability, contains_probability]

omit [DecidableEq R] in
theorem weight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (mask : R → Bool) :
    0 ≤ weight p mask := by
  apply Finset.prod_nonneg
  intro r _
  split
  · exact hp
  · linarith

theorem weight_sum (p : ℝ) : (∑ mask : R → Bool, weight p mask) = 1 := by
  simpa [probability, Contains] using contains_probability p (∅ : Finset R)

end RAFReactionCriticality.FiniteThinning

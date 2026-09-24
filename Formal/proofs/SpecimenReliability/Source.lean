import Mathlib

namespace SpecimenReliability
noncomputable section
open scoped BigOperators

/-- A target is unprocessed, lost in preparation 1, detected in preparation 1,
lost in preparation 2, or detected in preparation 2. Fractions include downstream
coverage; a target can be assigned to at most one preparation. -/
def path (a b x y : ℝ) : Fin 5 → ℝ :=
  ![1-a-b, a*(1-x), a*x, b*(1-y), b*y]

def negative : Fin 5 → Bool := ![true, true, false, true, false]

theorem path_normalized (a b x y : ℝ) : ∑ j, path a b x y j = 1 := by
  simp [path, Fin.sum_univ_succ]
  ring

theorem path_nonneg (a b x y : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a+b ≤ 1) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    ∀ j, 0 ≤ path a b x y j := by
  intro j
  have hx' : 0 ≤ 1-x := sub_nonneg.mpr hx.2
  have hy' : 0 ≤ 1-y := sub_nonneg.mpr hy.2
  fin_cases j
  · change 0 ≤ 1-a-b; linarith
  · exact mul_nonneg ha hx'
  · exact mul_nonneg ha hx.1
  · exact mul_nonneg hb hy'
  · exact mul_nonneg hb hy.1

theorem path_negative (a b x y : ℝ) :
    (∑ j, if negative j then path a b x y j else 0) = 1-a*x-b*y := by
  norm_num [negative, path, Fin.sum_univ_succ]
  ring

def histories (a b x y : ℝ) (n : ℕ) : ℝ :=
  ∑ h : Fin n → Fin 5, ∏ i, path a b x y (h i)

def negativeHistories (a b x y : ℝ) (n : ℕ) : ℝ :=
  ∑ h : Fin n → Fin 5, ∏ i, if negative (h i) then path a b x y (h i) else 0

theorem histories_normalized (a b x y : ℝ) (n : ℕ) : histories a b x y n = 1 := by
  rw [histories, ← Fintype.sum_pow, path_normalized, one_pow]

theorem negative_histories (a b x y : ℝ) (n : ℕ) :
    negativeHistories a b x y n = (1-a*x-b*y)^n := by
  unfold negativeHistories
  rw [← Fintype.sum_pow (fun j => if negative j then path a b x y j else 0) n,
    path_negative]

/-- Recovery is sampled once per specimen, outside the product over targets. -/
def sourceRisk {S : Type*} [Fintype S] (μ x y : S → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  ∑ s, μ s * negativeHistories a b (x s) (y s) n

theorem source_law {S : Type*} [Fintype S] (μ x y : S → ℝ)
    (a b : ℝ) (n : ℕ) :
    sourceRisk μ x y a b n = ∑ s, μ s * (1-a*x s-b*y s)^n := by
  simp only [sourceRisk, negative_histories]

theorem miss_unit_interval (a b x y : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a+b ≤ 1) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    0 ≤ 1-a*x-b*y ∧ 1-a*x-b*y ≤ 1 := by
  have hax := mul_le_mul_of_nonneg_left hx.2 ha
  have hby := mul_le_mul_of_nonneg_left hy.2 hb
  constructor
  · nlinarith
  · nlinarith [mul_nonneg ha hx.1, mul_nonneg hb hy.1]

end
end SpecimenReliability

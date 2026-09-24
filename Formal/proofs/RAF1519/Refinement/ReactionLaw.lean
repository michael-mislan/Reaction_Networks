import Mathlib

namespace RAF1519.Refinement
noncomputable section
open scoped BigOperators
open Classical

/-- Integer reactants and products; the coefficient is separate from volume scaling. -/
structure Reaction (ι : Type*) where
  consume : ι → ℕ
  produce : ι → ℕ
  coefficient : ℝ

namespace Reaction
variable {ι : Type*} [Fintype ι]

def enabled (R : Reaction ι) (N : ι → ℕ) : Prop := ∀ i, R.consume i ≤ N i

def next (R : Reaction ι) (N : ι → ℕ) : ι → ℕ :=
  if R.enabled N then fun i => N i-R.consume i+R.produce i else N

/-- Literal falling-factorial mass action, including the zero-order feed convention. -/
def rate (R : Reaction ι) (V : ℝ) (N : ι → ℕ) : ℝ :=
  R.coefficient*V*∏ i, (N i).descFactorial (R.consume i)/V^(R.consume i)

theorem rate_nonnegative (R : Reaction ι) (V : ℝ) (hV : 0 ≤ V)
    (hc : 0 ≤ R.coefficient) (N : ι → ℕ) : 0 ≤ R.rate V N := by
  unfold rate
  positivity

theorem rate_disabled (R : Reaction ι) (V : ℝ) (N : ι → ℕ)
    (h : ¬ R.enabled N) : R.rate V N = 0 := by
  unfold enabled at h
  push Not at h
  obtain ⟨i,hi⟩ := h
  have hz : (N i).descFactorial (R.consume i) = 0 := Nat.descFactorial_of_lt hi
  unfold rate
  have hp : (∏ j, ((N j).descFactorial (R.consume j):ℝ)/V^(R.consume j)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [hz,Nat.cast_zero,zero_div]
  rw [hp,mul_zero]

omit [Fintype ι] in
theorem next_of_enabled (R : Reaction ι) (N : ι → ℕ) (h : R.enabled N) (i : ι) :
    (R.next N i:ℝ)-(N i:ℝ) = (R.produce i:ℝ)-(R.consume i:ℝ) := by
  simp only [next,if_pos h,Nat.cast_add,Nat.cast_sub (h i)]
  ring

theorem rate_increment (R : Reaction ι) (V : ℝ) (N : ι → ℕ) (i : ι) :
    R.rate V N*((R.next N i:ℝ)-(N i:ℝ)) =
      R.rate V N*((R.produce i:ℝ)-(R.consume i:ℝ)) := by
  by_cases h : R.enabled N
  · rw [R.next_of_enabled N h i]
  · rw [R.rate_disabled V N h]
    simp

def material (w : ι → ℝ) (N : ι → ℕ) : ℝ := ∑ i, w i*(N i:ℝ)

theorem material_increment (R : Reaction ι) (V : ℝ) (N : ι → ℕ) (w : ι → ℝ) :
    R.rate V N*(material w (R.next N)-material w N) =
      R.rate V N*(∑ i, w i*((R.produce i:ℝ)-(R.consume i:ℝ))) := by
  unfold material
  rw [← Finset.sum_sub_distrib]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = w i*(R.rate V N*((R.next N i:ℝ)-(N i:ℝ))) := by ring
    _ = w i*(R.rate V N*((R.produce i:ℝ)-(R.consume i:ℝ))) := by rw [rate_increment]
    _ = _ := by ring

end Reaction
end
end RAF1519.Refinement

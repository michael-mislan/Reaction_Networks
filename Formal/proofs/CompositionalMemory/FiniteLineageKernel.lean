import Mathlib

namespace CompositionalMemory
open scoped ENNReal

/-- A copying-cycle kernel keeps successful offspring transitions and assigns
all missing mass to failure. Its probabilities may depend on the newborn state. -/
structure FiniteLineageKernel (α : Type*) [Fintype α] where
  weight : α → α → ℝ≥0∞
  total_le_one : ∀ x, ∑ y, weight x y ≤ 1

namespace FiniteLineageKernel
variable {α : Type*} [Fintype α] (P : FiniteLineageKernel α)

noncomputable def survival (P : FiniteLineageKernel α) : Nat → α → ℝ≥0∞
  | 0, _ => 1
  | n+1, x => ∑ y, P.weight x y*survival P n y

theorem survival_le_one (n : Nat) (x : α) : P.survival n x ≤ 1 := by
  induction n generalizing x with
  | zero => exact le_rfl
  | succ n ih =>
    calc
      _ ≤ ∑ y,P.weight x y*1 := Finset.sum_le_sum (fun y _ => mul_le_mul_right (ih y) _)
      _ ≤ 1 := by simpa using P.total_le_one x

theorem survival_lower (p : ℝ≥0∞) (h : ∀ x, p ≤ ∑ y,P.weight x y)
    (n : Nat) (x : α) : p^n ≤ P.survival n x := by
  induction n generalizing x with
  | zero => simp [survival]
  | succ n ih =>
    calc
      _ = p*p^n := by rw [pow_succ]; exact mul_comm _ _
      _ ≤ (∑ y,P.weight x y)*p^n := mul_le_mul_left (h x) _
      _ = ∑ y,P.weight x y*p^n := Finset.sum_mul _ _ _
      _ ≤ P.survival (n+1) x := Finset.sum_le_sum (fun y _ => mul_le_mul_right (ih y) _)

/-- Ten inspected cycles require no unconditional independence between
generations; the same uniform conditional lower bound suffices. -/
theorem ten_cycles (h : ∀ x, (9901/10000 : ℝ≥0∞) ≤ ∑ y,P.weight x y) (x : α) :
    (9/10 : ℝ≥0∞) ≤ P.survival 10 x := by
  apply le_trans _ (P.survival_lower (9901/10000) h 10 x)
  have hr : (9/10 : ℝ) ≤ (9901/10000 : ℝ)^10 := by norm_num
  have he := ENNReal.ofReal_le_ofReal hr
  rw [ENNReal.ofReal_pow (by norm_num)] at he
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 10),
    ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 10000)] at he
  norm_num only [ENNReal.ofReal_ofNat] at he
  exact he

end FiniteLineageKernel
end CompositionalMemory

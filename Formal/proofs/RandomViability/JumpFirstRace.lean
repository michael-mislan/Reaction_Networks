import proofs.RandomViability.PoissonFirstRace
import proofs.RandomViability.JumpRewardPaths

namespace RandomViability
open Classical FiniteCopy
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]

def markedLabel (A : β → Prop) : Option β → Prop
  | none => False
  | some b => A b

theorem labeled_marked_sum (M : FiniteJumpModel α β) (q : ℝ) (hq : 0 < q)
    (hbound : ∀ x, M.total x ≤ q) (A : β → Prop) (x : α) :
    (∑ b, if markedLabel A b then (labeledUniformize M q hq hbound).prob x b else 0) =
      (∑ b, if A b then M.rate x b else 0)/q := by
  simp [Fintype.sum_option, markedLabel, labeledUniformize, Finset.sum_div, ite_div]

theorem jump_firstRace_lower (M : FiniteJumpModel α β) (q : NNReal) (hq : 0 < (q : ℝ))
    (hbound : ∀ x, M.total x ≤ q) (marked target : β → Prop)
    (ell Λ : ℝ) (hell : 0 ≤ ell) (hΛ : 0 < Λ) (hΛq : Λ ≤ q)
    (htarget : ∀ x, ell ≤ ∑ b, if marked b ∧ target b then M.rate x b else 0)
    (hmarked : ∀ x, (∑ b, if marked b then M.rate x b else 0) ≤ Λ)
    (t : NNReal) (x : α) :
    ell/Λ*(1-Real.exp (-Λ*t)) ≤
      (labeledUniformize M q hq hbound).poissonEventMass (q*t) x
        (FiniteLabeledKernel.firstRace (markedLabel marked) (markedLabel target)) := by
  have ht : ∀ y, ell/(q : ℝ) ≤ ∑ b, if markedLabel marked b ∧ markedLabel target b then
      (labeledUniformize M q hq hbound).prob y b else 0 := by
    intro y
    calc
      _ ≤ (∑ b, if marked b ∧ target b then M.rate y b else 0)/(q : ℝ) :=
        div_le_div_of_nonneg_right (htarget y) hq.le
      _ = _ := by
        rw [Finset.sum_div, Fintype.sum_option]
        simp only [markedLabel, false_and, if_false, zero_add]
        apply Finset.sum_congr rfl
        intro z _
        by_cases hm : marked z <;> by_cases ht : target z <;>
          simp [labeledUniformize, hm, ht]
  have hm : ∀ y, (∑ b, if markedLabel marked b then (labeledUniformize M q hq hbound).prob y b else 0) ≤ Λ/(q : ℝ) := by
    intro y
    rw [labeled_marked_sum]
    exact div_le_div_of_nonneg_right (hmarked y) hq.le
  have hh := FiniteLabeledKernel.firstRace_poisson_lower (labeledUniformize M q hq hbound)
    (markedLabel marked) (markedLabel target) (ell/q) (Λ/q) (div_nonneg hell hq.le)
    (div_pos hΛ hq) ((div_le_one hq).mpr hΛq) ht hm (q*t) x
  have he : (ell/(q : ℝ))/(Λ/q) = ell/Λ := by field_simp
  have hex : -(Λ/(q : ℝ))*((q*t : NNReal) : ℝ) = -Λ*t := by
    simp only [NNReal.coe_mul]
    field_simp
  simpa only [he, hex] using hh

end
end RandomViability


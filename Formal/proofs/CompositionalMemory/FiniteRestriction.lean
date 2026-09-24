import proofs.FiniteCopy.FiniteJump

namespace CompositionalMemory
open Classical FiniteCopy
open scoped ENNReal
noncomputable section
variable {α β : Type*} [Fintype β]

abbrev RestrictedState (D : Finset α) := Option {x : α // x ∈ D}

def finiteRestrictionModel (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (D : Finset α) : FiniteJumpModel (RestrictedState D) β where
  next x b := match x with
    | none => none
    | some x => if h : next x.val b ∈ D then some ⟨next x.val b,h⟩ else none
  rate x b := match x with
    | none => 0
    | some x => rate x.val b
  nonneg x b := by cases x with
    | none => exact le_rfl
    | some x => exact hr x.val b

def restrictionValue (D : Finset α) (f : α → ℝ≥0∞) : RestrictedState D → ℝ≥0∞
  | none => 0
  | some x => f x.val

theorem restriction_total_some (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (D : Finset α) (x : {x : α // x ∈ D}) :
    (finiteRestrictionModel next rate hr D).total (some x)=∑ b,rate x.val b := rfl

theorem restriction_next_value (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (D : Finset α) (f : α → ℝ≥0∞)
    (hf : ∀ x,x ∉ D → f x=0) (x : {x : α // x ∈ D}) (b : β) :
    restrictionValue D f ((finiteRestrictionModel next rate hr D).next (some x) b)=f (next x.val b) := by
  by_cases h : next x.val b ∈ D
  · simp [finiteRestrictionModel,restrictionValue,h]
  · simp [finiteRestrictionModel,restrictionValue,h,hf _ h]

end
end CompositionalMemory

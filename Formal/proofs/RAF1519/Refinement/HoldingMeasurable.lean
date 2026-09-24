import proofs.RAF1519.Refinement.HoldingIndex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.Pi

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory

theorem holdingClock_measurable (j : ℕ) : Measurable (fun h : ℕ → ℝ => holdingClock h j) := by
  unfold holdingClock
  fun_prop

/-- The default index on paths without a covering interval is measurable too. -/
theorem holdingIndex_measurable (t : ℝ) : Measurable (fun h : ℕ → ℝ => holdingIndex h t) := by
  let A : ℕ → Set (ℕ → ℝ) := fun j => {h | holdingClock h j ≤ t ∧ t < holdingClock h j+h j}
  have hA : ∀ j, MeasurableSet (A j) := fun j =>
    (measurableSet_le (holdingClock_measurable j) measurable_const).inter
      (measurableSet_lt measurable_const ((holdingClock_measurable j).add (measurable_pi_apply j)))
  let E : Set (ℕ → ℝ) := {h | ∃ j, h ∈ A j}
  have hE : MeasurableSet E := by
    change MeasurableSet {h | ∃ j, h ∈ A j}
    simp only [Set.setOf_exists]
    exact MeasurableSet.iUnion hA
  have hf : Measurable (fun h : E => Nat.find h.property) := by
    apply measurable_find (fun h : E => h.property)
    intro j
    exact (hA j).preimage measurable_subtype_coe
  exact Measurable.dite hf measurable_const hE

end
end RAF1519.Refinement

import proofs.RandomViability.JumpWindow
import proofs.RandomViability.JumpTrajectory

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory Set
noncomputable section
set_option maxHeartbeats 20000

variable {α β : Type*} [mα : MeasurableSpace α] [cα : Countable α]
  [sα : MeasurableSingletonClass α] [fβ : Fintype β]
  [mβ : MeasurableSpace β] [sβ : MeasurableSingletonClass β]

def markedWindow (state : α) (label : β) (a d : ℝ) : Set (JumpState α β) :=
  {y | y.1=state ∧ y.2.1=Sum.inr label ∧ y.2.2 ∈ Ioc a (a+d)}

omit cα fβ in
theorem markedWindow_measurable (state : α) (label : β) (a d : ℝ) :
    MeasurableSet (markedWindow state label a d) := by
  have hl : MeasurableSet ((Sum.inr : β → Unit ⊕ β) '' {label}) :=
    (measurableSet_singleton label).inr_image
  have hl' : MeasurableSet ({Sum.inr label} : Set (Unit ⊕ β)) := by simpa using hl
  exact (measurable_fst (measurableSet_singleton state)).inter
    (((measurable_fst.comp measurable_snd) hl').inter
      ((measurable_snd.comp measurable_snd) measurableSet_Ioc))

theorem jumpStateKernel_marked_window (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b)
    (x : α) (b : β) (a d : ℝ) :
    jumpStateKernel next rate hr ht x (markedWindow (next x b) b a d) =
      jumpClockMeasure (rate x) (hr x) (ht x) ({b} ×ˢ Ioc a (a+d)) := by
  change ((jumpClockMeasure (rate x) (hr x) (ht x)).map (jumpStateUpdate next x)) _ = _
  rw [Measure.map_apply (jumpStateUpdate_measurable next x) (markedWindow_measurable _ _ _ _)]
  congr 1
  ext y
  simp only [mem_preimage, markedWindow, mem_setOf_eq, jumpStateUpdate,
    Sum.inr.injEq, mem_prod, mem_singleton_iff]
  constructor
  · exact fun h => ⟨h.2.1,h.2.2⟩
  · rintro ⟨hb,hy⟩
    exact ⟨congrArg (next x) hb,hb,hy⟩

theorem jumpStateKernel_marked_window_lower (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b)
    (x : α) (b : β) (Q a d e : ℝ)
    (hQ : (∑ c,rate x c) ≤ Q) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (he : 0 ≤ e) (hb : e ≤ rate x b) :
    ENNReal.ofReal (e*d*Real.exp (-Q*(a+d))) ≤
      jumpStateKernel next rate hr ht x (markedWindow (next x b) b a d) := by
  rw [jumpStateKernel_marked_window]
  exact jumpClock_window_lower (rate x) (hr x) (ht x) b Q a d e hQ ha hd he hb

end
end RandomViability

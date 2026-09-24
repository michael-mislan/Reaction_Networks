import proofs.RandomViability.CensoredJumpClock
import proofs.RandomViability.PredictableProductBounds

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 80000

variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

theorem censoredStateMultiplier_measurable (w : α → β → ℝ) (s : α → ℝ) :
    Measurable (fun p : α × (ℝ × JumpState α β) => censoredJumpMultiplier (w p.1) (s p.1) p.2.1 p.2.2) := by
  have hs : Measurable s := measurable_of_countable _
  apply Measurable.ite (measurableSet_le measurable_snd.snd.snd.snd measurable_snd.fst)
  · exact (stateDependentMultiplier_measurable w s).comp
      (measurable_fst.prodMk measurable_snd.snd)
  · exact ((((hs.comp measurable_fst).neg.mul measurable_snd.fst).exp).ennreal_ofReal)

def censoredStoppedMultiplier (w : α → β → ℝ) (s : α → ℝ)
    (remaining : (k : ℕ) → (Finset.Iic k → JumpState α β) → ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState α β) → Prop)
    (k : ℕ) (h : Finset.Iic k → JumpState α β) (y : JumpState α β) : ℝ≥0∞ :=
  if stop k h then 1 else censoredJumpMultiplier
    (w (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1) (s (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1)
    (remaining k h) y

theorem censoredStoppedMultiplier_measurable (w : α → β → ℝ) (s : α → ℝ)
    (remaining : (k : ℕ) → (Finset.Iic k → JumpState α β) → ℝ)
    (hremaining : ∀ k,Measurable (remaining k))
    (stop : (k : ℕ) → (Finset.Iic k → JumpState α β) → Prop)
    (hstop : ∀ k,MeasurableSet {h | stop k h}) (k : ℕ) :
    Measurable (fun p : (Finset.Iic k → JumpState α β) × JumpState α β =>
      censoredStoppedMultiplier w s remaining stop k p.1 p.2) := by
  have hx : Measurable (fun h : Finset.Iic k → JumpState α β =>
      (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1) := (measurable_pi_apply _).fst
  exact Measurable.ite ((hstop k).preimage measurable_fst) measurable_const
    ((censoredStateMultiplier_measurable w s).comp ((hx.comp measurable_fst).prodMk
      (((hremaining k).comp measurable_fst).prodMk measurable_snd)))

def prefixElapsed (k : ℕ) (h : Finset.Iic k → JumpState α β) : ℝ :=
  ∑ i : Fin k,(h ⟨(i : ℕ)+1,Finset.mem_Iic.mpr i.isLt⟩).2.2

omit [Countable α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β] in
theorem prefixElapsed_measurable (k : ℕ) : Measurable (@prefixElapsed α β k) := by
  unfold prefixElapsed
  apply Finset.measurable_sum
  intro i _
  exact (measurable_pi_apply (⟨(i : ℕ)+1,Finset.mem_Iic.mpr i.isLt⟩ : Finset.Iic k)).snd.snd

end
end RandomViability

import proofs.StartupCount.PrefixDensity

namespace StartupCount
open Classical MeasureTheory ProbabilityTheory RandomViability Set
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 50000
variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

def windowPrefixWeight (guard : α → Prop) (a b : ℝ) (k : ℕ)
    (h : Finset.Iic k → JumpState α β) (t : ℝ) : ℝ≥0∞ :=
  if readyPrefix guard k h t ∧ a < t ∧ t ≤ b then 1 else 0

omit [Fintype β] [MeasurableSingletonClass β] in
theorem windowPrefixWeight_joint (guard : α → Prop) (a b : ℝ) (k : ℕ) :
    Measurable (fun p : (Finset.Iic k → JumpState α β) × ℝ =>
      windowPrefixWeight guard a b k p.1 p.2) := by
  exact Measurable.ite ((readyPrefix_measurableSet guard k).inter
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const))) measurable_const measurable_const

omit [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [MeasurableSpace β] [MeasurableSingletonClass β] in
theorem crossing_prefix_density_le (rate : α → β → ℝ) (w : α → β → ℝ)
    (guard : α → Prop) (count : α → ℕ) (l k : ℕ) (C a b t : ℝ)
    (hbound : ∀ x,guard x → (∑ j,rate x j*w x j) ≤ C*(if count x ≤ l then 1 else 0))
    (h : Finset.Iic k → JumpState α β) :
    windowPrefixWeight guard a b k h t *
        ENNReal.ofReal (∑ j,rate (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 j*
          w (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 j) ≤
      ENNReal.ofReal C * (if a < t ∧ t ≤ b then lowPrefixWeight guard count l k h t else 0) := by
  by_cases hp : readyPrefix guard k h t
  · have hb := hbound _ (readyPrefix_last guard k h t hp).1
    by_cases hw : a < t ∧ t ≤ b
    · simp only [windowPrefixWeight,hp,hw,true_and,if_true,one_mul,
        lowPrefixWeight]
      apply le_trans (ENNReal.ofReal_le_ofReal hb)
      by_cases hl : count (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 ≤ l
      · simp only [hl,if_true,mul_one,le_refl]
      · simp only [hl,if_false,mul_zero,ENNReal.ofReal_zero,le_refl]
    · simp only [windowPrefixWeight,hp,hw,true_and,if_false,zero_mul,mul_zero,le_refl]
  · simp only [windowPrefixWeight,hp,false_and,if_false,zero_mul,zero_le]

end
end StartupCount

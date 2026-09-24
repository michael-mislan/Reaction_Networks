import proofs.RandomViability.BasalEnvelope

namespace RandomViability
open Classical FiniteCopy RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF
noncomputable section
set_option maxHeartbeats 20000

theorem basal_factorial_product_distinct {n : ℕ} (N : Molecule n → ℕ)
    (u w : Molecule n) (huw : u ≠ w) :
    (∏ x, ((N x).descFactorial (singleCount u x+singleCount w x) : ℝ)) =
      (N u : ℝ)*N w := by
  calc
    _ = ∏ x, (N x : ℝ)^(singleCount u x+singleCount w x) := by
      apply Finset.prod_congr rfl
      intro x _
      by_cases hu : x=u
      · subst x
        simp [singleCount, huw]
      · by_cases hw : x=w
        · subst x
          simp [singleCount, Ne.symm huw]
        · simp [singleCount, hu, hw]
    _ = _ := by
      simp only [pow_add, Finset.prod_mul_distrib]
      simp [singleCount, apply_ite]

theorem bounded_basal_ligation_rate_distinct {n B : ℕ} (c : SourceMoleculeFibreConfig n)
    (V D : NNReal) (hV : 0 < (V : ℝ)) (basal : Reaction n → NNReal)
    (cat : Reaction n → Molecule n → NNReal) (N : BoundedCounts n B) (r : Reaction n)
    (hdistinct : reactionLeft r ≠ reactionRight r)
    (hl : 1 ≤ boundedCountsValue N (reactionLeft r))
    (hr : 1 ≤ boundedCountsValue N (reactionRight r)) :
    (boundedPhysicalCountModel c V D basal cat).rate N (.inr (.inl (r,true))) =
      (basal r : ℝ)*((boundedCountsValue N (reactionLeft r) : ℝ)*boundedCountsValue N (reactionRight r))/V := by
  have hen : ∀ x, physicalChannelInput (.inr (.inl (r,true))) x ≤ boundedCountsValue N x := by
    intro x
    by_cases hx : x=reactionLeft r
    · subst x
      simpa [physicalChannelInput, singleCount, hdistinct] using hl
    · by_cases hy : x=reactionRight r
      · subst x
        simpa [physicalChannelInput, singleCount, Ne.symm hdistinct] using hr
      · simp [physicalChannelInput, singleCount, hx, hy]
  change (if ∀ x, physicalChannelInput (.inr (.inl (r,true))) x ≤ boundedCountsValue N x then
    physicalChannelRate c V D basal cat (boundedCountsValue N) (.inr (.inl (r,true))) else 0) = _
  rw [if_pos hen]
  unfold physicalChannelRate
  have hi : (∑ x, physicalChannelInput (.inr (.inl (r,true))) x) = 2 := by
    simp [physicalChannelInput, singleCount, Finset.sum_add_distrib]
  rw [hi]
  simp only [physicalChannelCoefficient, physicalChannelInput, if_true]
  rw [basal_factorial_product_distinct _ _ _ hdistinct]
  field_simp

end
end RandomViability

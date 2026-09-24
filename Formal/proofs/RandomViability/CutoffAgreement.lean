import proofs.RandomViability.FoodInputPaths

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 30000

theorem physical_raw_mass_le_input {n : ℕ} (N : Molecule n → ℕ)
    (ch : PhysicalCountChannel n) (he : ∀ z, physicalChannelInput ch z ≤ N z) :
    countMass (applyCountChannel N (physicalChannelInput ch) (physicalChannelOutput ch)) ≤
      countMass N + foodInputMass ch := by
  rcases ch with (ch | ch)
  · rcases ch with (f | z)
    · change countMass (fun z => N z+singleCount f.val z) ≤ countMass N+molLength f.val
      rw [countMass_add, countMass_single]
    · change countMass (fun w => N w-singleCount z w+0) ≤ countMass N+0
      simp only [Nat.add_zero, countMass]
      exact Finset.sum_le_sum (fun w _ => Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  · have hb : countMass (physicalChannelInput (.inr ch)) = countMass (physicalChannelOutput (.inr ch)) := by
      rcases ch with (ch | ch)
      · exact physical_basal_channel_balanced ch.1 ch.2
      · exact physical_catalytic_channel_balanced ch.1 ch.2.1 ch.2.2
    rw [applyCountChannel_mass _ _ _ he hb]
    exact Nat.le_add_right _ _

theorem bounded_next_values_agree {n B C : ℕ}
    (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (X : BoundedCounts n B) (Y : BoundedCounts n C)
    (hxy : boundedCountsValue X = boundedCountsValue Y) (ch : PhysicalCountChannel n)
    (hx : boundedMass X+foodInputMass ch ≤ B)
    (hy : boundedMass X+foodInputMass ch ≤ C) :
    boundedCountsValue ((boundedPhysicalCountModel c V D basal cat).next X ch) =
      boundedCountsValue ((boundedPhysicalCountModel c V D basal cat).next Y ch) := by
  by_cases he : ∀ z, physicalChannelInput ch z ≤ boundedCountsValue X z
  · have heY : ∀ z, physicalChannelInput ch z ≤ boundedCountsValue Y z := by rw [← hxy]; exact he
    change boundedCountsValue (if _ then _ else X) = boundedCountsValue (if _ then _ else Y)
    rw [if_pos he, if_pos heY]
    rw [truncateCounts_preserves X _ ((physical_raw_mass_le_input _ ch he).trans hx)]
    rw [truncateCounts_preserves Y _ (by rw [← hxy]; exact (physical_raw_mass_le_input _ ch he).trans hy)]
    rw [hxy]
  · have heY : ¬ ∀ z, physicalChannelInput ch z ≤ boundedCountsValue Y z := by rw [← hxy]; exact he
    change boundedCountsValue (if _ then _ else X) = boundedCountsValue (if _ then _ else Y)
    rw [if_neg he, if_neg heY]
    exact hxy

theorem bounded_rates_agree {n B C : ℕ}
    (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (X : BoundedCounts n B) (Y : BoundedCounts n C)
    (hxy : boundedCountsValue X = boundedCountsValue Y) (ch : PhysicalCountChannel n) :
    (boundedPhysicalCountModel c V D basal cat).rate X ch =
      (boundedPhysicalCountModel c V D basal cat).rate Y ch := by
  change (if _ then physicalChannelRate _ _ _ _ _ (boundedCountsValue X) ch else 0) =
    (if _ then physicalChannelRate _ _ _ _ _ (boundedCountsValue Y) ch else 0)
  rw [hxy]

end
end RandomViability

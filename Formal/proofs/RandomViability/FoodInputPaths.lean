import proofs.RandomViability.BoundedMassDrift
import proofs.RandomViability.JumpRewardPaths

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section

def foodInputMass {n : ℕ} : PhysicalCountChannel n → ℕ
  | .inl (.inl f) => molLength f.val
  | _ => 0

theorem bounded_mass_next_le_food_input {n B : ℕ} (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (basal : Reaction n → NNReal) (catalytic : Reaction n → Molecule n → NNReal)
    (N : BoundedCounts n B) (ch : PhysicalCountChannel n) :
    boundedMass ((boundedPhysicalCountModel c V D basal catalytic).next N ch) ≤
      boundedMass N + foodInputMass ch := by
  rcases ch with (ch | ch)
  · rcases ch with (f | z)
    · exact bounded_food_mass_next_le c V D basal catalytic N f
    · change boundedMass ((boundedPhysicalCountModel c V D basal catalytic).next N (.inl (.inr z))) ≤ boundedMass N + 0
      by_cases hz : 1 ≤ boundedCountsValue N z
      · have hh := bounded_outflow_mass_drop c V D basal catalytic N z hz
        omega
      · have he : ¬ ∀ w, singleCount z w ≤ boundedCountsValue N w :=
          fun hw => hz ((singleCount_enabled_iff _ z).mp hw)
        change boundedMass (if ∀ w, singleCount z w ≤ boundedCountsValue N w then _ else N) ≤ _
        rw [if_neg he]
        omega
  · have hb : countMass (physicalChannelInput (.inr ch)) = countMass (physicalChannelOutput (.inr ch)) := by
      rcases ch with (ch | ch)
      · exact physical_basal_channel_balanced ch.1 ch.2
      · exact physical_catalytic_channel_balanced ch.1 ch.2.1 ch.2.2
    rw [boundedPhysical_mass_next_of_balance c V D basal catalytic N _ hb]
    exact Nat.le_add_right _ _

namespace FiniteLabeledKernel
variable {α β : Type*} [Fintype β]

/-- A proposed step would cross the mass cap before its truncation. -/
def pathOverflow (K : FiniteLabeledKernel α β) (mass : α → ℝ) (input : α → β → ℝ) (B : ℝ) :
    (n : ℕ) → α → RewardPath β n → Prop
  | 0, _, _ => False
  | n+1, x, p => B < mass x + input x p.1 ∨ pathOverflow K mass input B n (K.next x p.1) p.2

theorem pathOverflow_requires_input (K : FiniteLabeledKernel α β)
    (mass : α → ℝ) (input : α → β → ℝ) (hinput : ∀ x b, 0 ≤ input x b)
    (hstep : ∀ x b, mass (K.next x b) ≤ mass x + input x b)
    (B : ℝ) (n : ℕ) (x : α) (p : RewardPath β n)
    (hover : K.pathOverflow mass input B n x p) :
    B < mass x + K.pathReward input n x p := by
  induction n generalizing x with
  | zero => exact False.elim hover
  | succ n ih =>
    change B < mass x + (input x p.1 + K.pathReward input n (K.next x p.1) p.2)
    rcases hover with (hfirst | hlater)
    · have ht := K.pathReward_nonneg input hinput n (K.next x p.1) p.2
      linarith
    · have ht := ih _ p.2 hlater
      have hs := hstep x p.1
      linarith

end FiniteLabeledKernel
end
end RandomViability

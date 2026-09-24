import proofs.RandomViability.BoundedCountModel
import proofs.RandomViability.LiteralUptake

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section

def weightedCountMass {n : ℕ} (w : Molecule n → ℝ) (N : Molecule n → ℕ) : ℝ :=
  ∑ x, w x * (N x : ℝ)

theorem weightedCountMass_change {n : ℕ} (w : Molecule n → ℝ)
    (N input output : Molecule n → ℕ) (he : ∀ x, input x ≤ N x) :
    weightedCountMass w (applyCountChannel N input output) - weightedCountMass w N =
      weightedCountMass w output - weightedCountMass w input := by
  unfold weightedCountMass
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  simp only [applyCountChannel, Nat.cast_add, Nat.cast_sub (he x)]
  ring

def countNonfoodMass {n : ℕ} (N : Molecule n → ℕ) : ℝ :=
  weightedCountMass (fun x => (molLength x : ℝ)-foodMassWeight x) N

theorem catalytic_nonfood_raw_change {n : ℕ} (N : Molecule n → ℕ)
    (r : Reaction n) (z : Molecule n) (d : Bool)
    (he : ∀ x, physicalChannelInput (.inr (.inr (r,z,d))) x ≤ N x) :
    countNonfoodMass (applyCountChannel N (physicalChannelInput (.inr (.inr (r,z,d))))
      (physicalChannelOutput (.inr (.inr (r,z,d))))) - countNonfoodMass N =
      if d then ligationNonfoodMassGain r else -ligationNonfoodMassGain r := by
  unfold countNonfoodMass
  rw [weightedCountMass_change _ _ _ _ he]
  rw [ligationNonfoodMassGain_eq_mass_difference]
  cases d <;>
    simp [weightedCountMass, physicalChannelInput, physicalChannelOutput,
      singleCount, Nat.cast_add, mul_add, Finset.sum_add_distrib, mul_ite] <;> ring

theorem bounded_catalytic_positive_reward {n B : ℕ}
    (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (basal : Reaction n → NNReal) (catalytic : Reaction n → Molecule n → NNReal)
    (N : BoundedCounts n B) (r : Reaction n) (z : Molecule n) (d : Bool) :
    (boundedPhysicalCountModel c V D basal catalytic).rate N (.inr (.inr (r,z,d))) *
      max 0 (countNonfoodMass (boundedCountsValue
        ((boundedPhysicalCountModel c V D basal catalytic).next N (.inr (.inr (r,z,d))))) -
          countNonfoodMass (boundedCountsValue N)) =
      if d then ligationNonfoodMassGain r *
        (boundedPhysicalCountModel c V D basal catalytic).rate N (.inr (.inr (r,z,d))) else 0 := by
  by_cases he : ∀ x, physicalChannelInput (.inr (.inr (r,z,d))) x ≤ boundedCountsValue N x
  · have hn : boundedCountsValue ((boundedPhysicalCountModel c V D basal catalytic).next N (.inr (.inr (r,z,d)))) =
        applyCountChannel (boundedCountsValue N) (physicalChannelInput (.inr (.inr (r,z,d))))
          (physicalChannelOutput (.inr (.inr (r,z,d)))) := by
      change boundedCountsValue (if ∀ x, physicalChannelInput (.inr (.inr (r,z,d))) x ≤ boundedCountsValue N x then
        truncateCounts N _ else N) = _
      rw [if_pos he]
      exact truncateCounts_internal_unchanged N _ _ he (physical_catalytic_channel_balanced r z d)
    rw [hn, catalytic_nonfood_raw_change _ r z d he]
    have hg := (ligationNonfoodMassGain_bounds r).1
    cases d
    · simp only [Bool.false_eq_true, ↓reduceIte, max_eq_left (neg_nonpos.mpr hg), mul_zero]
    · simp only [↓reduceIte, max_eq_right hg, mul_comm]
  · have hr : (boundedPhysicalCountModel c V D basal catalytic).rate N (.inr (.inr (r,z,d))) = 0 := by
      exact if_neg he
    rw [hr]
    simp

end
end RandomViability

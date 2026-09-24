import proofs.RAF.Concrete.PolymerCRS
import Mathlib.Tactic

namespace RandomViability
open Classical RAF.Polymer RAF.Concrete
noncomputable section

def countMass {n : ℕ} (N : Molecule n → ℕ) : ℕ := ∑ z, molLength z * N z

theorem count_le_countMass {n : ℕ} (N : Molecule n → ℕ) (z : Molecule n) :
    N z ≤ countMass N := by
  have hl : 1 ≤ molLength z := by simp [molLength]
  calc
    N z ≤ molLength z * N z := by nlinarith
    _ ≤ _ := Finset.single_le_sum (f := fun w => molLength w * N w)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ z)

def BoundedCounts (n B : ℕ) :=
  {N : Molecule n → Fin (B+1) // countMass (fun z => (N z).val) ≤ B}

instance (n B : ℕ) : Fintype (BoundedCounts n B) := inferInstanceAs
  (Fintype {N : Molecule n → Fin (B+1) // countMass (fun z => (N z).val) ≤ B})

def boundedCountsValue {n B : ℕ} (N : BoundedCounts n B) : Molecule n → ℕ :=
  fun z => (N.val z).val

def truncateCounts {n B : ℕ} (N : BoundedCounts n B) (raw : Molecule n → ℕ) :
    BoundedCounts n B :=
  if h : countMass raw ≤ B then
    ⟨fun z => ⟨raw z, by have hh := (count_le_countMass raw z).trans h; omega⟩, h⟩
  else N

theorem truncateCounts_preserves {n B : ℕ} (N : BoundedCounts n B)
    (raw : Molecule n → ℕ) (h : countMass raw ≤ B) :
    boundedCountsValue (truncateCounts N raw) = raw := by
  simp only [truncateCounts, dif_pos h]
  rfl

theorem truncateCounts_blocks {n B : ℕ} (N : BoundedCounts n B)
    (raw : Molecule n → ℕ) (h : B < countMass raw) : truncateCounts N raw = N := by
  simp only [truncateCounts, dif_neg (Nat.not_le.mpr h)]

def applyCountChannel {n : ℕ} (N input output : Molecule n → ℕ) : Molecule n → ℕ :=
  fun z => N z - input z + output z

theorem applyCountChannel_mass {n : ℕ} (N input output : Molecule n → ℕ)
    (henabled : ∀ z, input z ≤ N z) (hbalance : countMass input = countMass output) :
    countMass (applyCountChannel N input output) = countMass N := by
  have hsum : countMass (applyCountChannel N input output) + countMass input =
      countMass N + countMass output := by
    unfold countMass applyCountChannel
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z _
    have hh := congrArg (fun t => molLength z * t) (Nat.sub_add_cancel (henabled z))
    nlinarith
  omega

theorem truncateCounts_internal_unchanged {n B : ℕ} (N : BoundedCounts n B)
    (input output : Molecule n → ℕ)
    (henabled : ∀ z, input z ≤ boundedCountsValue N z)
    (hbalance : countMass input = countMass output) :
    boundedCountsValue (truncateCounts N (applyCountChannel (boundedCountsValue N) input output)) =
      applyCountChannel (boundedCountsValue N) input output := by
  apply truncateCounts_preserves
  rw [applyCountChannel_mass _ _ _ henabled hbalance]
  exact N.property

def singleCount {n : ℕ} (z : Molecule n) : Molecule n → ℕ := fun w => if w=z then 1 else 0

theorem countMass_single {n : ℕ} (z : Molecule n) : countMass (singleCount z) = molLength z := by
  simp [countMass, singleCount]

theorem countMass_add {n : ℕ} (N M : Molecule n → ℕ) :
    countMass (fun z => N z + M z) = countMass N + countMass M := by
  simp only [countMass, Nat.mul_add, Finset.sum_add_distrib]

/-- Exact weighted balance includes the catalyst on both sides, even when
it coincides with a substrate or product. -/
theorem catalytic_count_channel_balance {n : ℕ} (r : Reaction n) (c : Molecule n) :
    countMass (fun z => singleCount (reactionLeft r) z + singleCount (reactionRight r) z + singleCount c z) =
    countMass (fun z => singleCount (reactionProduct r) z + singleCount c z) := by
  rw [countMass_add, countMass_add, countMass_add]
  simp only [countMass_single, molLength_reactionLeft, molLength_reactionRight, molLength_reactionProduct]
  rw [reaction_length_add]

theorem basal_count_channel_balance {n : ℕ} (r : Reaction n) :
    countMass (fun z => singleCount (reactionLeft r) z + singleCount (reactionRight r) z) =
      countMass (singleCount (reactionProduct r)) := by
  rw [countMass_add]
  simp only [countMass_single, molLength_reactionLeft, molLength_reactionRight, molLength_reactionProduct]
  exact reaction_length_add r

end
end RandomViability

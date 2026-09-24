import proofs.RandomViability.ProductiveClockBounds
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace RandomViability
open Classical
noncomputable section
set_option maxHeartbeats 30000

theorem productive_firing_window_iff (m : ℕ) (hm : 0 < m) (τ : ℕ → ℝ)
    (hτ : ∀ i < 3*m+1, productiveWaitLower m i < τ i ∧
      τ i ≤ productiveWaitLower m i+productiveWaitWidth m)
    (hnon : ∀ i, 0 ≤ τ i) (i : ℕ) :
    (1 < productiveClock τ (i+1) ∧ productiveClock τ (i+1) ≤ 100) ↔ m ≤ i ∧ i < 3*m := by
  have hb := productive_clock_margins m hm τ hτ
  have hmono := productive_clock_monotone τ hnon
  constructor
  · intro hi
    constructor
    · by_contra h
      have hh := hmono (show i+1 ≤ m by omega)
      linarith [hb.1,hi.1]
    · by_contra h
      have hh := hmono (show 3*m+1 ≤ i+1 by omega)
      linarith [hb.2.2.2,hi.2]
  · rintro ⟨hl,hu⟩
    constructor
    · exact hb.2.1.trans_le (hmono (by omega))
    · exact ((hmono (show i+1 ≤ 3*m by omega)).trans hb.2.2.1).trans (by norm_num)

theorem productive_parity_count (m p : ℕ) (hp : p < 2) :
    (∑ j ∈ Finset.range (2*m), (if j%2=p then (1 : ℝ) else 0)) = m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    have hp' : p=0 ∨ p=1 := by omega
    rcases hp' with rfl | rfl <;>
      simp [Nat.add_mod, Nat.cast_add, Nat.cast_one] <;> decide

theorem productive_operating_parity_count (m p : ℕ) (hp : p < 2) :
    (∑' i : ℕ, if m ≤ i ∧ i < 3*m then
      (if (i-m)%2=p then (1 : ℝ) else 0) else 0) = m := by
  rw [tsum_eq_sum (s := Finset.range (3*m)) (fun i hi =>
    if_neg (by have hh : ¬ i < 3*m := fun h => hi (Finset.mem_range.mpr h); tauto))]
  rw [show 3*m=m+2*m by omega, Finset.sum_range_add]
  have hz : (∑ i ∈ Finset.range m, if m ≤ i ∧ i < m+2*m then
      (if (i-m)%2=p then (1 : ℝ) else 0) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply if_neg
    have hh := Finset.mem_range.mp hi
    omega
  rw [hz,zero_add]
  calc
    _ = ∑ j ∈ Finset.range (2*m), (if j%2=p then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hh := Finset.mem_range.mp hj
      simp [show m ≤ m+j ∧ m+j < m+2*m by omega]
    _ = _ := productive_parity_count m p hp

end
end RandomViability

import proofs.RandomViability.ProductiveWindows

namespace RandomViability
open Classical
noncomputable section
set_option maxHeartbeats 30000

def productiveClock (τ : ℕ → ℝ) (k : ℕ) : ℝ := ∑ i ∈ Finset.range k, τ i

theorem productive_clock_margins (m : ℕ) (hm : 0 < m) (τ : ℕ → ℝ)
    (hτ : ∀ i < 3*m+1, productiveWaitLower m i < τ i ∧
      τ i ≤ productiveWaitLower m i+productiveWaitWidth m) :
    productiveClock τ m ≤ 1/2 ∧ 1 < productiveClock τ (m+1) ∧
    productiveClock τ (3*m) ≤ 185/2 ∧ 100 < productiveClock τ (3*m+1) := by
  have hnon : ∀ k ≤ 3*m+1, 0 ≤ productiveClock τ k := by
    intro k hk
    apply Finset.sum_nonneg
    intro i hi
    exact (productive_wait_lower_nonneg m i).trans (hτ i (by have := Finset.mem_range.mp hi; omega)).1.le
  have hupper : ∀ k ≤ 3*m+1, productiveClock τ k ≤
      ∑ i ∈ Finset.range k, (productiveWaitLower m i+productiveWaitWidth m) := by
    intro k hk
    apply Finset.sum_le_sum
    intro i hi
    exact (hτ i (by have := Finset.mem_range.mp hi; omega)).2
  have hstart := hupper m (by omega)
  rw [productive_wait_startup_upper m hm] at hstart
  have hend := hupper (3*m) (by omega)
  rw [productive_wait_operating_upper m hm] at hend
  have hfirst : 1 < productiveClock τ (m+1) := by
    have hh := (hτ m (by omega)).1
    have he : productiveWaitLower m m = 45/(m : ℝ)+1 := by
      simp [productiveWaitLower, show m<3*m by omega]
    rw [he] at hh
    have hp : 0 ≤ 45/(m : ℝ) := by positivity
    have hs := hnon m (by omega)
    unfold productiveClock
    rw [Finset.sum_range_succ]
    change 1 < productiveClock τ m+τ m
    linarith
  have hfinal : 100 < productiveClock τ (3*m+1) := by
    have hh := (hτ (3*m) (by omega)).1
    have he : productiveWaitLower m (3*m)=100 := by simp [productiveWaitLower]; omega
    rw [he] at hh
    have hs := hnon (3*m) (by omega)
    unfold productiveClock
    rw [Finset.sum_range_succ]
    change 100 < productiveClock τ (3*m)+τ (3*m)
    linarith
  exact ⟨hstart,hfirst,hend,hfinal⟩

theorem productive_clock_monotone (τ : ℕ → ℝ) (hτ : ∀ i, 0 ≤ τ i) :
    Monotone (productiveClock τ) := by
  apply monotone_nat_of_le_succ
  intro i
  unfold productiveClock
  rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right (hτ i)

/-- Every chronological population interval meeting [1,100] is an operating
index of the prescribed path. This also excludes all later jump indices. -/
theorem productive_clock_operating_index (m : ℕ) (hm : 0 < m) (τ : ℕ → ℝ)
    (hτ : ∀ i < 3*m+1, productiveWaitLower m i < τ i ∧
      τ i ≤ productiveWaitLower m i+productiveWaitWidth m)
    (hnon : ∀ i, 0 ≤ τ i) (t : ℝ) (ht : 1 ≤ t ∧ t ≤ 100)
    (i : ℕ) (hi : productiveClock τ i ≤ t ∧ t < productiveClock τ (i+1)) :
    m ≤ i ∧ i ≤ 3*m := by
  have hb := productive_clock_margins m hm τ hτ
  have hmono := productive_clock_monotone τ hnon
  constructor
  · by_contra h
    have hh := hmono (show i+1 ≤ m by omega)
    linarith [hb.1,hi.2,ht.1]
  · by_contra h
    have hh := hmono (show 3*m+1 ≤ i by omega)
    linarith [hb.2.2.2,hi.1,ht.2]

end
end RandomViability

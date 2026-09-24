import proofs.RAF1519.Refinement.HoldingClock

namespace RAF1519.Refinement
noncomputable section
open scoped BigOperators

def holdingPrimitive (h v : ℕ → ℝ) (K : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range K, v i*holdingRamp (holdingClock h i) (h i) t

theorem holdingPrimitive_continuous (h v : ℕ → ℝ) (K : ℕ) :
    Continuous (holdingPrimitive h v K) := by
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul (holdingRamp_continuous _ _)

theorem holding_active_iff (h : ℕ → ℝ) (hh : ∀ i, 0 ≤ h i)
    (j : ℕ) (t : ℝ) (ha : holdingClock h j ≤ t) (hb : t < holdingClock h j+h j) (i : ℕ) :
    (holdingClock h i ≤ t ∧ t < holdingClock h i+h i) ↔ i=j := by
  constructor
  · intro hi
    rcases lt_trichotomy i j with hij|hij|hij
    · have hc := holdingClock_monotone h hh (Nat.succ_le_of_lt hij)
      rw [holdingClock_succ] at hc
      linarith [hi.2]
    · exact hij
    · have hc := holdingClock_monotone h hh (Nat.succ_le_of_lt hij)
      rw [holdingClock_succ] at hc
      linarith [hi.1]
  · rintro rfl
    exact ⟨ha,hb⟩

theorem holdingPrimitive_right_derivative (h v : ℕ → ℝ) (hh : ∀ i, 0 ≤ h i)
    (K j : ℕ) (hj : j < K) (t : ℝ)
    (ha : holdingClock h j ≤ t) (hb : t < holdingClock h j+h j) :
    HasDerivWithinAt (holdingPrimitive h v K) (v j) (Set.Ici t) t := by
  have hd := HasDerivWithinAt.fun_sum (u := Finset.range K) (fun i _ =>
    (holdingRamp_right_derivative (holdingClock h i) (h i) t (hh i)).const_mul (v i))
  simp_rw [holding_active_iff h hh j t ha hb] at hd
  simpa only [holdingPrimitive,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',
    Finset.mem_range,if_pos hj] using hd

theorem holdingPrimitive_completed (h v : ℕ → ℝ) (hh : ∀ i, 0 ≤ h i)
    (K : ℕ) (t : ℝ) (ht : holdingClock h K ≤ t) :
    holdingPrimitive h v K t = ∑ i ∈ Finset.range K, v i*h i := by
  apply Finset.sum_congr rfl
  intro i hi
  have hc := holdingClock_monotone h hh (Nat.succ_le_of_lt (Finset.mem_range.mp hi))
  rw [holdingClock_succ] at hc
  rw [holdingRamp_completed _ _ _ (hh i) (hc.trans ht)]

theorem holdingPrimitive_on_interval (h v : ℕ → ℝ) (hh : ∀ i, 0 ≤ h i)
    (K j : ℕ) (hj : j < K) (t : ℝ)
    (ha : holdingClock h j ≤ t) (hb : t < holdingClock h j+h j) :
    holdingPrimitive h v K t =
      (∑ i ∈ Finset.range j, v i*h i)+v j*(t-holdingClock h j) := by
  induction K with
  | zero => omega
  | succ K ih =>
    have he : holdingPrimitive h v (K+1) t = holdingPrimitive h v K t+
        v K*holdingRamp (holdingClock h K) (h K) t := by
      unfold holdingPrimitive
      rw [Finset.sum_range_succ]
    rw [he]
    by_cases hjK : j=K
    · subst j
      rw [holdingPrimitive_completed h v hh K t ha,holdingRamp_current _ _ _ ha hb.le]
    · have hj' : j < K := by omega
      rw [ih hj']
      have hc := holdingClock_monotone h hh (Nat.succ_le_of_lt hj')
      rw [holdingClock_succ] at hc
      rw [holdingRamp_not_started _ _ _ (hb.le.trans hc)]
      simp

end
end RAF1519.Refinement

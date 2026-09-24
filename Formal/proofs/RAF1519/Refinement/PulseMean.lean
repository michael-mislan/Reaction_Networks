import proofs.RAF1519.Refinement.PulseWeights

namespace RAF1519.Refinement
noncomputable section
open Classical
open scoped BigOperators

theorem pulse_retention_bounds (p : Intervention) (s : Fin 7) :
    (49/50)*p.q ≤ pulseCategory p s 0 ∧ pulseCategory p s 0 ≤ p.q := by
  have hq : 0 ≤ p.q := le_trans (by norm_num) p.q_lower
  constructor
  · have h := mul_le_mul_of_nonneg_left (speciesRetention_bounds p s).1 hq
    change (49/50)*p.q ≤ p.q*speciesRetention p s
    linarith
  · change p.q*speciesRetention p s ≤ p.q
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (speciesRetention_bounds p s).2 hq

theorem pulseNodeWeight_mean_bounds {n : ℕ} (N : MolecularState n) (p : Fin n → Intervention)
    (i : Fin n) (w : Fin 7 → ℝ) (hw : ∀ s, 0 ≤ w s) :
    (49/50)*(p i).q*(∑ s, w s*(N (i,s):ℝ)) ≤
      categoricalMean (graphPulseCategory N p) (pulseNodeWeight i w) ∧
    categoricalMean (graphPulseCategory N p) (pulseNodeWeight i w) ≤
      (p i).q*(∑ s, w s*(N (i,s):ℝ)) := by
  rw [← pulseNodeWeight_total N i w]
  unfold categoricalMean
  constructor
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m _
    by_cases hi : m.1.1=i
    · simp only [pulseNodeWeight,graphPulseCategory,hi]
      exact mul_le_mul_of_nonneg_right (pulse_retention_bounds (p i) m.1.2).1 (hw m.1.2)
    · simp only [pulseNodeWeight,if_neg hi,mul_zero,le_refl]
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m _
    by_cases hi : m.1.1=i
    · simp only [pulseNodeWeight,graphPulseCategory,hi]
      exact mul_le_mul_of_nonneg_right (pulse_retention_bounds (p i) m.1.2).2 (hw m.1.2)
    · simp only [pulseNodeWeight,if_neg hi,mul_zero,le_refl]

end
end RAF1519.Refinement

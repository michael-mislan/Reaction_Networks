import proofs.RandomViability.BindingCountDrift
import proofs.RandomViability.BindingResourceFoster

namespace RandomViability.Binding
noncomputable section
open scoped BigOperators

theorem weightedCount_nonneg (N : Counts) : 0 ≤ weightedCount N := by
  unfold weightedCount weighted
  positivity

theorem freeCount_le_weighted (N : Counts) : (N 2:ℝ) ≤ weightedCount N := by
  unfold weightedCount weighted
  linarith [Nat.cast_nonneg (α := ℝ) (N 3),Nat.cast_nonneg (α := ℝ) (N 4),
    Nat.cast_nonneg (α := ℝ) (N 5)]

theorem count_exponential_generator (N : Counts) (V eps k r s : ℝ) :
    literalGenerator N V eps k r (fun X => Real.exp (-s*weightedCount X)) =
      Real.exp (-s*weightedCount N) *
      (∑ j,countRate N V eps k r j*(Real.exp (-s*weightedJump j)-1)) := by
  rw [literalGenerator,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hz : countRate N V eps k r j = 0
  · simp [hz]
  · have hj := weighted_actual_jump N j (rate_support N V eps k r j hz)
    have he : weightedCount (countNext N j) = weightedCount N+weightedJump j := by linarith
    rw [he,show -s*(weightedCount N+weightedJump j) =
      -s*weightedCount N+(-s*weightedJump j) by ring,Real.exp_add]
    ring

theorem corridor_count_variance (N : Counts) (V : ℕ) (eps k r : ℝ)
    (hV : 0 < (V:ℝ)) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hk : 0 ≤ k) (hk1 : k ≤ 1/8) (hr : 0 ≤ r) (hr1 : r ≤ 22)
    (h : resourceGood N V) :
    countVariance N V eps k r ≤ 5*weightedCount N+(25/16)*eps*V := by
  have hc (i : Fin 6) : (N i:ℝ)/(V:ℝ) ≤ 11/10 :=
    (div_le_iff₀ hV).mpr (resource_count_cap N V h i)
  apply actual_count_variance_bound N V eps k r hV heps heps1 hk hk1 hr hr1
  · linarith [hc 0]
  · linarith [hc 1]
  · have hp := mul_le_mul (hc 0) (hc 1) (by positivity : 0 ≤ (N 1:ℝ)/(V:ℝ))
      (by norm_num : (0:ℝ) ≤ 11/10)
    linarith
  · linarith [hc 2]

theorem corridor_count_growth (N : Counts) (V : ℕ) (eps k r : ℝ)
    (hV : 0 < (V:ℝ)) (heps : 0 ≤ eps) (heps1 : eps ≤ 1/1000000)
    (hk : 0 ≤ k) (hk1 : k ≤ 1/8) (hr : 18 ≤ r) (hr1 : r ≤ 22)
    (h : resourceGood N V) (hY : weightedCount N ≤ (V:ℝ)/1000) :
    (39/100)*weightedCount N+(16/25)*eps*V ≤ countGrowth N V eps k r := by
  have hf := low_count_food_corridor N V hV h.1 h.2.2.1 hY
  apply actual_count_corridor_growth N V eps k r hV heps heps1 hk hk1 hr hr1
  · exact (le_div_iff₀ hV).mpr hf.1
  · exact (le_div_iff₀ hV).mpr hf.2
  · apply (div_le_iff₀ hV).mpr
    have hx := (freeCount_le_weighted N).trans hY
    linarith

theorem actual_entry_exponential (N : Counts) (V : ℕ) (eps k r s : ℝ)
    (hV : 0 < (V:ℝ)) (heps : 0 ≤ eps) (heps1 : eps ≤ 1/1000000)
    (hk : 0 ≤ k) (hk1 : k ≤ 1/8) (hr : 18 ≤ r) (hr1 : r ≤ 22)
    (h : resourceGood N V) (hY : weightedCount N ≤ (V:ℝ)/1000)
    (hs : 0 ≤ s) (hs1 : s ≤ 2/25) :
    literalGenerator N V eps k r (fun X => Real.exp (-s*weightedCount X)) ≤
      Real.exp (-s*weightedCount N)*
        (-(3/10*s-3*s^2)*weightedCount N-(14/25)*eps*V*s) := by
  rw [count_exponential_generator]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have hg := corridor_count_growth N V eps k r hV heps heps1 hk hk1 hr hr1 h hY
  have hq := corridor_count_variance N V eps k r hV heps (by linarith) hk hk1
    (by linarith) hr1 h
  simp only [countGrowth,rated_weighted_jump] at hg
  simpa only [mul_assoc] using entry_exponential_strong (countRate N V eps k r) weightedJump (weightedCount N)
    (eps*V) s (countRate_nonneg N V eps k r hV heps hk (by linarith))
    weightedJump_bound (weightedCount_nonneg N) (by positivity) hs hs1
    (by simpa only [mul_assoc] using hg)
    (by simpa only [mul_assoc] using hq)

end
end RandomViability.Binding

import proofs.RandomViability.BindingEntrySchedule
import proofs.RandomViability.BindingPoissonDeadline

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped NNReal

theorem entryTest_le_one (V : ℕ) (H s : ℝ) (hs : 0 ≤ s) (N : BoxCounts V) :
    entryTest V H s N ≤ 1 := by
  unfold entryTest
  split_ifs
  · apply Real.exp_le_one_iff.mpr
    have h := mul_nonneg hs (weightedCount_nonneg (boxCounts N))
    linarith
  · norm_num

theorem entry_indicator_bound (V : ℕ) (H s : ℝ) (hs : 0 ≤ s) (N : BoxCounts V) :
    FiniteKernel.eventIndicator {X | entryActive V H X} N ≤
      Real.exp (s*H)*entryTest V H s N := by
  by_cases h : entryActive V H N
  · simp only [FiniteKernel.eventIndicator,Set.mem_setOf_eq,if_pos h,entryTest]
    rw [← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    have hm := mul_le_mul_of_nonneg_left h.2.le hs
    linarith
  · simp [FiniteKernel.eventIndicator,entryTest,h]

theorem entry_discrete_after_startup (V q : ℕ) (H eps k r : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1/1000000) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 18 ≤ r) (hr1 : r ≤ 22) (hH : H ≤ (V:ℝ)/1000) (hq : 0 < q)
    (hbound : ∀ N, (entryModel V H eps k r hV heps hk (by linarith)).total N ≤ q)
    (m : ℕ) (N : BoxCounts V) :
    ((entryModel V H eps k r hV heps hk (by linarith)).uniformize q (by exact_mod_cast hq) hbound).steps
      (m+100*q) (FiniteKernel.eventIndicator {X | entryActive V H X}) N ≤
      Real.exp (H/40000-((14/25)*eps*V*(2/25)/(q:ℝ))*(m:ℝ)) := by
  let P := (entryModel V H eps k r hV heps hk (by linarith)).uniformize q (by exact_mod_cast hq) hbound
  have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
  have hi := P.steps_mono (entry_indicator_bound V H (1/40000) (by norm_num)) (m+100*q) N
  rw [P.steps_scale] at hi
  have ht := P.steps_mono (entry_hundred_clock_transfer V q H eps k r hV heps heps1 hk hk1 hr hr1 hH hq hbound) m N
  have hd (X : BoxCounts V) : P.step (entryTest V H (2/25)) X ≤
      Real.exp (-(14/25)*eps*V*(2/25)/(q:ℝ))*entryTest V H (2/25) X := by
    apply entry_step_transfer V H eps k r (2/25) (2/25) q hV heps heps1 hk hk1 hr hr1 hH
      (by norm_num) (by norm_num) _ hq' hbound X
    have hpos : 0 ≤ ((3/10:ℝ)*(2/25)-3*(2/25)^2)/(q:ℝ) := by positivity
    linarith
  have hd' := P.steps_decay_bound (entryTest V H (2/25))
    (Real.exp (-(14/25)*eps*V*(2/25)/(q:ℝ))) (Real.exp_pos _).le hd m N
  have hl := mul_le_mul_of_nonneg_left (entryTest_le_one V H (2/25) (by norm_num) N)
    (pow_nonneg (Real.exp_pos (-(14/25)*eps*V*(2/25)/(q:ℝ))).le m)
  have hb : P.steps m (P.steps (100*q) (entryTest V H (1/40000))) N ≤
      Real.exp (-(14/25)*eps*V*(2/25)/(q:ℝ))^m := by
    exact ht.trans (hd'.trans (by simpa only [mul_one] using hl))
  rw [← steps_comp] at hb
  have hh := mul_le_mul_of_nonneg_left hb (Real.exp_pos ((1/40000)*H)).le
  have result := hi.trans hh
  convert result using 1
  rw [← Real.exp_nat_mul,← Real.exp_add]
  congr 1
  ring

theorem entry_scalar_budget : Real.exp (-(8047:ℝ)/3125) < 1/12 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 8047/3125) 7
  norm_num [Finset.sum_range_succ] at h
  have he : Real.exp (-(8047:ℝ)/3125)*Real.exp ((8047:ℝ)/3125) = 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [Real.exp_pos (-(8047:ℝ)/3125)]

end
end RandomViability.Binding

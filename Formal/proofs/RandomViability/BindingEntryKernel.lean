import proofs.RandomViability.BindingCountExponential

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped BigOperators

def entryActive (V : ℕ) (H : ℝ) (N : BoxCounts V) : Prop :=
  resourceGood (boxCounts N) V ∧ weightedCount (boxCounts N) < H

/-- Auxiliary absorption for the no-entry event, not a reset of the reactor. -/
def entryModel (V : ℕ) (H eps k r : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r) :
    FiniteJumpModel (BoxCounts V) (Fin 18) where
  next := boxNext V
  rate N j := if entryActive V H N then countRate (boxCounts N) V eps k r j else 0
  nonneg N j := by
    split_ifs
    · exact countRate_nonneg (boxCounts N) V eps k r hV heps hk hr j
    · rfl

def entryTest (V : ℕ) (H s : ℝ) (N : BoxCounts V) : ℝ :=
  if entryActive V H N then Real.exp (-s*weightedCount (boxCounts N)) else 0

theorem entryTest_nonneg (V : ℕ) (H s : ℝ) (N : BoxCounts V) :
    0 ≤ entryTest V H s N := by
  unfold entryTest
  split_ifs
  · positivity
  · rfl

theorem entryTest_antitone (V : ℕ) (H s t : ℝ) (hst : s ≤ t) (N : BoxCounts V) :
    entryTest V H t N ≤ entryTest V H s N := by
  unfold entryTest
  split_ifs
  · apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hst (weightedCount_nonneg (boxCounts N))
    linarith
  · rfl

theorem entry_total_bound (V : ℕ) (H eps k r : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 0 ≤ r) (hr22 : r ≤ 22) (N : BoxCounts V) :
    (entryModel V H eps k r hV heps hk hr).total N ≤ 3000*(V:ℝ) := by
  by_cases h : entryActive V H N
  · simp only [FiniteJumpModel.total,entryModel,if_pos h]
    apply total_rate_bound (boxCounts N) V eps k r hV heps heps1 hk hk1 hr hr22
    intro i
    have hi := resource_count_cap (boxCounts N) V h.1 i
    linarith
  · simp only [FiniteJumpModel.total,entryModel,if_neg h,Finset.sum_const_zero]
    positivity

theorem entry_generator_inside (V : ℕ) (H eps k r s : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r) (N : BoxCounts V)
    (h : entryActive V H N) :
    (entryModel V H eps k r hV heps hk hr).generator (entryTest V H s) N ≤
      literalGenerator (boxCounts N) V eps k r (fun X => Real.exp (-s*weightedCount X)) := by
  simp only [FiniteJumpModel.generator,entryModel,if_pos h,literalGenerator]
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (countRate_nonneg (boxCounts N) V eps k r hV heps hk hr j)
  rw [show entryTest V H s N = Real.exp (-s*weightedCount (boxCounts N)) by simp [entryTest,h]]
  apply sub_le_sub_right
  unfold entryTest
  split_ifs
  · rw [boxNext_exact V N j h.1]
  · positivity

theorem entry_generator_outside (V : ℕ) (H eps k r s : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r) (N : BoxCounts V)
    (h : ¬entryActive V H N) :
    (entryModel V H eps k r hV heps hk hr).generator (entryTest V H s) N = 0 := by
  simp [FiniteJumpModel.generator,entryModel,h]

theorem entry_step_transfer (V : ℕ) (H eps k r s t q : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1/1000000) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 18 ≤ r) (hr1 : r ≤ 22) (hH : H ≤ (V:ℝ)/1000)
    (hs : 0 ≤ s) (hs1 : s ≤ 2/25) (ht : t ≤ s+(3/10*s-3*s^2)/q)
    (hq : 0 < q)
    (hbound : ∀ N, (entryModel V H eps k r hV heps hk (by linarith)).total N ≤ q)
    (N : BoxCounts V) :
    ((entryModel V H eps k r hV heps hk (by linarith)).uniformize q hq hbound).step
      (entryTest V H s) N ≤ Real.exp (-(14/25)*eps*V*s/q)*entryTest V H t N := by
  rw [FiniteJumpModel.uniformize_step]
  by_cases h : entryActive V H N
  · have hg := (entry_generator_inside V H eps k r s hV heps hk (by linarith) N h).trans
      (actual_entry_exponential (boxCounts N) V eps k r s hV heps heps1 hk hk1 hr hr1 h.1
        (h.2.le.trans hH) hs hs1)
    have hd := div_le_div_of_nonneg_right hg hq.le
    simp only [entryTest,if_pos h]
    calc
      _ ≤ Real.exp (-s*weightedCount (boxCounts N))*
          (1+(-(3/10*s-3*s^2)*weightedCount (boxCounts N)-(14/25)*eps*V*s)/q) := by
        calc
          _ ≤ Real.exp (-s*weightedCount (boxCounts N))+
              Real.exp (-s*weightedCount (boxCounts N))*
                (-(3/10*s-3*s^2)*weightedCount (boxCounts N)-(14/25)*eps*V*s)/q :=
            add_le_add le_rfl hd
          _ = _ := by ring
      _ ≤ Real.exp (-s*weightedCount (boxCounts N))*
          Real.exp ((-(3/10*s-3*s^2)*weightedCount (boxCounts N)-(14/25)*eps*V*s)/q) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        linarith [Real.add_one_le_exp ((-(3/10*s-3*s^2)*weightedCount (boxCounts N)-(14/25)*eps*V*s)/q)]
      _ = Real.exp (-(14/25)*eps*V*s/q)*
          Real.exp (-(s+(3/10*s-3*s^2)/q)*weightedCount (boxCounts N)) := by
        rw [← Real.exp_add,← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply Real.exp_le_exp.mpr
        have hm := mul_le_mul_of_nonneg_right ht (weightedCount_nonneg (boxCounts N))
        linarith
  · rw [entry_generator_outside V H eps k r s hV heps hk (by linarith) N h]
    simp [entryTest,h]

end
end RandomViability.Binding

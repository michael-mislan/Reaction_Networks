import proofs.RandomViability.BindingCompetitionResourceTails
import proofs.RandomViability.BindingEntryKernel

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped BigOperators

theorem competition_exponential_generator (N : Counts) (V eps k r delta s : ℝ) :
    competitionGenerator N V eps k r delta (fun X => Real.exp (-s*weightedCount X)) =
      Real.exp (-s*weightedCount N) *
      (∑ j,competitionRate N V eps k r delta j*(Real.exp (-s*weightedJump (competitionBase j))-1)) := by
  rw [competitionGenerator,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hz : competitionRate N V eps k r delta j = 0
  · simp [hz]
  · have hj := weighted_actual_jump N (competitionBase j)
      (competition_rate_support N V eps k r delta j hz)
    have he : weightedCount (competitionNext N j) = weightedCount N+weightedJump (competitionBase j) := by
      change weightedCount (countNext N (competitionBase j)) = _
      linarith
    rw [he,show -s*(weightedCount N+weightedJump (competitionBase j)) =
      -s*weightedCount N+(-s*weightedJump (competitionBase j)) by ring,Real.exp_add]
    ring

theorem competition_entry_exponential (N : Counts) (V : ℕ) (eps k r delta s : ℝ)
    (hV : 0 < (V:ℝ)) (heps : 0 ≤ eps) (heps1 : eps ≤ 1/1000000)
    (hk : 0 ≤ k) (hk1 : k ≤ 1/8) (hr : 18 ≤ r) (hr1 : r ≤ 22)
    (hd : 0 ≤ delta) (hd1 : delta ≤ 3/5)
    (h : resourceGood N V) (hY : weightedCount N ≤ (V:ℝ)/1000)
    (hs : 0 ≤ s) (hs1 : s ≤ 2/25) :
    competitionGenerator N V eps k r delta (fun X => Real.exp (-s*weightedCount X)) ≤
      Real.exp (-s*weightedCount N)*
        (-(3/10*s-3*s^2)*weightedCount N-(14/25)*eps*V*s) := by
  rw [competition_exponential_generator]
  exact mul_le_mul_of_nonneg_left
    (competition_corridor_exponential N V eps k r delta s hV heps heps1 hk hk1 hr hr1 hd hd1 h hY hs hs1)
    (Real.exp_pos _).le

/-- Auxiliary absorption for the no-entry event, not a reset of the reactor. -/
def competitionEntryModel (V : ℕ) (H eps k r delta : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r) (hd : 0 ≤ delta) :
    FiniteJumpModel (BoxCounts V) CompetitionChannel where
  next N j := boxNext V N (competitionBase j)
  rate N j := if entryActive V H N then competitionRate (boxCounts N) V eps k r delta j else 0
  nonneg N j := by
    split_ifs
    · exact competitionRate_nonneg (boxCounts N) V eps k r delta hV heps hk hr hd j
    · rfl

theorem competition_entry_total_bound (V : ℕ) (H eps k r delta : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 0 ≤ r) (hr22 : r ≤ 22) (hd : 0 ≤ delta) (hd1 : delta ≤ 3/5) (N : BoxCounts V) :
    (competitionEntryModel V H eps k r delta hV heps hk hr hd).total N ≤ 3000*(V:ℝ) := by
  by_cases h : entryActive V H N
  · simp only [FiniteJumpModel.total,competitionEntryModel,if_pos h]
    apply competition_total_rate_bound (boxCounts N) V eps k r delta hV heps heps1 hk hk1 hr hr22 hd hd1
    intro i
    have hi := resource_count_cap (boxCounts N) V h.1 i
    linarith
  · simp only [FiniteJumpModel.total,competitionEntryModel,if_neg h,Finset.sum_const_zero]
    positivity

theorem competition_entry_generator_inside (V : ℕ) (H eps k r delta s : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r) (hd : 0 ≤ delta) (N : BoxCounts V)
    (h : entryActive V H N) :
    (competitionEntryModel V H eps k r delta hV heps hk hr hd).generator (entryTest V H s) N ≤
      competitionGenerator (boxCounts N) V eps k r delta (fun X => Real.exp (-s*weightedCount X)) := by
  simp only [FiniteJumpModel.generator,competitionEntryModel,if_pos h,competitionGenerator]
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (competitionRate_nonneg (boxCounts N) V eps k r delta hV heps hk hr hd j)
  rw [show entryTest V H s N = Real.exp (-s*weightedCount (boxCounts N)) by simp [entryTest,h]]
  apply sub_le_sub_right
  unfold entryTest
  split_ifs
  · rw [boxNext_exact V N (competitionBase j) h.1]
    exact le_rfl
  · positivity

theorem competition_entry_generator_outside (V : ℕ) (H eps k r delta s : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r) (hd : 0 ≤ delta) (N : BoxCounts V)
    (h : ¬entryActive V H N) :
    (competitionEntryModel V H eps k r delta hV heps hk hr hd).generator (entryTest V H s) N = 0 := by
  simp [FiniteJumpModel.generator,competitionEntryModel,h]

theorem competition_entry_step_transfer (V : ℕ) (H eps k r delta s t q : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1/1000000) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 18 ≤ r) (hr1 : r ≤ 22) (hd : 0 ≤ delta) (hd1 : delta ≤ 3/5) (hH : H ≤ (V:ℝ)/1000)
    (hs : 0 ≤ s) (hs1 : s ≤ 2/25) (ht : t ≤ s+(3/10*s-3*s^2)/q)
    (hq : 0 < q)
    (hbound : ∀ N, (competitionEntryModel V H eps k r delta hV heps hk (by linarith) hd).total N ≤ q)
    (N : BoxCounts V) :
    ((competitionEntryModel V H eps k r delta hV heps hk (by linarith) hd).uniformize q hq hbound).step
      (entryTest V H s) N ≤ Real.exp (-(14/25)*eps*V*s/q)*entryTest V H t N := by
  rw [FiniteJumpModel.uniformize_step]
  by_cases h : entryActive V H N
  · have hg := (competition_entry_generator_inside V H eps k r delta s hV heps hk (by linarith) hd N h).trans
      (competition_entry_exponential (boxCounts N) V eps k r delta s hV heps heps1 hk hk1 hr hr1 hd hd1 h.1
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
  · rw [competition_entry_generator_outside V H eps k r delta s hV heps hk (by linarith) hd N h]
    simp [entryTest,h]

end
end RandomViability.Binding

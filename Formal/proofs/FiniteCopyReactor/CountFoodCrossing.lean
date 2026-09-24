import proofs.FiniteCopyReactor.CountFoodStopping

namespace FiniteCopyReactor
open Classical MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 30000

def foodCrossingBy (b : ℕ) (T : ℝ) (K : ℕ)
    (z : ℕ → JumpState Counts CompetitionChannel) : Prop :=
  ∃ j, j ≤ K ∧
    (∀ i < j, incomingSum (fun l => reactorTrajectoryFood (z (l+1)).2.1) i < b) ∧
    b ≤ incomingSum (fun l => reactorTrajectoryFood (z (l+1)).2.1) j ∧
    waitingSum (fun l => (z (l+1)).2.2) j ≤ T

def foodCrossingEvent (b : ℕ) (T : ℝ) :
    Set (ℕ → JumpState Counts CompetitionChannel) :=
  ⋃ K, {z | foodCrossingBy b T K z}

theorem food_crossing_weighted_probability (V r d : ℝ) (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (N : Counts) (b K : ℕ) (T : ℝ) :
    ENNReal.ofReal ((2 : ℝ)^b * Real.exp (-(2*V)*T)) *
      reactorTrajectory V r d hV hr hd N {z | foodCrossingBy b T K z} ≤ 1 := by
  let a := ENNReal.ofReal ((2 : ℝ)^b * Real.exp (-(2*V)*T))
  have ht := stopped_physical_product_tail V r d hV hr hd N
    (foodBudgetStop b) (foodHistorySum_stop_measurable b) K a
  have hsub : {z : ℕ → JumpState Counts CompetitionChannel | foodCrossingBy b T K z} ⊆
      {z | a ≤ trajectoryProduct (fun k h y => if foodBudgetStop b k h then 1 else
        jumpMultiplier (fun ch => (2 : ℝ)^reactorFood ch) (2*V) y) K z} := by
    intro z hz
    obtain ⟨j, hjK, hbefore, hcross, htime⟩ := hz
    change a ≤ _
    rw [physical_stopped_product_eq]
    exact food_crossing_multiplier_lower _ _ (2*V) T (by positivity) b j K hjK hbefore hcross htime
  exact (mul_le_mul_right (measure_mono hsub) a).trans ht

theorem food_crossing_probability (V r d : ℝ) (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (N : Counts) (b K : ℕ) (T : ℝ) :
    reactorTrajectory V r d hV hr hd N {z | foodCrossingBy b T K z} ≤
      ENNReal.ofReal (Real.exp ((2*V)*T)/(2 : ℝ)^b) := by
  let a := ENNReal.ofReal ((2 : ℝ)^b * Real.exp (-(2*V)*T))
  let B := ENNReal.ofReal (Real.exp ((2*V)*T)/(2 : ℝ)^b)
  have ha : B*a = 1 := by
    dsimp [B, a]
    rw [← ENNReal.ofReal_mul (by positivity)]
    have he : Real.exp ((2*V)*T)/(2 : ℝ)^b *
        ((2 : ℝ)^b * Real.exp (-(2*V)*T)) = 1 := by
      rw [neg_mul, Real.exp_neg]
      field_simp
    rw [he, ENNReal.ofReal_one]
  have ht := food_crossing_weighted_probability V r d hV hr hd N b K T
  calc
    _ = B*(a*reactorTrajectory V r d hV hr hd N {z | foodCrossingBy b T K z}) := by
      rw [← mul_assoc, ha, one_mul]
    _ ≤ B*1 := mul_le_mul_right ht B
    _ = B := mul_one _

theorem food_crossing_any_jump_probability (V r d : ℝ) (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (N : Counts) (b : ℕ) (T : ℝ) :
    reactorTrajectory V r d hV hr hd N (foodCrossingEvent b T) ≤
      ENNReal.ofReal (Real.exp ((2*V)*T)/(2 : ℝ)^b) := by
  have hm : Monotone (fun K => {z : ℕ → JumpState Counts CompetitionChannel | foodCrossingBy b T K z}) := by
    intro K L hKL z hz
    obtain ⟨j, hj, hp, hc, ht⟩ := hz
    exact ⟨j, hj.trans hKL, hp, hc, ht⟩
  rw [foodCrossingEvent, hm.measure_iUnion]
  exact iSup_le (fun K => food_crossing_probability V r d hV hr hd N b K T)

end
end FiniteCopyReactor

import proofs.RandomViability.PhysicalRewardRenewal

namespace StartupCount
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 40000
variable {α β : Type*}

/-- Terminal payoff when the deadline is reached in fewer than k jumps,
and every visited state remains inside the guard. -/
def killedTerminal (guard : α → Prop) (f : α → ℝ≥0∞) :
    ℕ → ℝ → (ℕ → JumpState α β) → ℝ≥0∞
  | 0, _, _ => 0
  | k+1, T, z => if guard (z 0).1 then
      if T < (z 1).2.2 then f (z 0).1
      else killedTerminal guard f k (T-(z 1).2.2) (restartJump z)
    else 0

theorem killedTerminal_mono (guard : α → Prop) (f : α → ℝ≥0∞)
    (k : ℕ) (T : ℝ) (z : ℕ → JumpState α β) :
    killedTerminal guard f k T z ≤ killedTerminal guard f (k+1) T z := by
  induction k generalizing T z with
  | zero => exact bot_le
  | succ k ih =>
    change (if guard (z 0).1 then if T < (z 1).2.2 then f (z 0).1 else
      killedTerminal guard f k (T-(z 1).2.2) (restartJump z) else 0) ≤
      (if guard (z 0).1 then if T < (z 1).2.2 then f (z 0).1 else
      killedTerminal guard f (k+1) (T-(z 1).2.2) (restartJump z) else 0)
    split_ifs <;> first | exact le_rfl | exact ih _ _

variable [MeasurableSpace α] [MeasurableSpace β]
  [Countable α] [MeasurableSingletonClass α]

theorem killedTerminal_measurable (guard : α → Prop) (f : α → ℝ≥0∞) (k : ℕ) :
    Measurable (fun p : ℝ × (ℕ → JumpState α β) => killedTerminal guard f k p.1 p.2) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    have hg : MeasurableSet {p : ℝ × (ℕ → JumpState α β) | guard (p.2 0).1} :=
      (Set.to_countable {x : α | guard x}).measurableSet.preimage
        (((measurable_pi_apply 0).comp measurable_snd).fst)
    have ht : MeasurableSet {p : ℝ × (ℕ → JumpState α β) | p.1 < (p.2 1).2.2} := by
      exact measurableSet_lt measurable_fst (((measurable_pi_apply 1).comp measurable_snd).snd.snd)
    exact Measurable.ite hg (Measurable.ite ht
      ((measurable_of_countable f).comp (((measurable_pi_apply 0).comp measurable_snd).fst))
      (ih.comp ((measurable_fst.sub (((measurable_pi_apply 1).comp measurable_snd).snd.snd)).prodMk
        (restartJump_measurable.comp measurable_snd)))) measurable_const

variable [Fintype β] [MeasurableSingletonClass β]

def killedTerminalMean (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (guard : α → Prop) (f : α → ℝ≥0∞) (k : ℕ) (T : ℝ) (x : α) : ℝ≥0∞ :=
  ∫⁻ z,killedTerminal guard f k T z ∂jumpTrajectoryLaw x next rate hr ht

/-- Renewal is derived from the actual infinite trajectory law, with killing
and the no-jump terminal payoff both explicit. -/
theorem killedTerminalMean_succ (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (guard : α → Prop) (f : α → ℝ≥0∞) (k : ℕ) (T : ℝ) (x : α) :
    killedTerminalMean next rate hr ht guard f (k+1) T x =
      ∫⁻ y,if guard x then if T < y.2 then f x else
        killedTerminalMean next rate hr ht guard f k (T-y.2) (next x y.1)
      else 0 ∂jumpClockMeasure (rate x) (hr x) (ht x) := by
  unfold killedTerminalMean
  have hm (j : ℕ) (t : ℝ) : Measurable (killedTerminal (β := β) guard f j t) :=
    (killedTerminal_measurable guard f j).comp (measurable_const.prodMk measurable_id)
  rw [jumpTrajectory_first_jump_lintegral x next rate hr ht _ (hm (k+1) T)]
  apply lintegral_congr
  intro y
  let h1 := firstMarkedPrefix x next y
  let ν := Kernel.traj (X := fun _ => JumpState α β) (jumpHistoryKernel next rate hr ht) 1 h1
  have he : ∀ᵐ z ∂ν,killedTerminal guard f (k+1) T z =
      if guard x then if T < y.2 then f x else
        killedTerminal guard f k (T-y.2) (restartJump z) else 0 := by
    filter_upwards [continuation_prefix_ae next rate hr ht h1] with z hz
    have hz0 : z 0 = (x,(Sum.inl (), (0 : ℝ))) :=
      congrFun hz ⟨0,Finset.mem_Iic.mpr (by omega)⟩
    have hz1 : z 1 = jumpStateUpdate next x y :=
      congrFun hz ⟨1,Finset.mem_Iic.mpr le_rfl⟩
    simp only [killedTerminal,hz0,hz1,jumpStateUpdate]
  rw [lintegral_congr_ae he]
  by_cases hg : guard x
  · simp only [if_pos hg]
    by_cases htime : T < y.2
    · simp only [if_pos htime,lintegral_const,measure_univ,mul_one]
    · simp only [if_neg htime]
      rw [← lintegral_map' (hm k (T-y.2)).aemeasurable restartJump_measurable.aemeasurable]
      rw [jumpTrajectory_restart_law]
      rfl
  · simp only [if_neg hg,lintegral_zero]

theorem killedTerminalMean_bound (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (guard : α → Prop) (f : α → ℝ≥0∞) (G : ℝ → α → ℝ≥0∞)
    (hsup : ∀ T,0 ≤ T → ∀ x,guard x →
      (∫⁻ y,if T < y.2 then f x else G (T-y.2) (next x y.1)
        ∂jumpClockMeasure (rate x) (hr x) (ht x)) ≤ G T x)
    (k : ℕ) (T : ℝ) (hT : 0 ≤ T) (x : α) :
    killedTerminalMean next rate hr ht guard f k T x ≤ G T x := by
  induction k generalizing T x with
  | zero => simp only [killedTerminalMean,killedTerminal,lintegral_zero]; exact bot_le
  | succ k ih =>
    rw [killedTerminalMean_succ]
    by_cases hg : guard x
    · simp only [if_pos hg]
      apply le_trans _ (hsup T hT x hg)
      apply lintegral_mono
      intro y
      by_cases hy : T < y.2
      · simp only [if_pos hy]; exact le_rfl
      · simp only [if_neg hy]
        exact ih (T-y.2) (by linarith) (next x y.1)
    · simp only [if_neg hg,lintegral_zero]; exact bot_le

/-- Monotone passage removes the artificial jump limit under the actual law. -/
theorem killedTerminal_limit_bound (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (guard : α → Prop) (f : α → ℝ≥0∞) (G : ℝ → α → ℝ≥0∞)
    (hsup : ∀ T,0 ≤ T → ∀ x,guard x →
      (∫⁻ y,if T < y.2 then f x else G (T-y.2) (next x y.1)
        ∂jumpClockMeasure (rate x) (hr x) (ht x)) ≤ G T x)
    (T : ℝ) (hT : 0 ≤ T) (x : α) :
    (∫⁻ z,⨆ k,killedTerminal guard f k T z ∂jumpTrajectoryLaw x next rate hr ht) ≤ G T x := by
  rw [lintegral_iSup]
  · exact iSup_le (fun k => killedTerminalMean_bound next rate hr ht guard f G hsup k T hT x)
  · intro k
    exact (killedTerminal_measurable guard f k).comp (measurable_const.prodMk measurable_id)
  · exact monotone_nat_of_le_succ (fun k z => killedTerminal_mono guard f k T z)

end
end StartupCount

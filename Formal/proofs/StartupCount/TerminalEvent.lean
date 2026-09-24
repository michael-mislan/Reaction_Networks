import proofs.StartupCount.KilledTerminal

namespace StartupCount
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 40000
variable {α β : Type*}

theorem restart_elapsed (z : ℕ → JumpState α β) (k : ℕ) :
    jumpElapsed z (k+1) = (z 1).2.2+jumpElapsed (restartJump z) k :=
  restart_wait_sum z k

theorem restart_population (z : ℕ → JumpState α β) (k : ℕ) :
    (restartJump z k).1 = (z (k+1)).1 := by cases k <;> rfl

/-- On an active holding interval the finite-jump payoff is exactly the
observable at the actual current state. -/
theorem killedTerminal_at_active (guard : α → Prop) (f : α → ℝ≥0∞)
    (k : ℕ) (T : ℝ) (z : ℕ → JumpState α β)
    (hg : ∀ j ≤ k,guard (z j).1)
    (hpre : ∀ j ≤ k,jumpElapsed z j ≤ T)
    (hpost : T < jumpElapsed z (k+1)) :
    killedTerminal guard f (k+1) T z = f (z k).1 := by
  induction k generalizing T z with
  | zero =>
    have hp : T < (z 1).2.2 := by simpa [jumpElapsed] using hpost
    rw [killedTerminal,if_pos (hg 0 le_rfl),if_pos hp]
  | succ k ih =>
    have hwait : (z 1).2.2 ≤ T := by simpa [jumpElapsed] using hpre 1 (by omega)
    rw [killedTerminal,if_pos (hg 0 (by omega)),if_neg (not_lt.mpr hwait)]
    rw [ih]
    · exact congrArg f (restart_population z k)
    · intro j hj
      rw [restart_population]
      exact hg (j+1) (by omega)
    · intro j hj
      have hh := hpre (j+1) (by omega)
      rw [restart_elapsed] at hh
      linarith
    · rw [restart_elapsed] at hpost
      linarith

def guardedLowEvent (guard : α → Prop) (count : α → ℕ) (h : ℕ) (T : ℝ) :
    Set (ℕ → JumpState α β) :=
  {z | ∃ k,(∀ j ≤ k,guard (z j).1) ∧ (∀ j ≤ k,jumpElapsed z j ≤ T) ∧
    T < jumpElapsed z (k+1) ∧ count (z k).1 ≤ h}

variable [MeasurableSpace α] [MeasurableSpace β] [Countable α] [MeasurableSingletonClass α]

theorem guardedLowEvent_measurable (guard : α → Prop) (count : α → ℕ) (h : ℕ) (T : ℝ) :
    MeasurableSet (guardedLowEvent (β := β) guard count h T) := by
  unfold guardedLowEvent
  simp only [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro k
  apply MeasurableSet.inter
  · have hall : MeasurableSet (⋂ j : ℕ,{z : ℕ → JumpState α β | j ≤ k → guard (z j).1}) := by
      apply MeasurableSet.iInter
      intro j
      apply MeasurableSet.imp (MeasurableSet.const _)
      exact (Set.to_countable {x : α | guard x}).measurableSet.preimage (measurable_pi_apply j).fst
    convert hall using 1
    ext z
    simp only [Set.mem_iInter,Set.mem_setOf_eq]
    rfl
  · apply MeasurableSet.inter
    · have hall : MeasurableSet (⋂ j : ℕ,{z : ℕ → JumpState α β | j ≤ k → jumpElapsed z j ≤ T}) := by
        apply MeasurableSet.iInter
        intro j
        exact MeasurableSet.imp (MeasurableSet.const _)
          (measurableSet_le (jumpElapsed_measurable j) measurable_const)
      convert hall using 1
      ext z
      simp only [Set.mem_iInter,Set.mem_setOf_eq]
      rfl
    · exact (measurableSet_lt measurable_const (jumpElapsed_measurable (k+1))).inter
        ((Set.to_countable {x : α | count x ≤ h}).measurableSet.preimage (measurable_pi_apply k).fst)

/-- The observable bound controls the literal low-count event at an active
holding interval, rather than an event in a comparison chain. -/
theorem guardedLowEvent_weighted_bound (μ : Measure (ℕ → JumpState α β))
    (guard : α → Prop) (count : α → ℕ) (h : ℕ) (T : ℝ) :
    ENNReal.ofReal ((9/10 : ℝ)^h)*μ (guardedLowEvent guard count h T) ≤
      ∫⁻ z,⨆ k,killedTerminal guard (fun x => ENNReal.ofReal ((9/10 : ℝ)^(count x))) k T z ∂μ := by
  let E := guardedLowEvent (β := β) guard count h T
  let a := ENNReal.ofReal ((9/10 : ℝ)^h)
  have he := guardedLowEvent_measurable (β := β) guard count h T
  have hp (z : ℕ → JumpState α β) : E.indicator (fun _ => a) z ≤
      ⨆ k,killedTerminal guard (fun x => ENNReal.ofReal ((9/10 : ℝ)^(count x))) k T z := by
    by_cases hz : z ∈ E
    · rw [Set.indicator_of_mem hz]
      obtain ⟨k,hg,hpre,hpost,hcount⟩ := hz
      have hh : (9/10 : ℝ)^h ≤ (9/10 : ℝ)^(count (z k).1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hcount
      apply le_trans (ENNReal.ofReal_le_ofReal hh)
      rw [← killedTerminal_at_active guard (fun x => ENNReal.ofReal ((9/10 : ℝ)^(count x))) k T z hg hpre hpost]
      exact le_iSup (fun j => killedTerminal guard (fun x => ENNReal.ofReal ((9/10 : ℝ)^(count x))) j T z) (k+1)
    · rw [Set.indicator_of_notMem hz]
      exact bot_le
  have hh := lintegral_mono hp (μ := μ)
  rw [lintegral_indicator he,lintegral_const,Measure.restrict_apply_univ] at hh
  exact hh

end
end StartupCount

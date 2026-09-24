import proofs.StartupCount.CrossingProbability

namespace StartupCount
open Classical MeasureTheory ProbabilityTheory RandomViability Set
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 50000
variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

def lowDuring (guard : α → Prop) (count : α → ℕ) (h : ℕ) (a b : ℝ) :
    Set (ℕ → JumpState α β) :=
  {z | ∃ t,a ≤ t ∧ t ≤ b ∧ z ∈ guardedLowEvent guard count (h-1) t}

/-- Actual trajectory-law crossing bound. Only time coverage remains abstract;
the physical source law supplies it by its existing nonexplosion theorem. -/
theorem lowDuring_probability_le (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x j,0 ≤ rate x j) (ht : ∀ x,0 < ∑ j,rate x j)
    (initial : α) (guard : α → Prop) (count : α → ℕ) (h l : ℕ) (hh : 0 < h)
    (C a b : ℝ)
    (hcover : ∀ᵐ z ∂jumpTrajectoryLaw initial next rate hr ht,
      ∃ J,(∀ j ≤ J,jumpElapsed z j ≤ a) ∧ a < jumpElapsed z (J+1))
    (hbound : ∀ x,guard x →
      (∑ j,rate x j*(if h ≤ count x ∧ count (next x j) < h then 1 else 0)) ≤
        C*(if count x ≤ l then 1 else 0)) :
    (jumpTrajectoryLaw initial next rate hr ht) (lowDuring guard count h a b) ≤
      (jumpTrajectoryLaw initial next rate hr ht) (guardedLowEvent guard count (h-1) a) +
      ∫⁻ t : ℝ,if a < t ∧ t ≤ b then ENNReal.ofReal C *
        (jumpTrajectoryLaw initial next rate hr ht) (guardedLowEvent guard count l t) else 0 := by
  have hinc : ∀ᵐ z ∂jumpTrajectoryLaw initial next rate hr ht,
      z ∈ lowDuring guard count h a b →
      z ∈ (guardedLowEvent guard count (h-1) a ∪ ⋃ k,crossingAt guard count h a b k) := by
    filter_upwards [hcover,jumpTrajectory_wait_nonneg initial next rate hr ht] with z hc hw
    rintro ⟨t,hat,htb,hlow⟩
    rcases low_interval_requires_crossing guard count h hh a b t hat htb z hw hc hlow with ha | hx
    · exact Or.inl ha
    · exact Or.inr (Set.mem_iUnion.mpr hx)
  exact (measure_mono_ae hinc).trans ((measure_union_le _ _).trans
    (add_le_add le_rfl (crossings_probability_le next rate hr ht initial guard count h l C a b hbound)))

end
end StartupCount

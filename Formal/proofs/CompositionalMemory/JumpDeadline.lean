import proofs.RandomViability.ChronologicalReward

namespace CompositionalMemory
open Classical RandomViability MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
noncomputable section
variable {α β : Type*}

/-- The first interval extending past the deadline, with every prior state retained. -/
def safeDeadlineIndex (D : Set α) (T : ℝ) (z : ℕ → JumpState α β) (K : ℕ) : Prop :=
  (∀ i ≤ K, (z i).1 ∈ D ∧ jumpElapsed z i ≤ T) ∧ T < jumpElapsed z (K+1)

def safeDeadlinePayoff (D : Set α) (f : α → ℝ≥0∞) (T : ℝ)
    (z : ℕ → JumpState α β) : ℝ≥0∞ :=
  ∑' K, if safeDeadlineIndex D T z K then f (z K).1 else 0

theorem safeDeadlineIndex_unique (D : Set α) (T : ℝ) (z : ℕ → JumpState α β)
    {K L : ℕ} (hK : safeDeadlineIndex D T z K) (hL : safeDeadlineIndex D T z L) : K=L := by
  apply le_antisymm
  · by_contra h
    have hh := (hK.1 (L+1) (by omega)).2
    exact (not_lt_of_ge hh) hL.2
  · by_contra h
    have hh := (hL.1 (K+1) (by omega)).2
    exact (not_lt_of_ge hh) hK.2

theorem safeDeadlinePayoff_eq (D : Set α) (f : α → ℝ≥0∞) (T : ℝ)
    (z : ℕ → JumpState α β) {K : ℕ} (hK : safeDeadlineIndex D T z K) :
    safeDeadlinePayoff D f T z = f (z K).1 := by
  unfold safeDeadlinePayoff
  rw [tsum_eq_single K]
  · exact if_pos hK
  · intro L hL
    exact if_neg (fun hh => hL (safeDeadlineIndex_unique D T z hh hK))

theorem safeDeadlinePayoff_le_one (D : Set α) (f : α → ℝ≥0∞) (hf : ∀ x,f x ≤ 1)
    (T : ℝ) (z : ℕ → JumpState α β) : safeDeadlinePayoff D f T z ≤ 1 := by
  by_cases h : ∃ K,safeDeadlineIndex D T z K
  · obtain ⟨K,hK⟩ := h
    rw [safeDeadlinePayoff_eq D f T z hK]
    exact hf _
  · have hh : safeDeadlinePayoff D f T z=0 := by
      apply ENNReal.tsum_eq_zero.mpr
      intro K
      exact if_neg (fun hK => h ⟨K,hK⟩)
    rw [hh]
    exact zero_le

/-- Nonexplosion yields an actual holding interval at each finite nonnegative deadline. -/
theorem deadline_interval_exists (z : ℕ → JumpState α β)
    (hd : Tendsto (jumpElapsed z) atTop atTop) (T : ℝ) (hT : 0 ≤ T) :
    ∃ K, (∀ i ≤ K,jumpElapsed z i ≤ T) ∧ T < jumpElapsed z (K+1) := by
  have he : ∃ K,T < jumpElapsed z K := (hd.eventually (eventually_gt_atTop T)).exists
  have hj := Nat.find_spec he
  have hj0 : Nat.find he ≠ 0 := by
    intro h
    rw [h] at hj
    simp only [jumpElapsed,Finset.range_zero,Finset.sum_empty] at hj
    exact (not_lt_of_ge hT) hj
  refine ⟨Nat.find he-1,?_,?_⟩
  · intro i hi
    exact le_of_not_gt (Nat.find_min he (by omega))
  · have hh : Nat.find he-1+1=Nat.find he := by omega
    rwa [hh]

variable [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α] [MeasurableSpace β]

theorem safeDeadlineIndex_measurable (D : Set α) (K : ℕ) :
    MeasurableSet {p : ℝ × (ℕ → JumpState α β) | safeDeadlineIndex D p.1 p.2 K} := by
  have hD : MeasurableSet D := (Set.to_countable D).measurableSet
  unfold safeDeadlineIndex
  apply MeasurableSet.inter
  · change MeasurableSet {p : ℝ × (ℕ → JumpState α β) | ∀ i, ∀ (_ : i ≤ K), (p.2 i).1 ∈ D ∧ jumpElapsed p.2 i ≤ p.1}
    simp only [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro _
    exact (hD.preimage (((measurable_pi_apply i).comp measurable_snd).fst)).inter
      (measurableSet_le ((jumpElapsed_measurable i).comp measurable_snd) measurable_fst)
  · exact measurableSet_lt measurable_fst ((jumpElapsed_measurable (K+1)).comp measurable_snd)

theorem safeDeadlinePayoff_measurable (D : Set α) (f : α → ℝ≥0∞) :
    Measurable (fun p : ℝ × (ℕ → JumpState α β) => safeDeadlinePayoff D f p.1 p.2) := by
  unfold safeDeadlinePayoff
  apply Measurable.tsum
  intro K
  exact Measurable.ite (safeDeadlineIndex_measurable D K)
    ((measurable_of_countable f).comp (((measurable_pi_apply K).comp measurable_snd).fst)) measurable_const

end
end CompositionalMemory

import proofs.CompositionalMemory.JumpLyapunovCrossing
import proofs.CompositionalMemory.JumpBoundedRegion
import proofs.RandomViability.JumpWaitingSupport

namespace CompositionalMemory
open RandomViability MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

variable {α β : Type*}
  [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-- Local boundedness of rates and a positive linear Lyapunov function exclude
finite accumulation of the actual state-dependent exponential holding times. -/
theorem jump_bounded_time_null (initial : α) (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b)
    (V : α → ℝ) (hV : ∀ x, 0 < V x) (c : ℝ) (hc : 0 ≤ c)
    (hgen : ∀ x, (∑ b, rate x b*(V (next x b)-V x)) ≤ c*V x)
    (hlocal : ∀ B : ℕ, ∃ q : ℝ, 0 < q ∧ ∀ x,V x ≤ B → (∑ b,rate x b) ≤ q)
    (T : ℝ) :
    jumpTrajectoryLaw initial next rate hr ht {z | ∀ K,waitingSum (fun i => (z (i+1)).2.2) K ≤ T}=0 := by
  classical
  let μ := jumpTrajectoryLaw initial next rate hr ht
  let E := {z : ℕ → JumpState α β | ∀ K,waitingSum (fun i => (z (i+1)).2.2) K ≤ T}
  have hb : ∀ b : ℕ, μ E ≤ ENNReal.ofReal (V initial*Real.exp (c*T)/(2 : ℝ)^b) := by
    intro b
    obtain ⟨q,hq,hqb⟩ := hlocal (2^b)
    let A := {z : ℕ → JumpState α β | (∀ K,waitingSum (fun i => (z (i+1)).2.2) K ≤ T) ∧
      ∀ K,V (z K).1 ≤ ((2^b : ℕ) : ℝ)}
    have hnull : μ A=0 := bounded_region_before_time_null initial next rate hr ht
      (fun x => V x ≤ ((2^b : ℕ) : ℝ)) q hq hqb T
    have hsub : E ⊆ (⋃ K,{z | lyapunovCrossingBy V ((2 : ℝ)^b) T K z}) ∪ A := by
      intro z hz
      by_cases h : ∃ j,(2 : ℝ)^b ≤ V (z j).1
      · left
        obtain ⟨j,hj⟩ := h
        exact Set.mem_iUnion.mpr ⟨j,j,le_rfl,hz j,hj⟩
      · right
        refine ⟨hz,?_⟩
        intro j
        have hj : V (z j).1 < (2 : ℝ)^b := lt_of_not_ge (fun hh => h ⟨j,hh⟩)
        simpa only [Nat.cast_pow,Nat.cast_ofNat] using hj.le
    calc
      μ E ≤ μ ((⋃ K,{z | lyapunovCrossingBy V ((2 : ℝ)^b) T K z}) ∪ A) := measure_mono hsub
      _ ≤ μ (⋃ K,{z | lyapunovCrossingBy V ((2 : ℝ)^b) T K z})+μ A := measure_union_le _ _
      _ ≤ _ := by
        rw [hnull,add_zero]
        exact jump_lyapunov_crossing_any initial next rate hr ht V hV c hc hgen ((2 : ℝ)^b) T (by positivity)
  have hrzero : Tendsto (fun b : ℕ => V initial*Real.exp (c*T)/(2 : ℝ)^b) atTop (𝓝 0) := by
    simpa only [one_div_pow,mul_one_div,mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
        (by norm_num : (1/2 : ℝ) < 1)).const_mul (V initial*Real.exp (c*T))
  have hezero : Tendsto (fun b : ℕ => ENNReal.ofReal (V initial*Real.exp (c*T)/(2 : ℝ)^b)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using (ENNReal.continuous_ofReal.tendsto 0).comp hrzero
  apply le_antisymm ?_ (by positivity)
  exact ge_of_tendsto hezero (Eventually.of_forall hb)

theorem jump_times_diverge (initial : α) (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b)
    (V : α → ℝ) (hV : ∀ x, 0 < V x) (c : ℝ) (hc : 0 ≤ c)
    (hgen : ∀ x, (∑ b, rate x b*(V (next x b)-V x)) ≤ c*V x)
    (hlocal : ∀ B : ℕ, ∃ q : ℝ, 0 < q ∧ ∀ x,V x ≤ B → (∑ b,rate x b) ≤ q) :
    ∀ᵐ z ∂jumpTrajectoryLaw initial next rate hr ht,
      Tendsto (waitingSum (fun i => (z (i+1)).2.2)) atTop atTop := by
  have hb : ∀ᵐ z ∂jumpTrajectoryLaw initial next rate hr ht,
      ∀ M : ℕ, ¬(∀ K,waitingSum (fun i => (z (i+1)).2.2) K ≤ (M : ℝ)) := by
    apply ae_all_iff.mpr
    intro M
    exact (measure_eq_zero_iff_ae_notMem).mp (jump_bounded_time_null initial next rate hr ht V hV c hc hgen hlocal M)
  filter_upwards [hb,jumpTrajectory_wait_nonneg initial next rate hr ht] with z hz hw
  have hm : Monotone (waitingSum (fun i => (z (i+1)).2.2)) := by
    apply monotone_nat_of_le_succ
    intro K
    change (∑ i ∈ Finset.range K,(z (i+1)).2.2) ≤ ∑ i ∈ Finset.range (K+1),(z (i+1)).2.2
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_right (hw K)
  apply (tendsto_atTop_atTop_iff_of_monotone hm).mpr
  intro T
  obtain ⟨M,hM⟩ := exists_nat_gt T
  have hnot : ¬∀ K,waitingSum (fun i => (z (i+1)).2.2) K ≤ (M : ℝ) := hz M
  push Not at hnot
  obtain ⟨K,hK⟩ := hnot
  exact ⟨K,hM.le.trans hK.le⟩

end CompositionalMemory

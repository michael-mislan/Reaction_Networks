import proofs.ResourceLimitedCompetition.PartitionPopulation
import proofs.FiniteCopy.UniformizedBounds

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy Set
open scoped NNReal

noncomputable local instance GlobalPartitionDecidableEq (D : Finset PopulationState) : DecidableEq (StoppedPopulation D) :=
  Classical.decEq _

theorem partition_population_nonneg (N M : ℕ) (zL zH : ℝ)
    (x : StoppedPopulation (activeDomain N M zL zH)) :
    0 ≤ partitionPopulationObservable N M zL zH (activeDomain N M zL zH) x := by
  classical
  cases x with
  | inl s =>
    exact partitionReserve_nonneg N M s.val.divisions
      (active_divisions_strict N M zL zH s).le
  | inr e => exact partitionFlag_nonneg N M zL zH _ e

theorem global_partition_generator (γ : ℝ) (hγ : 0 ≤ γ) (Ω N M : ℕ) (hN : 0 < N)
    (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (x : StoppedPopulation (activeDomain N M zL zH)) :
    (stoppedPopulationModel γ hγ Ω N M zL zH (activeDomain N M zL zH)).generator
      (partitionPopulationObservable N M zL zH (activeDomain N M zL zH)) x ≤ 0 := by
  classical
  cases x with
  | inr e => exact (terminal_generator γ hγ Ω N M zL zH _ _ e).le
  | inl s =>
    have h := active_generator_le γ hγ Ω N M zL zH (activeDomain N M zL zH)
      (partitionPopulationObservable N M zL zH (activeDomain N M zL zH)) s
      (fun e => partitionReserve N M (eventOutcome N ⟨s,e⟩).divisions+
        partitionFlag N M zL zH ⟨s,e⟩)
      (partition_next_le N M zL zH _ s (active_divisions_strict N M zL zH s))
    apply h.trans
    simp only [partitionPopulationObservable]
    rw [Fintype.sum_sigma]
    apply Finset.sum_nonpos
    intro i _
    rw [Fintype.sum_sum_type]
    simp only [resident_partition_flag,eventOutcome,residentAt,add_zero,sub_self,
      mul_zero,Finset.sum_const_zero,zero_add]
    exact growth_partition_compensated γ hγ Ω N M hN zL zH hzL hzH _ s i

def partitionFailureSet (N M : ℕ) (zL zH : ℝ) (D : Finset PopulationState) :
    Set (StoppedPopulation D) :=
  {x | ∃ e, x=.inr e ∧ eventReason N M zL zH e=.partition}

theorem global_partition_failure_bound (γ : ℝ) (hγ : 0 ≤ γ) (Ω N M : ℕ) (hN : 0 < N)
    (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (q t : ℝ≥0) (hq : 0 < (q : ℝ))
    (hbound : ∀ x, (stoppedPopulationModel γ hγ Ω N M zL zH (activeDomain N M zL zH)).total x ≤ q)
    (s : ActiveState (activeDomain N M zL zH)) :
    ((stoppedPopulationModel γ hγ Ω N M zL zH (activeDomain N M zL zH)).uniformize q hq hbound).poissonized (q*t)
        (FiniteKernel.eventIndicator (partitionFailureSet N M zL zH (activeDomain N M zL zH)))
        (.inl s) ≤ partitionReserve N M s.val.divisions := by
  classical
  have h := (stoppedPopulationModel γ hγ Ω N M zL zH (activeDomain N M zL zH)).uniformized_event_bound q t hq hbound
      (partitionFailureSet N M zL zH (activeDomain N M zL zH))
      (partitionPopulationObservable N M zL zH (activeDomain N M zL zH)) 1 0
      (partition_population_nonneg N M zL zH)
      (by rintro x ⟨e,rfl,he⟩; simp [partitionPopulationObservable,partitionFlag,he])
      (global_partition_generator γ hγ Ω N M hN zL zH hzL hzH) (.inl s)
  simpa only [one_mul,mul_zero,add_zero,partitionPopulationObservable] using h

end ResourceLimitedCompetition

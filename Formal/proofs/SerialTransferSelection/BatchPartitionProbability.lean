import proofs.SerialTransferSelection.BatchPartitionPopulation
import proofs.FiniteCopy.UniformizedBounds

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Set
open scoped NNReal

noncomputable local instance GlobalPartitionDecidableEq (D : Finset PopulationState) : DecidableEq (StoppedPopulation D) :=
  Classical.decEq _

theorem phase_partition_population_nonneg (N M W0 : ℕ) (hN : 0 < N) (hW : W0 ≤ 2*N*M) (zL zH : ℝ)
    (x : StoppedPopulation (phaseActiveDomain N M W0 zL zH)) :
    0 ≤ phasePartitionPopulationObservable N M W0 zL zH (phaseActiveDomain N M W0 zL zH) x := by
  classical
  cases x with
  | inl s =>
    exact phasePartitionReserve_nonneg N M s.val.divisions
      (phase_active_reserve N M W0 hN hW zL zH s).le
  | inr e => exact phasePartitionFlag_nonneg N W0 zL zH _ e

theorem phase_global_partition_generator (γ : ℝ) (hγ : 0 ≤ γ) (Ω N M W0 : ℕ) (hN : 0 < N) (hW : W0 ≤ 2*N*M)
    (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (x : StoppedPopulation (phaseActiveDomain N M W0 zL zH)) :
    (phaseStoppedModel γ hγ Ω N W0 zL zH (phaseActiveDomain N M W0 zL zH)).generator
      (phasePartitionPopulationObservable N M W0 zL zH (phaseActiveDomain N M W0 zL zH)) x ≤ 0 := by
  classical
  cases x with
  | inr e => exact (phase_terminal_generator γ hγ Ω N W0 zL zH _ _ e).le
  | inl s =>
    have h := phase_active_generator_le γ hγ Ω N W0 zL zH (phaseActiveDomain N M W0 zL zH)
      (phasePartitionPopulationObservable N M W0 zL zH (phaseActiveDomain N M W0 zL zH)) s
      (fun e => phasePartitionReserve N M (eventOutcome N ⟨s,e⟩).divisions+
        phasePartitionFlag N W0 zL zH ⟨s,e⟩)
      (phase_partition_next_le N M W0 zL zH _ s (phase_active_reserve N M W0 hN hW zL zH s))
    apply h.trans
    simp only [phasePartitionPopulationObservable]
    rw [Fintype.sum_sigma]
    apply Finset.sum_nonpos
    intro i _
    rw [Fintype.sum_sum_type]
    simp only [phase_resident_partition_flag,eventOutcome,residentAt,add_zero,sub_self,
      mul_zero,Finset.sum_const_zero,zero_add]
    exact phase_growth_partition_compensated γ hγ Ω N M W0 hN zL zH hzL hzH _ s i

def phasePartitionFailureSet (N W0 : ℕ) (zL zH : ℝ) (D : Finset PopulationState) :
    Set (StoppedPopulation D) :=
  {x | ∃ e, x=.inr e ∧ phaseEventReason N W0 zL zH e=.partition}

theorem phase_global_partition_failure_bound (γ : ℝ) (hγ : 0 ≤ γ) (Ω N M W0 : ℕ) (hN : 0 < N) (hW : W0 ≤ 2*N*M)
    (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (q t : ℝ≥0) (hq : 0 < (q : ℝ))
    (hbound : ∀ x, (phaseStoppedModel γ hγ Ω N W0 zL zH (phaseActiveDomain N M W0 zL zH)).total x ≤ q)
    (s : ActiveState (phaseActiveDomain N M W0 zL zH)) :
    ((phaseStoppedModel γ hγ Ω N W0 zL zH (phaseActiveDomain N M W0 zL zH)).uniformize q hq hbound).poissonized (q*t)
        (FiniteKernel.eventIndicator (phasePartitionFailureSet N W0 zL zH (phaseActiveDomain N M W0 zL zH)))
        (.inl s) ≤ phasePartitionReserve N M s.val.divisions := by
  classical
  have h := (phaseStoppedModel γ hγ Ω N W0 zL zH (phaseActiveDomain N M W0 zL zH)).uniformized_event_bound q t hq hbound
      (phasePartitionFailureSet N W0 zL zH (phaseActiveDomain N M W0 zL zH))
      (phasePartitionPopulationObservable N M W0 zL zH (phaseActiveDomain N M W0 zL zH)) 1 0
      (phase_partition_population_nonneg N M W0 hN hW zL zH)
      (by rintro x ⟨e,rfl,he⟩; simp [phasePartitionPopulationObservable,phasePartitionFlag,he])
      (phase_global_partition_generator γ hγ Ω N M W0 hN hW zL zH hzL hzH) (.inl s)
  simpa only [one_mul,mul_zero,add_zero,phasePartitionPopulationObservable] using h

end SerialTransferSelection

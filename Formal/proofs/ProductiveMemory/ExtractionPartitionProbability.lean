import proofs.ProductiveMemory.ExtractionPartitionPopulation
import proofs.FiniteCopy.UniformizedBounds

namespace ProductiveMemory
set_option Elab.async false
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Set
open scoped NNReal

noncomputable local instance ProductivePartitionDecidableEq (D : Finset ProductiveState) : DecidableEq (ProductiveStopped D) :=
  Classical.decEq _

theorem productive_partition_population_nonneg (N M W0 J : ℕ) (hN : 0 < N) (hW : W0 ≤ 2*N*M) (rho zL zH : ℝ)
    (x : ProductiveStopped (productiveActiveDomain N M W0 J rho zL zH)) :
    0 ≤ productivePartitionPopulationObservable N M W0 J rho zL zH (productiveActiveDomain N M W0 J rho zL zH) x := by
  classical
  cases x with
  | inl s =>
    exact productivePartitionReserve_nonneg N M s.val.population.divisions
      (productive_active_reserve N M W0 J hN hW rho zL zH s).le
  | inr e => exact productivePartitionFlag_nonneg N W0 J rho zL zH _ e

theorem productive_global_partition_generator (γ : ℝ) (hγ : 0 ≤ γ) (Ω N M W0 J : ℕ) (hN : 0 < N) (hW : W0 ≤ 2*N*M)
    (rho zL zH : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (x : ProductiveStopped (productiveActiveDomain N M W0 J rho zL zH)) :
    (productiveStoppedModel rho γ (by linarith [hr.1]) hγ Ω N W0 J zL zH (productiveActiveDomain N M W0 J rho zL zH)).generator
      (productivePartitionPopulationObservable N M W0 J rho zL zH (productiveActiveDomain N M W0 J rho zL zH)) x ≤ 0 := by
  classical
  cases x with
  | inr e => exact (productive_terminal_generator rho γ (by linarith [hr.1]) hγ Ω N W0 J zL zH _ _ e).le
  | inl s =>
    rw [productive_active_generator]
    calc
      _ ≤ ∑ e : ProductiveEvent s.val, productiveRate rho γ Ω s.val e*
          (productivePartitionReserve N M (productiveOutcome N s.val e).population.divisions+
            productivePartitionFlag N W0 J rho zL zH ⟨s,e⟩-
            productivePartitionReserve N M s.val.population.divisions) := by
        apply Finset.sum_le_sum
        intro e _
        apply mul_le_mul_of_nonneg_left _ (productive_rate_nonneg rho γ (by linarith [hr.1]) hγ Ω s.val e)
        exact sub_le_sub_right (productive_partition_next_le N M W0 J rho zL zH _ s
          (productive_active_reserve N M W0 J hN hW rho zL zH s) e) _
      _ ≤ 0 := by
        rw [Fintype.sum_sum_type]
        have hex : (∑ i : Fin s.val.population.live.length, productiveRate rho γ Ω s.val (.inr i)*
            (productivePartitionReserve N M (productiveOutcome N s.val (.inr i)).population.divisions+
              productivePartitionFlag N W0 J rho zL zH ⟨s,.inr i⟩-
              productivePartitionReserve N M s.val.population.divisions)) = 0 := by
          simp only [productive_extraction_partition_flag,productiveOutcome,extractionAt,add_zero,sub_self,
            mul_zero,Finset.sum_const_zero]
        rw [hex,add_zero,Fintype.sum_sigma]
        apply Finset.sum_nonpos
        intro i _
        rw [Fintype.sum_sum_type]
        simp only [productive_resident_partition_flag,productiveOutcome,residentAt,add_zero,sub_self,
          mul_zero,Finset.sum_const_zero,zero_add]
        exact productive_growth_partition_compensated γ hγ Ω N M W0 J hN rho zL zH hr hzL hzH _ s i

def productivePartitionFailureSet (N W0 J : ℕ) (rho zL zH : ℝ) (D : Finset ProductiveState) :
    Set (ProductiveStopped D) :=
  {x | ∃ e, x=.inr e ∧ productiveReason N W0 J rho zL zH e=.partition}

theorem productive_global_partition_failure_bound (γ : ℝ) (hγ : 0 ≤ γ) (Ω N M W0 J : ℕ) (hN : 0 < N) (hW : W0 ≤ 2*N*M)
    (rho zL zH : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (q t : ℝ≥0) (hq : 0 < (q : ℝ))
    (hbound : ∀ x, (productiveStoppedModel rho γ (by linarith [hr.1]) hγ Ω N W0 J zL zH (productiveActiveDomain N M W0 J rho zL zH)).total x ≤ q)
    (s : ProductiveActive (productiveActiveDomain N M W0 J rho zL zH)) :
    ((productiveStoppedModel rho γ (by linarith [hr.1]) hγ Ω N W0 J zL zH (productiveActiveDomain N M W0 J rho zL zH)).uniformize q hq hbound).poissonized (q*t)
        (FiniteKernel.eventIndicator (productivePartitionFailureSet N W0 J rho zL zH (productiveActiveDomain N M W0 J rho zL zH)))
        (.inl s) ≤ productivePartitionReserve N M s.val.population.divisions := by
  classical
  have h := (productiveStoppedModel rho γ (by linarith [hr.1]) hγ Ω N W0 J zL zH (productiveActiveDomain N M W0 J rho zL zH)).uniformized_event_bound q t hq hbound
      (productivePartitionFailureSet N W0 J rho zL zH (productiveActiveDomain N M W0 J rho zL zH))
      (productivePartitionPopulationObservable N M W0 J rho zL zH (productiveActiveDomain N M W0 J rho zL zH)) 1 0
      (productive_partition_population_nonneg N M W0 J hN hW rho zL zH)
      (by rintro x ⟨e,rfl,he⟩; simp [productivePartitionPopulationObservable,productivePartitionFlag,he])
      (productive_global_partition_generator γ hγ Ω N M W0 J hN hW rho zL zH hr hzL hzH) (.inl s)
  simpa only [one_mul,mul_zero,add_zero,productivePartitionPopulationObservable] using h

end ProductiveMemory

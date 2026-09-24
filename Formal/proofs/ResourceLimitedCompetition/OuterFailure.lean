import proofs.ResourceLimitedCompetition.GlobalOuter

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy CoreCouplingCAC Set
open scoped NNReal

noncomputable local instance OuterFailureDecidableEq (D : Finset PopulationState) : DecidableEq (StoppedPopulation D) :=
  Classical.decEq _

def outerFailureSet (N M : ℕ) (zL zH : ℝ) (D : Finset PopulationState) :
    Set (StoppedPopulation D) :=
  {x | ∃ e, x=.inr e ∧ eventReason N M zL zH e=.outer}

theorem global_outer_failure_bound (N M : ℕ) (hN : 1 ≤ N)
    (hlarge : (140000000000000000000 : ℝ) ≤ N)
    (zL zH γ : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hsL : Stationary sourceRates (lift sourceRates zL))
    (hsH : Stationary sourceRates (lift sourceRates zH))
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (q t : ℝ≥0) (hq : 0 < (q : ℝ))
    (hbound : ∀ x, (stoppedPopulationModel γ hγ (4*(N*M)) N M zL zH
      (activeDomain N M zL zH)).total x ≤ q)
    (s : ActiveState (activeDomain N M zL zH)) :
    Real.exp ((N : ℝ)*localAlpha*outerEnergy)*
      ((stoppedPopulationModel γ hγ (4*(N*M)) N M zL zH
        (activeDomain N M zL zH)).uniformize q hq hbound).poissonized (q*t)
        (FiniteKernel.eventIndicator (outerFailureSet N M zL zH (activeDomain N M zL zH)))
        (.inl s) ≤
      potentialSum (cellOuter N zL zH) s.val+outerReserve N M s.val.divisions+
        (t : ℝ)*(8*(M : ℝ)*((N : ℝ)*localAlpha*innerEnergy/672)*
          Real.exp ((N : ℝ)*localAlpha*innerEnergy/2)) := by
  classical
  apply (stoppedPopulationModel γ hγ (4*(N*M)) N M zL zH
    (activeDomain N M zL zH)).uniformized_event_bound q t hq hbound
      (outerFailureSet N M zL zH (activeDomain N M zL zH))
      (outerPopulationObservable N M zL zH (activeDomain N M zL zH))
  · exact outer_population_nonneg N M zL zH
  · rintro x ⟨e,rfl,he⟩
    simp [outerPopulationObservable,he]
  · exact global_outer_generator N M hN hlarge zL zH γ hzL hzH hsL hsH hγ hγmax

end ResourceLimitedCompetition

import proofs.SerialTransferSelection.BatchSpatialBoundary
import proofs.FiniteCopy.UniformizedBounds

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set
open scoped NNReal

noncomputable local instance GlobalSpatialDecidableEq (D : Finset PopulationState) : DecidableEq (StoppedPopulation D) :=
  Classical.decEq _

theorem phase_global_spatial_generator (N M W0 : ℕ) (hN : 1 ≤ N)
    (hlarge : (140000000000000000000 : ℝ) ≤ N)
    (zL zH γ : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hsL : Stationary sourceRates (lift sourceRates zL))
    (hsH : Stationary sourceRates (lift sourceRates zH))
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (x : StoppedPopulation (phaseActiveDomain N M W0 zL zH)) :
    (phaseStoppedModel γ hγ (4*W0) N W0 zL zH (phaseActiveDomain N M W0 zL zH)).generator
      (phaseSpatialPopulationObservable N W0 zL zH (phaseActiveDomain N M W0 zL zH)) x ≤
      16*(M : ℝ)*((N : ℝ)*localAlpha*innerEnergy/672)*
        Real.exp ((N : ℝ)*localAlpha*innerEnergy/2) := by
  classical
  cases x with
  | inr e =>
    rw [phase_terminal_generator]
    unfold localAlpha innerEnergy outerEnergy
    positivity
  | inl s =>
    have hgen := phase_active_generator_le γ hγ (4*W0) N W0 zL zH
      (phaseActiveDomain N M W0 zL zH)
      (phaseSpatialPopulationObservable N W0 zL zH (phaseActiveDomain N M W0 zL zH)) s
      (rawEventPotential (cellSpatial N zL zH) s.val)
      (phase_spatial_next_le_raw N W0 hlarge zL zH _ s)
    have hraw := phase_raw_spatial_generator_bound N M W0 hN hlarge zL zH γ
      hzL hzH hsL hsH hγ hγmax s
    change (phaseStoppedModel γ hγ (4*W0) N W0 zL zH
      (phaseActiveDomain N M W0 zL zH)).generator
      (phaseSpatialPopulationObservable N W0 zL zH (phaseActiveDomain N M W0 zL zH)) (.inl s) ≤ _ at hgen
    have h := hgen.trans hraw
    convert h using 1
    ring

def phaseDivisionFailureSet (N W0 : ℕ) (zL zH : ℝ) (D : Finset PopulationState) :
    Set (StoppedPopulation D) :=
  {x | ∃ e, x=.inr e ∧ phaseEventReason N W0 zL zH e=.divisionEnergy}

theorem phase_global_division_failure_bound (N M W0 : ℕ) (hN : 1 ≤ N)
    (hlarge : (140000000000000000000 : ℝ) ≤ N)
    (zL zH γ : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hsL : Stationary sourceRates (lift sourceRates zL))
    (hsH : Stationary sourceRates (lift sourceRates zH))
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (q t : ℝ≥0) (hq : 0 < (q : ℝ))
    (hbound : ∀ x, (phaseStoppedModel γ hγ (4*W0) N W0 zL zH
      (phaseActiveDomain N M W0 zL zH)).total x ≤ q)
    (s : ActiveState (phaseActiveDomain N M W0 zL zH)) :
    Real.exp (2*(N : ℝ)*localAlpha*innerEnergy)*
      ((phaseStoppedModel γ hγ (4*W0) N W0 zL zH
        (phaseActiveDomain N M W0 zL zH)).uniformize q hq hbound).poissonized (q*t)
        (FiniteKernel.eventIndicator (phaseDivisionFailureSet N W0 zL zH (phaseActiveDomain N M W0 zL zH)))
        (.inl s) ≤
      potentialSum (cellSpatial N zL zH) s.val+
        (t : ℝ)*(16*(M : ℝ)*((N : ℝ)*localAlpha*innerEnergy/672)*
          Real.exp ((N : ℝ)*localAlpha*innerEnergy/2)) := by
  classical
  apply (phaseStoppedModel γ hγ (4*W0) N W0 zL zH
    (phaseActiveDomain N M W0 zL zH)).uniformized_event_bound q t hq hbound
      (phaseDivisionFailureSet N W0 zL zH (phaseActiveDomain N M W0 zL zH))
      (phaseSpatialPopulationObservable N W0 zL zH (phaseActiveDomain N M W0 zL zH))
  · exact phase_spatial_population_nonneg N W0 zL zH _
  · rintro x ⟨e,rfl,he⟩
    simp [phaseSpatialPopulationObservable,he]
  · exact phase_global_spatial_generator N M W0 hN hlarge zL zH γ hzL hzH hsL hsH hγ hγmax

end SerialTransferSelection

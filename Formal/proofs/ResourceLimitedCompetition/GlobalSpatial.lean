import proofs.ResourceLimitedCompetition.SpatialPopulationBoundary
import proofs.FiniteCopy.UniformizedBounds

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy CoreCouplingCAC Set
open scoped NNReal

noncomputable local instance GlobalSpatialDecidableEq (D : Finset PopulationState) : DecidableEq (StoppedPopulation D) :=
  Classical.decEq _

theorem global_spatial_generator (N M : ℕ) (hN : 1 ≤ N)
    (hlarge : (140000000000000000000 : ℝ) ≤ N)
    (zL zH γ : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hsL : Stationary sourceRates (lift sourceRates zL))
    (hsH : Stationary sourceRates (lift sourceRates zH))
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (x : StoppedPopulation (activeDomain N M zL zH)) :
    (stoppedPopulationModel γ hγ (4*(N*M)) N M zL zH (activeDomain N M zL zH)).generator
      (spatialPopulationObservable N M zL zH (activeDomain N M zL zH)) x ≤
      8*(M : ℝ)*((N : ℝ)*localAlpha*innerEnergy/672)*
        Real.exp ((N : ℝ)*localAlpha*innerEnergy/2) := by
  classical
  have hc : 0 ≤ ((N : ℝ)*localAlpha*innerEnergy/672)*
      (2*Real.exp ((N : ℝ)*localAlpha*innerEnergy/2)) := by
    unfold localAlpha innerEnergy outerEnergy
    positivity
  cases x with
  | inr e =>
    rw [terminal_generator]
    unfold localAlpha innerEnergy outerEnergy
    positivity
  | inl s =>
    have hs := activeDomain_safe N M zL zH s.val s.property
    have hbox := (mem_populationBox N M s.val).mp (Finset.mem_filter.mp s.property).1
    have hlocal (i : Fin s.val.live.length) := cellSpatial_source_bound N hN hlarge
      zL zH γ hzL hzH hsL hsH hγ hγmax s.val.resource (4*(N*M)) hs.2.1
      (selectedCell s.val i) (hs.2.2.2.2.1 _ (selected_mem _ _)).1
      (hs.2.2.2.2.1 _ (selected_mem _ _)).2.le (hs.2.2.2.2.2 _ (selected_mem _ _))
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hlocal i)
    have hgen := population_potential_generator_le γ hγ (4*(N*M)) N M zL zH
      (activeDomain N M zL zH)
      (spatialPopulationObservable N M zL zH (activeDomain N M zL zH)) s
      (cellSpatial N zL zH) rfl (spatial_next_le_raw N M hlarge zL zH _ s)
    have hlen : (s.val.live.length : ℝ) ≤ 4*(M : ℝ) := by exact_mod_cast hbox.2.1.1
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
    have hscale := mul_le_mul_of_nonneg_right hlen hc
    nlinarith only [hgen,hsum,hscale]

def divisionFailureSet (N M : ℕ) (zL zH : ℝ) (D : Finset PopulationState) :
    Set (StoppedPopulation D) :=
  {x | ∃ e, x=.inr e ∧ eventReason N M zL zH e=.divisionEnergy}

theorem global_division_failure_bound (N M : ℕ) (hN : 1 ≤ N)
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
    Real.exp (2*(N : ℝ)*localAlpha*innerEnergy)*
      ((stoppedPopulationModel γ hγ (4*(N*M)) N M zL zH
        (activeDomain N M zL zH)).uniformize q hq hbound).poissonized (q*t)
        (FiniteKernel.eventIndicator (divisionFailureSet N M zL zH (activeDomain N M zL zH)))
        (.inl s) ≤
      potentialSum (cellSpatial N zL zH) s.val+
        (t : ℝ)*(8*(M : ℝ)*((N : ℝ)*localAlpha*innerEnergy/672)*
          Real.exp ((N : ℝ)*localAlpha*innerEnergy/2)) := by
  classical
  apply (stoppedPopulationModel γ hγ (4*(N*M)) N M zL zH
    (activeDomain N M zL zH)).uniformized_event_bound q t hq hbound
      (divisionFailureSet N M zL zH (activeDomain N M zL zH))
      (spatialPopulationObservable N M zL zH (activeDomain N M zL zH))
  · exact spatial_population_nonneg N M zL zH _
  · rintro x ⟨e,rfl,he⟩
    simp [spatialPopulationObservable,he]
  · exact global_spatial_generator N M hN hlarge zL zH γ hzL hzH hsL hsH hγ hγmax

end ResourceLimitedCompetition

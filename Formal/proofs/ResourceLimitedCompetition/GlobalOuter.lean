import proofs.ResourceLimitedCompetition.OuterPopulationBoundary
import proofs.FiniteCopy.UniformizedBounds

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy CoreCouplingCAC Set
open scoped NNReal

noncomputable local instance GlobalOuterDecidableEq (D : Finset PopulationState) : DecidableEq (StoppedPopulation D) :=
  Classical.decEq _

theorem outer_population_nonneg (N M : ℕ) (zL zH : ℝ)
    (x : StoppedPopulation (activeDomain N M zL zH)) :
    0 ≤ outerPopulationObservable N M zL zH (activeDomain N M zL zH) x := by
  classical
  cases x with
  | inl s =>
    have hb := (mem_populationBox N M s.val).mp (Finset.mem_filter.mp s.property).1
    exact add_nonneg (sum_map_nonneg _ (cellOuter_nonneg N zL zH) _)
      (outerReserve_nonneg N M s.val.divisions hb.2.2)
  | inr e =>
    simp only [outerPopulationObservable]
    split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl

theorem global_outer_generator (N M : ℕ) (hN : 1 ≤ N)
    (hlarge : (140000000000000000000 : ℝ) ≤ N)
    (zL zH γ : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hsL : Stationary sourceRates (lift sourceRates zL))
    (hsH : Stationary sourceRates (lift sourceRates zH))
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (x : StoppedPopulation (activeDomain N M zL zH)) :
    (stoppedPopulationModel γ hγ (4*(N*M)) N M zL zH (activeDomain N M zL zH)).generator
      (outerPopulationObservable N M zL zH (activeDomain N M zL zH)) x ≤
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
    have hlocal (i : Fin s.val.live.length) := cellOuter_source_bound N hN hlarge
      zL zH γ hzL hzH hsL hsH hγ hγmax s.val.resource (4*(N*M)) hs.2.1
      (selectedCell s.val i) (hs.2.2.2.2.1 _ (selected_mem _ _)).1
      (hs.2.2.2.2.2 _ (selected_mem _ _))
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hlocal i)
    have hgen := active_generator_le γ hγ (4*(N*M)) N M zL zH (activeDomain N M zL zH)
      (outerPopulationObservable N M zL zH (activeDomain N M zL zH)) s
      (fun e => rawEventPotential (cellOuter N zL zH) s.val e+outerReserve N M s.val.divisions)
      (outer_next_le_raw N M zL zH _ s hbox.2.2)
    have hcancel (a b c : ℝ) : a+c-(b+c)=a-b := by ring
    simp only [outerPopulationObservable,hcancel] at hgen
    rw [raw_event_generator_sum] at hgen
    have hlen : (s.val.live.length : ℝ) ≤ 4*(M : ℝ) := by exact_mod_cast hbox.2.1.1
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
    have hscale := mul_le_mul_of_nonneg_right hlen hc
    nlinarith only [hgen,hsum,hscale]

end ResourceLimitedCompetition

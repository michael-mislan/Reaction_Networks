import proofs.SerialTransferSelection.BatchOuterBoundary
import proofs.FiniteCopy.UniformizedBounds

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set
open scoped NNReal

noncomputable local instance GlobalOuterDecidableEq (D : Finset PopulationState) : DecidableEq (StoppedPopulation D) :=
  Classical.decEq _

theorem phase_outer_population_nonneg (N M W0 : ℕ) (zL zH : ℝ)
    (x : StoppedPopulation (phaseActiveDomain N M W0 zL zH)) :
    0 ≤ phaseOuterPopulationObservable N M W0 zL zH (phaseActiveDomain N M W0 zL zH) x := by
  classical
  cases x with
  | inl s =>
    have hb := (mem_phasePopulationBox N M W0 s.val).mp (Finset.mem_filter.mp s.property).1
    exact add_nonneg (sum_map_nonneg _ (cellOuter_nonneg N zL zH) _)
      (phaseOuterReserve_nonneg N M s.val.divisions hb.2.2)
  | inr e =>
    simp only [phaseOuterPopulationObservable]
    split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl

theorem phase_global_outer_generator (N M W0 : ℕ) (hN : 1 ≤ N)
    (hlarge : (140000000000000000000 : ℝ) ≤ N)
    (zL zH γ : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hsL : Stationary sourceRates (lift sourceRates zL))
    (hsH : Stationary sourceRates (lift sourceRates zH))
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (x : StoppedPopulation (phaseActiveDomain N M W0 zL zH)) :
    (phaseStoppedModel γ hγ (4*W0) N W0 zL zH (phaseActiveDomain N M W0 zL zH)).generator
      (phaseOuterPopulationObservable N M W0 zL zH (phaseActiveDomain N M W0 zL zH)) x ≤
      16*(M : ℝ)*((N : ℝ)*localAlpha*innerEnergy/672)*
        Real.exp ((N : ℝ)*localAlpha*innerEnergy/2) := by
  classical
  have hc : 0 ≤ ((N : ℝ)*localAlpha*innerEnergy/672)*
      (2*Real.exp ((N : ℝ)*localAlpha*innerEnergy/2)) := by
    unfold localAlpha innerEnergy outerEnergy
    positivity
  cases x with
  | inr e =>
    rw [phase_terminal_generator]
    unfold localAlpha innerEnergy outerEnergy
    positivity
  | inl s =>
    have hs := phaseActiveDomain_safe N M W0 zL zH s.val s.property
    have hbox := (mem_phasePopulationBox N M W0 s.val).mp (Finset.mem_filter.mp s.property).1
    have hlocal (i : Fin s.val.live.length) := cellOuter_source_bound N hN hlarge
      zL zH γ hzL hzH hsL hsH hγ hγmax s.val.resource (4*W0) hs.2.1
      (selectedCell s.val i) (hs.2.2.2.2.1 _ (selected_mem _ _)).1
      (phase_active_source_energy N M W0 zL zH s _ (selected_mem _ _))
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hlocal i)
    have hgen := phase_active_generator_le γ hγ (4*W0) N W0 zL zH (phaseActiveDomain N M W0 zL zH)
      (phaseOuterPopulationObservable N M W0 zL zH (phaseActiveDomain N M W0 zL zH)) s
      (fun e => rawEventPotential (cellOuter N zL zH) s.val e+phaseOuterReserve N M s.val.divisions)
      (phase_outer_next_le_raw N M W0 zL zH _ s hbox.2.2)
    have hcancel (a b c : ℝ) : a+c-(b+c)=a-b := by ring
    simp only [phaseOuterPopulationObservable,hcancel] at hgen
    rw [raw_event_generator_sum] at hgen
    have hlen : (s.val.live.length : ℝ) ≤ 8*(M : ℝ) := by exact_mod_cast hbox.2.1.1
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
    have hscale := mul_le_mul_of_nonneg_right hlen hc
    nlinarith only [hgen,hsum,hscale]

def phaseOuterFailureSet (N W0 : ℕ) (zL zH : ℝ) (D : Finset PopulationState) :
    Set (StoppedPopulation D) :=
  {x | ∃ e, x=.inr e ∧ phaseEventReason N W0 zL zH e=.outer}

theorem phase_global_outer_failure_bound (N M W0 : ℕ) (hN : 1 ≤ N)
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
    Real.exp ((N : ℝ)*localAlpha*(8*innerEnergy))*
      ((phaseStoppedModel γ hγ (4*W0) N W0 zL zH
        (phaseActiveDomain N M W0 zL zH)).uniformize q hq hbound).poissonized (q*t)
        (FiniteKernel.eventIndicator (phaseOuterFailureSet N W0 zL zH (phaseActiveDomain N M W0 zL zH)))
        (.inl s) ≤
      potentialSum (cellOuter N zL zH) s.val+phaseOuterReserve N M s.val.divisions+
        (t : ℝ)*(16*(M : ℝ)*((N : ℝ)*localAlpha*innerEnergy/672)*
          Real.exp ((N : ℝ)*localAlpha*innerEnergy/2)) := by
  classical
  apply (phaseStoppedModel γ hγ (4*W0) N W0 zL zH
    (phaseActiveDomain N M W0 zL zH)).uniformized_event_bound q t hq hbound
      (phaseOuterFailureSet N W0 zL zH (phaseActiveDomain N M W0 zL zH))
      (phaseOuterPopulationObservable N M W0 zL zH (phaseActiveDomain N M W0 zL zH))
  · exact phase_outer_population_nonneg N M W0 zL zH
  · rintro x ⟨e,rfl,he⟩
    simp [phaseOuterPopulationObservable,he]
  · exact phase_global_outer_generator N M W0 hN hlarge zL zH γ hzL hzH hsL hsH hγ hγmax

end SerialTransferSelection

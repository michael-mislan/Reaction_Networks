import proofs.ResourceLimitedCompetition.OddsProbability

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy Set
open scoped NNReal
noncomputable local instance GainProbabilityDecidableEq (D : Finset PopulationState) : DecidableEq (StoppedPopulation D) := Classical.decEq _

def gainExceptionalSet (gain : ℝ) (N H0 L0 : ℕ) (D : Finset PopulationState) : Set (StoppedPopulation D) :=
  {x | Real.exp (((N : ℝ)/1000)*((3/5)*Real.log 4-Real.log 2-gain)) ≤ ancestralObservable N (oddsValue N H0 L0) x}

theorem global_gain_probability (gain : ℝ) (γ : ℝ) (hγ : 0 ≤ γ) (Ω N M : ℕ)
    (hN : 1000 ≤ N) (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (q t : ℝ≥0) (hq : 0 < (q : ℝ))
    (hbound : ∀ x, (stoppedPopulationModel γ hγ Ω N M zL zH (activeDomain N M zL zH)).total x ≤ q)
    (s : ActiveState (activeDomain N M zL zH))
    (hH : 0 < ancestralMembrane true s.val.live) (hL : 0 < ancestralMembrane false s.val.live) :
    ((stoppedPopulationModel γ hγ Ω N M zL zH (activeDomain N M zL zH)).uniformize q hq hbound).poissonized
      (q*t) (FiniteKernel.eventIndicator (gainExceptionalSet gain N (ancestralMembrane true s.val.live)
        (ancestralMembrane false s.val.live) (activeDomain N M zL zH))) (.inl s) ≤
      Real.exp (-(((N : ℝ)/1000)*((3/5)*Real.log 4-Real.log 2-gain))) := by
  classical
  have h := (stoppedPopulationModel γ hγ Ω N M zL zH (activeDomain N M zL zH)).uniformized_event_bound
    q t hq hbound
    (gainExceptionalSet gain N (ancestralMembrane true s.val.live) (ancestralMembrane false s.val.live) _)
    (ancestralObservable N (oddsValue N (ancestralMembrane true s.val.live) (ancestralMembrane false s.val.live)))
    (Real.exp (((N : ℝ)/1000)*((3/5)*Real.log 4-Real.log 2-gain))) 0
    (fun x => oddsValue_nonneg _ _ _ _ _)
    (fun _ hx => hx)
    (global_odds_generator γ hγ Ω N M _ _ hN zL zH hzL hzH) (.inl s)
  rw [initial_odds_value N _ s hH hL,mul_zero,add_zero] at h
  exact exp_barrier_cancel _ _ h


end ResourceLimitedCompetition

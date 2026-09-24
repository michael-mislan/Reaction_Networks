import proofs.ResourceLimitedCompetition.GlobalOdds
import proofs.FiniteCopy.UniformizedBounds

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy Set
open scoped NNReal

noncomputable local instance OddsProbabilityDecidableEq (D : Finset PopulationState) : DecidableEq (StoppedPopulation D) :=
  Classical.decEq _

theorem exp_barrier_cancel (p a : ℝ) (h : Real.exp a*p ≤ 1) : p ≤ Real.exp (-a) := by
  have hm := mul_le_mul_of_nonneg_left h (Real.exp_pos (-a)).le
  have hi : Real.exp (-a)*(Real.exp a*p)=p := by
    rw [← mul_assoc,← Real.exp_add]
    simp
  simpa only [hi,mul_one] using hm

def oddsExceptionalSet (N H0 L0 : ℕ) (D : Finset PopulationState) : Set (StoppedPopulation D) :=
  {x | Real.exp (19*(N : ℝ)/500000) ≤ ancestralObservable N (oddsValue N H0 L0) x}

theorem initial_odds_value (N : ℕ) (D : Finset PopulationState) (s : ActiveState D)
    (hH : 0 < ancestralMembrane true s.val.live) (hL : 0 < ancestralMembrane false s.val.live) :
    ancestralObservable N (oddsValue N (ancestralMembrane true s.val.live)
      (ancestralMembrane false s.val.live)) (.inl s)=1 := by
  simp only [ancestralObservable,physicalState,oddsValue,Nat.ne_of_gt hH,Nat.ne_of_gt hL,
    or_self,if_false]
  exact div_self (ne_of_gt (oddsShape_pos _ _ _))

theorem global_odds_probability (γ : ℝ) (hγ : 0 ≤ γ) (Ω N M : ℕ)
    (hN : 1000 ≤ N) (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (q t : ℝ≥0) (hq : 0 < (q : ℝ))
    (hbound : ∀ x, (stoppedPopulationModel γ hγ Ω N M zL zH (activeDomain N M zL zH)).total x ≤ q)
    (s : ActiveState (activeDomain N M zL zH))
    (hH : 0 < ancestralMembrane true s.val.live) (hL : 0 < ancestralMembrane false s.val.live) :
    ((stoppedPopulationModel γ hγ Ω N M zL zH (activeDomain N M zL zH)).uniformize q hq hbound).poissonized
      (q*t) (FiniteKernel.eventIndicator (oddsExceptionalSet N (ancestralMembrane true s.val.live)
        (ancestralMembrane false s.val.live) (activeDomain N M zL zH))) (.inl s) ≤
      Real.exp (-(19*(N : ℝ)/500000)) := by
  classical
  have h := (stoppedPopulationModel γ hγ Ω N M zL zH (activeDomain N M zL zH)).uniformized_event_bound
    q t hq hbound
    (oddsExceptionalSet N (ancestralMembrane true s.val.live) (ancestralMembrane false s.val.live) _)
    (ancestralObservable N (oddsValue N (ancestralMembrane true s.val.live) (ancestralMembrane false s.val.live)))
    (Real.exp (19*(N : ℝ)/500000)) 0
    (fun x => oddsValue_nonneg _ _ _ _ _)
    (fun _ hx => hx)
    (global_odds_generator γ hγ Ω N M _ _ hN zL zH hzL hzH) (.inl s)
  rw [initial_odds_value N _ s hH hL,mul_zero,add_zero] at h
  exact exp_barrier_cancel _ _ h

end ResourceLimitedCompetition

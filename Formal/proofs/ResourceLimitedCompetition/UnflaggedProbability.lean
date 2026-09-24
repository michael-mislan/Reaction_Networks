import proofs.ResourceLimitedCompetition.PopulationSupport
import proofs.FiniteCopy.UniformizedBounds

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy Set
open scoped NNReal

noncomputable local instance UnflaggedProbabilityDecidableEq (D : Finset PopulationState) : DecidableEq (StoppedPopulation D) :=
  Classical.decEq _

def unflaggedTerminalSet (N M : ℕ) (zL zH : ℝ) (D : Finset PopulationState) : Set (StoppedPopulation D) :=
  {x | ∃ e, x=.inr e ∧ eventReason N M zL zH e=.active}

theorem unflagged_active_indicator (N M : ℕ) (zL zH : ℝ) (D : Finset PopulationState) (s : ActiveState D) :
    FiniteKernel.eventIndicator (unflaggedTerminalSet N M zL zH D) (.inl s)=0 := by
  simp [FiniteKernel.eventIndicator,unflaggedTerminalSet]

theorem positive_unflagged_next_zero (γ : ℝ) (N M : ℕ) (hN : 1 ≤ N) (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (s : ActiveState (activeDomain N M zL zH)) (e : CellEvent s.val)
    (hr : 0 < eventRate γ (4*(N*M)) ⟨s,e⟩) :
    FiniteKernel.eventIndicator (unflaggedTerminalSet N M zL zH (activeDomain N M zL zH))
      (stoppedNext N M zL zH (activeDomain N M zL zH) (.inl s) ⟨s,e⟩)=0 := by
  classical
  by_cases ha : eventReason N M zL zH ⟨s,e⟩=.active
  · have hd := positive_active_domain_preserved N M hN zL zH γ hzL hzH s e hr ha
    simp [stoppedNext,ha,hd,FiniteKernel.eventIndicator,unflaggedTerminalSet]
  · have hn : Sum.inr ⟨s,e⟩ ∉ unflaggedTerminalSet N M zL zH (activeDomain N M zL zH) := by
      rintro ⟨e',heq,hr'⟩
      have he' := Sum.inr.inj heq
      subst e'
      exact ha hr'
    simp only [stoppedNext,if_true,if_neg ha,FiniteKernel.eventIndicator,if_neg hn]

theorem unflagged_generator (γ : ℝ) (hγ : 0 ≤ γ) (N M : ℕ) (hN : 1 ≤ N) (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (x : StoppedPopulation (activeDomain N M zL zH)) :
    (stoppedPopulationModel γ hγ (4*(N*M)) N M zL zH (activeDomain N M zL zH)).generator
      (FiniteKernel.eventIndicator (unflaggedTerminalSet N M zL zH (activeDomain N M zL zH))) x ≤ 0 := by
  classical
  cases x with
  | inr e => exact (terminal_generator γ hγ (4*(N*M)) N M zL zH _ _ e).le
  | inl s =>
    rw [active_generator,unflagged_active_indicator]
    apply Finset.sum_nonpos
    intro e _
    by_cases hz : eventRate γ (4*(N*M)) ⟨s,e⟩=0
    · simp only [hz,zero_mul,le_refl]
    · have hp := lt_of_le_of_ne (event_rate_nonneg γ hγ (4*(N*M)) ⟨s,e⟩) (Ne.symm hz)
      rw [positive_unflagged_next_zero γ N M hN zL zH hzL hzH s e hp]
      simp

theorem unflagged_probability (γ : ℝ) (hγ : 0 ≤ γ) (N M : ℕ) (hN : 1 ≤ N) (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (q t : ℝ≥0) (hq : 0 < (q : ℝ))
    (hbound : ∀ x, (stoppedPopulationModel γ hγ (4*(N*M)) N M zL zH (activeDomain N M zL zH)).total x ≤ q)
    (s : ActiveState (activeDomain N M zL zH)) :
    ((stoppedPopulationModel γ hγ (4*(N*M)) N M zL zH (activeDomain N M zL zH)).uniformize q hq hbound).poissonized
      (q*t) (FiniteKernel.eventIndicator (unflaggedTerminalSet N M zL zH (activeDomain N M zL zH))) (.inl s) ≤ 0 := by
  classical
  have h := (stoppedPopulationModel γ hγ (4*(N*M)) N M zL zH (activeDomain N M zL zH)).uniformized_event_bound
    q t hq hbound (unflaggedTerminalSet N M zL zH (activeDomain N M zL zH))
    (FiniteKernel.eventIndicator (unflaggedTerminalSet N M zL zH (activeDomain N M zL zH))) 1 0
    (by intro y; unfold FiniteKernel.eventIndicator; split_ifs <;> norm_num)
    (by intro y hy; simp only [FiniteKernel.eventIndicator,if_pos hy,le_refl])
    (unflagged_generator γ hγ N M hN zL zH hzL hzH) (.inl s)
  simpa only [unflagged_active_indicator,one_mul,mul_zero,add_zero] using h

end ResourceLimitedCompetition

import proofs.SerialTransferSelection.BatchSupport
import proofs.FiniteCopy.UniformizedBounds

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Set
open scoped NNReal

noncomputable local instance UnflaggedProbabilityDecidableEq (D : Finset PopulationState) : DecidableEq (StoppedPopulation D) :=
  Classical.decEq _

def phaseUnflaggedTerminalSet (N W0 : ℕ) (zL zH : ℝ) (D : Finset PopulationState) : Set (StoppedPopulation D) :=
  {x | ∃ e, x=.inr e ∧ phaseEventReason N W0 zL zH e=.active}

theorem phase_unflagged_active_indicator (N W0 : ℕ) (zL zH : ℝ) (D : Finset PopulationState) (s : ActiveState D) :
    FiniteKernel.eventIndicator (phaseUnflaggedTerminalSet N W0 zL zH D) (.inl s)=0 := by
  simp [FiniteKernel.eventIndicator,phaseUnflaggedTerminalSet]

theorem phase_positive_unflagged_next_zero (γ : ℝ) (N M W0 : ℕ) (hN : 1 ≤ N) (hW : W0 ≤ 2*N*M) (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (s : ActiveState (phaseActiveDomain N M W0 zL zH)) (e : CellEvent s.val)
    (hr : 0 < eventRate γ (4*W0) ⟨s,e⟩) :
    FiniteKernel.eventIndicator (phaseUnflaggedTerminalSet N W0 zL zH (phaseActiveDomain N M W0 zL zH))
      (phaseStoppedNext N W0 zL zH (phaseActiveDomain N M W0 zL zH) (.inl s) ⟨s,e⟩)=0 := by
  classical
  by_cases ha : phaseEventReason N W0 zL zH ⟨s,e⟩=.active
  · have hd := phase_positive_active_domain_preserved N M W0 hN hW zL zH γ hzL hzH s e hr ha
    simp [phaseStoppedNext,ha,hd,FiniteKernel.eventIndicator,phaseUnflaggedTerminalSet]
  · have hn : Sum.inr ⟨s,e⟩ ∉ phaseUnflaggedTerminalSet N W0 zL zH (phaseActiveDomain N M W0 zL zH) := by
      rintro ⟨e',heq,hr'⟩
      have he' := Sum.inr.inj heq
      subst e'
      exact ha hr'
    simp only [phaseStoppedNext,if_true,if_neg ha,FiniteKernel.eventIndicator,if_neg hn]

theorem phase_unflagged_generator (γ : ℝ) (hγ : 0 ≤ γ) (N M W0 : ℕ) (hN : 1 ≤ N) (hW : W0 ≤ 2*N*M) (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (x : StoppedPopulation (phaseActiveDomain N M W0 zL zH)) :
    (phaseStoppedModel γ hγ (4*W0) N W0 zL zH (phaseActiveDomain N M W0 zL zH)).generator
      (FiniteKernel.eventIndicator (phaseUnflaggedTerminalSet N W0 zL zH (phaseActiveDomain N M W0 zL zH))) x ≤ 0 := by
  classical
  cases x with
  | inr e => exact (phase_terminal_generator γ hγ (4*W0) N W0 zL zH _ _ e).le
  | inl s =>
    rw [phase_active_generator,phase_unflagged_active_indicator]
    apply Finset.sum_nonpos
    intro e _
    by_cases hz : eventRate γ (4*W0) ⟨s,e⟩=0
    · simp only [hz,zero_mul,le_refl]
    · have hp := lt_of_le_of_ne (event_rate_nonneg γ hγ (4*W0) ⟨s,e⟩) (Ne.symm hz)
      rw [phase_positive_unflagged_next_zero γ N M W0 hN hW zL zH hzL hzH s e hp]
      simp

theorem phase_unflagged_probability (γ : ℝ) (hγ : 0 ≤ γ) (N M W0 : ℕ) (hN : 1 ≤ N) (hW : W0 ≤ 2*N*M) (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (q t : ℝ≥0) (hq : 0 < (q : ℝ))
    (hbound : ∀ x, (phaseStoppedModel γ hγ (4*W0) N W0 zL zH (phaseActiveDomain N M W0 zL zH)).total x ≤ q)
    (s : ActiveState (phaseActiveDomain N M W0 zL zH)) :
    ((phaseStoppedModel γ hγ (4*W0) N W0 zL zH (phaseActiveDomain N M W0 zL zH)).uniformize q hq hbound).poissonized
      (q*t) (FiniteKernel.eventIndicator (phaseUnflaggedTerminalSet N W0 zL zH (phaseActiveDomain N M W0 zL zH))) (.inl s) ≤ 0 := by
  classical
  have h := (phaseStoppedModel γ hγ (4*W0) N W0 zL zH (phaseActiveDomain N M W0 zL zH)).uniformized_event_bound
    q t hq hbound (phaseUnflaggedTerminalSet N W0 zL zH (phaseActiveDomain N M W0 zL zH))
    (FiniteKernel.eventIndicator (phaseUnflaggedTerminalSet N W0 zL zH (phaseActiveDomain N M W0 zL zH))) 1 0
    (by intro y; unfold FiniteKernel.eventIndicator; split_ifs <;> norm_num)
    (by intro y hy; simp only [FiniteKernel.eventIndicator,if_pos hy,le_refl])
    (phase_unflagged_generator γ hγ N M W0 hN hW zL zH hzL hzH) (.inl s)
  simpa only [phase_unflagged_active_indicator,one_mul,mul_zero,add_zero] using h

end SerialTransferSelection

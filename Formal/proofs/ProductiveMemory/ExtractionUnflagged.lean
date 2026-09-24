import proofs.ProductiveMemory.ExtractionSupport
import proofs.FiniteCopy.UniformizedBounds

namespace ProductiveMemory
set_option Elab.async false
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Set
open scoped NNReal

noncomputable local instance ProductiveUnflaggedDecidableEq (D : Finset ProductiveState) : DecidableEq (ProductiveStopped D) :=
  Classical.decEq _

def productiveUnflaggedTerminalSet (N W0 J : ℕ) (rho zL zH : ℝ) (D : Finset ProductiveState) : Set (ProductiveStopped D) :=
  {x | ∃ e, x=.inr e ∧ productiveReason N W0 J rho zL zH e=.active}

theorem productive_unflagged_active_indicator (N W0 J : ℕ) (rho zL zH : ℝ) (D : Finset ProductiveState) (s : ProductiveActive D) :
    FiniteKernel.eventIndicator (productiveUnflaggedTerminalSet N W0 J rho zL zH D) (.inl s)=0 := by
  simp [FiniteKernel.eventIndicator,productiveUnflaggedTerminalSet]

theorem productive_positive_unflagged_next_zero (γ : ℝ) (N M W0 J : ℕ) (hN : 1 ≤ N) (hW : W0 ≤ 2*N*M) (rho zL zH : ℝ)
    (hrho : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (s : ProductiveActive (productiveActiveDomain N M W0 J rho zL zH)) (e : ProductiveEvent s.val)
    (hr : 0 < productiveRate rho γ (4*W0) s.val e) :
    FiniteKernel.eventIndicator (productiveUnflaggedTerminalSet N W0 J rho zL zH (productiveActiveDomain N M W0 J rho zL zH))
      (productiveStoppedNext N W0 J rho zL zH (productiveActiveDomain N M W0 J rho zL zH) (.inl s) ⟨s,e⟩)=0 := by
  classical
  by_cases ha : productiveReason N W0 J rho zL zH ⟨s,e⟩=.active
  · have hd := productive_positive_active_domain_preserved N M W0 J hN hW rho zL zH γ hrho hzL hzH s e hr ha
    simp [productiveStoppedNext,ha,hd,FiniteKernel.eventIndicator,productiveUnflaggedTerminalSet]
  · have hn : Sum.inr ⟨s,e⟩ ∉ productiveUnflaggedTerminalSet N W0 J rho zL zH (productiveActiveDomain N M W0 J rho zL zH) := by
      rintro ⟨e',heq,hr'⟩
      have he' := Sum.inr.inj heq
      subst e'
      exact ha hr'
    simp only [productiveStoppedNext,if_true,if_neg ha,FiniteKernel.eventIndicator,if_neg hn]

theorem productive_unflagged_generator (γ : ℝ) (hγ : 0 ≤ γ) (N M W0 J : ℕ) (hN : 1 ≤ N) (hW : W0 ≤ 2*N*M) (rho zL zH : ℝ)
    (hrho : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (x : ProductiveStopped (productiveActiveDomain N M W0 J rho zL zH)) :
    (productiveStoppedModel rho γ (by linarith [hrho.1]) hγ (4*W0) N W0 J zL zH (productiveActiveDomain N M W0 J rho zL zH)).generator
      (FiniteKernel.eventIndicator (productiveUnflaggedTerminalSet N W0 J rho zL zH (productiveActiveDomain N M W0 J rho zL zH))) x ≤ 0 := by
  classical
  cases x with
  | inr e => exact (productive_terminal_generator rho γ (by linarith [hrho.1]) hγ (4*W0) N W0 J zL zH _ _ e).le
  | inl s =>
    rw [productive_active_generator,productive_unflagged_active_indicator]
    apply Finset.sum_nonpos
    intro e _
    by_cases hz : productiveRate rho γ (4*W0) s.val e=0
    · simp only [hz,zero_mul,le_refl]
    · have hp := lt_of_le_of_ne (productive_rate_nonneg rho γ (by linarith [hrho.1]) hγ (4*W0) s.val e) (Ne.symm hz)
      rw [productive_positive_unflagged_next_zero γ N M W0 J hN hW rho zL zH hrho hzL hzH s e hp]
      simp

theorem productive_unflagged_probability (γ : ℝ) (hγ : 0 ≤ γ) (N M W0 J : ℕ) (hN : 1 ≤ N) (hW : W0 ≤ 2*N*M) (rho zL zH : ℝ)
    (hrho : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (q t : ℝ≥0) (hq : 0 < (q : ℝ))
    (hbound : ∀ x, (productiveStoppedModel rho γ (by linarith [hrho.1]) hγ (4*W0) N W0 J zL zH (productiveActiveDomain N M W0 J rho zL zH)).total x ≤ q)
    (s : ProductiveActive (productiveActiveDomain N M W0 J rho zL zH)) :
    ((productiveStoppedModel rho γ (by linarith [hrho.1]) hγ (4*W0) N W0 J zL zH (productiveActiveDomain N M W0 J rho zL zH)).uniformize q hq hbound).poissonized
      (q*t) (FiniteKernel.eventIndicator (productiveUnflaggedTerminalSet N W0 J rho zL zH (productiveActiveDomain N M W0 J rho zL zH))) (.inl s) ≤ 0 := by
  classical
  have h := (productiveStoppedModel rho γ (by linarith [hrho.1]) hγ (4*W0) N W0 J zL zH (productiveActiveDomain N M W0 J rho zL zH)).uniformized_event_bound
    q t hq hbound (productiveUnflaggedTerminalSet N W0 J rho zL zH (productiveActiveDomain N M W0 J rho zL zH))
    (FiniteKernel.eventIndicator (productiveUnflaggedTerminalSet N W0 J rho zL zH (productiveActiveDomain N M W0 J rho zL zH))) 1 0
    (by intro y; unfold FiniteKernel.eventIndicator; split_ifs <;> norm_num)
    (by intro y hy; simp only [FiniteKernel.eventIndicator,if_pos hy,le_refl])
    (productive_unflagged_generator γ hγ N M W0 J hN hW rho zL zH hrho hzL hzH) (.inl s)
  simpa only [productive_unflagged_active_indicator,one_mul,mul_zero,add_zero] using h

end ProductiveMemory

import proofs.ProductiveMemory.ExtractionAncestralBinding
import proofs.ProductiveMemory.ExtractionOddsScalar
import proofs.ResourceLimitedCompetition.ActiveAncestralGeometry

import proofs.ResourceLimitedCompetition.OddsProbability

namespace ProductiveMemory
set_option Elab.async false
open scoped NNReal
noncomputable local instance ProductiveOddsDecidableEq (D : Finset ProductiveState) : DecidableEq (ProductiveStopped D) := Classical.decEq _
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Set

def productiveOddsExceptionalSet (N H0 L0 : ℕ) (D : Finset ProductiveState) : Set (ProductiveStopped D) :=
  {x | Real.exp (19*(N:ℝ)/500000) ≤ productiveAncestralObservable N (oddsValue N H0 L0) x}

theorem productive_initial_odds_value (N : ℕ) (D : Finset ProductiveState) (s : ProductiveActive D)
    (hH : 0 < ancestralMembrane true s.val.population.live) (hL : 0 < ancestralMembrane false s.val.population.live) :
    productiveAncestralObservable N (oddsValue N (ancestralMembrane true s.val.population.live)
      (ancestralMembrane false s.val.population.live)) (.inl s)=1 := by
  simp only [productiveAncestralObservable,productivePhysical,oddsValue,Nat.ne_of_gt hH,Nat.ne_of_gt hL,
    or_self,if_false]
  exact div_self (ne_of_gt (oddsShape_pos _ _ _))

theorem productive_global_odds_generator (γ : ℝ) (hγ : 0 ≤ γ) (Ω N M W0 J H0 L0 : ℕ)
    (hN : 1000 ≤ N) (rho zL zH : ℝ)
    (hrho : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (x : ProductiveStopped (productiveActiveDomain N M W0 J rho zL zH)) :
    (productiveStoppedModel rho γ (by linarith [hrho.1]) hγ Ω N W0 J zL zH (productiveActiveDomain N M W0 J rho zL zH)).generator
      (productiveAncestralObservable N (oddsValue N H0 L0)) x ≤ 0 := by
  classical
  cases x with
  | inr e => exact (productive_terminal_generator rho γ (by linarith [hrho.1]) hγ Ω N W0 J zL zH _ _ e).le
  | inl s =>
    have hs := productive_active_safe N M W0 J rho zL zH s.val s.property
    have hr := extraction_ancestral_rates N (by omega) rho zL zH hzL hzH s.val.population hs.2.2.2.2.1 (productive_active_energy N M W0 J rho zL zH s)
    have hb : 0 ≤ resourceCoefficient γ s.val.population.resource Ω := by
      unfold resourceCoefficient
      positivity
    rw [productive_ancestral_generator_binding]
    by_cases hHzero : ancestralMembrane true s.val.population.live=0
    · have hZ : ancestralZ true s.val.population.live=0 := by
        have ht := hr.1.2
        rw [hHzero,Nat.cast_zero,mul_zero] at ht
        exact le_antisymm ht (ancestralZ_nonneg _ _)
      simp [oddsValue,hHzero,hZ]
    by_cases hLzero : ancestralMembrane false s.val.population.live=0
    · have hZ : ancestralZ false s.val.population.live=0 := by
        have ht := hr.2.2
        rw [hLzero,Nat.cast_zero] at ht
        exact le_antisymm ht (ancestralZ_nonneg _ _)
      simp [oddsValue,hLzero,hZ]
    have hHpos := Nat.pos_of_ne_zero hHzero
    have hLpos := Nat.pos_of_ne_zero hLzero
    have hHlower := ancestral_membrane_lower_of_pos N true s.val.population.live
      (fun c hc => ⟨(hs.2.2.2.2.1 c hc).1,(hs.2.2.2.2.1 c hc).2.le⟩) hHpos
    have hLlower := ancestral_membrane_lower_of_pos N false s.val.population.live
      (fun c hc => ⟨(hs.2.2.2.2.1 c hc).1,(hs.2.2.2.2.1 c hc).2.le⟩) hLpos
    have hHr : 0 < (ancestralMembrane true s.val.population.live : ℝ) := by exact_mod_cast hHpos
    have hLr : 0 < (ancestralMembrane false s.val.population.live : ℝ) := by exact_mod_cast hLpos
    have haH : (288/100 : ℝ) ≤ ancestralZ true s.val.population.live/(ancestralMembrane true s.val.population.live : ℝ) ∧
        ancestralZ true s.val.population.live/(ancestralMembrane true s.val.population.live : ℝ) ≤ 3 :=
      ⟨(le_div_iff₀ hHr).mpr hr.1.1,(div_le_iff₀ hHr).mpr hr.1.2⟩
    have haL : (97/100 : ℝ) ≤ ancestralZ false s.val.population.live/(ancestralMembrane false s.val.population.live : ℝ) ∧
        ancestralZ false s.val.population.live/(ancestralMembrane false s.val.population.live : ℝ) ≤ 1 :=
      ⟨(le_div_iff₀ hLr).mpr hr.2.1,(div_le_iff₀ hLr).mpr (by simpa only [one_mul] using hr.2.2)⟩
    have hscalar := extraction_odds_scalar_drift (N : ℝ)
      (ancestralMembrane true s.val.population.live) (ancestralMembrane false s.val.population.live) _ _
      (by exact_mod_cast hN) (by exact_mod_cast hHlower) (by exact_mod_cast hLlower) haH haL
    rw [div_mul_cancel₀ _ (ne_of_gt hHr),div_mul_cancel₀ _ (ne_of_gt hLr)] at hscalar
    rw [oddsValue_growth_high N H0 L0 _ _ hHpos hLpos,
      oddsValue_growth_low N H0 L0 _ _ hHpos hLpos]
    have h := mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg hb (oddsValue_nonneg N H0 L0
        (ancestralMembrane true s.val.population.live) (ancestralMembrane false s.val.population.live))) hscalar
    nlinarith only [h]

theorem productive_global_odds_probability (γ : ℝ) (hγ : 0 ≤ γ) (Ω N M W0 J : ℕ)
    (hN : 1000 ≤ N) (rho zL zH : ℝ)
    (hrho : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (q t : ℝ≥0) (hq : 0 < (q : ℝ))
    (hbound : ∀ x, (productiveStoppedModel rho γ (by linarith [hrho.1]) hγ Ω N W0 J zL zH (productiveActiveDomain N M W0 J rho zL zH)).total x ≤ q)
    (s : ProductiveActive (productiveActiveDomain N M W0 J rho zL zH))
    (hH : 0 < ancestralMembrane true s.val.population.live) (hL : 0 < ancestralMembrane false s.val.population.live) :
    ((productiveStoppedModel rho γ (by linarith [hrho.1]) hγ Ω N W0 J zL zH (productiveActiveDomain N M W0 J rho zL zH)).uniformize q hq hbound).poissonized
      (q*t) (FiniteKernel.eventIndicator (productiveOddsExceptionalSet N (ancestralMembrane true s.val.population.live)
        (ancestralMembrane false s.val.population.live) (productiveActiveDomain N M W0 J rho zL zH))) (.inl s) ≤
      Real.exp (-(19*(N : ℝ)/500000)) := by
  classical
  have h := (productiveStoppedModel rho γ (by linarith [hrho.1]) hγ Ω N W0 J zL zH (productiveActiveDomain N M W0 J rho zL zH)).uniformized_event_bound
    q t hq hbound
    (productiveOddsExceptionalSet N (ancestralMembrane true s.val.population.live) (ancestralMembrane false s.val.population.live) _)
    (productiveAncestralObservable N (oddsValue N (ancestralMembrane true s.val.population.live) (ancestralMembrane false s.val.population.live)))
    (Real.exp (19*(N : ℝ)/500000)) 0
    (fun x => oddsValue_nonneg _ _ _ _ _)
    (fun _ hx => hx)
    (productive_global_odds_generator γ hγ Ω N M W0 J _ _ hN rho zL zH hrho hzL hzH) (.inl s)
  simp only [productive_initial_odds_value N _ s hH hL,mul_zero,add_zero] at h
  exact exp_barrier_cancel _ _ h

end ProductiveMemory


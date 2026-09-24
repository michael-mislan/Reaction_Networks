import proofs.ResourceLimitedCompetition.PopulationOddsValue
import proofs.ResourceLimitedCompetition.ActiveAncestralGeometry

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy Set

theorem global_odds_generator (γ : ℝ) (hγ : 0 ≤ γ) (Ω N M H0 L0 : ℕ)
    (hN : 1000 ≤ N) (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (x : StoppedPopulation (activeDomain N M zL zH)) :
    (stoppedPopulationModel γ hγ Ω N M zL zH (activeDomain N M zL zH)).generator
      (ancestralObservable N (oddsValue N H0 L0)) x ≤ 0 := by
  classical
  cases x with
  | inr e => exact (terminal_generator γ hγ Ω N M zL zH _ _ e).le
  | inl s =>
    have hs := activeDomain_safe N M zL zH s.val s.property
    have hr := safe_ancestral_rates N (by omega) zL zH hzL hzH s.val hs.2.2.2.2.1 hs.2.2.2.2.2
    have hb : 0 ≤ resourceCoefficient γ s.val.resource Ω := by
      unfold resourceCoefficient
      positivity
    rw [ancestral_generator_binding]
    by_cases hHzero : ancestralMembrane true s.val.live=0
    · have hZ : ancestralZ true s.val.live=0 := by
        have ht := hr.1.2
        rw [hHzero,Nat.cast_zero,mul_zero] at ht
        exact le_antisymm ht (ancestralZ_nonneg _ _)
      simp [oddsValue,hHzero,hZ]
    by_cases hLzero : ancestralMembrane false s.val.live=0
    · have hZ : ancestralZ false s.val.live=0 := by
        have ht := hr.2.2
        rw [hLzero,Nat.cast_zero,mul_zero] at ht
        exact le_antisymm ht (ancestralZ_nonneg _ _)
      simp [oddsValue,hLzero,hZ]
    have hHpos := Nat.pos_of_ne_zero hHzero
    have hLpos := Nat.pos_of_ne_zero hLzero
    have hHlower := ancestral_membrane_lower_of_pos N true s.val.live
      (fun c hc => ⟨(hs.2.2.2.2.1 c hc).1,(hs.2.2.2.2.1 c hc).2.le⟩) hHpos
    have hLlower := ancestral_membrane_lower_of_pos N false s.val.live
      (fun c hc => ⟨(hs.2.2.2.2.1 c hc).1,(hs.2.2.2.2.1 c hc).2.le⟩) hLpos
    have hHr : 0 < (ancestralMembrane true s.val.live : ℝ) := by exact_mod_cast hHpos
    have hLr : 0 < (ancestralMembrane false s.val.live : ℝ) := by exact_mod_cast hLpos
    have haH : (297/100 : ℝ) ≤ ancestralZ true s.val.live/(ancestralMembrane true s.val.live : ℝ) ∧
        ancestralZ true s.val.live/(ancestralMembrane true s.val.live : ℝ) ≤ 3 :=
      ⟨(le_div_iff₀ hHr).mpr hr.1.1,(div_le_iff₀ hHr).mpr hr.1.2⟩
    have haL : (99/100 : ℝ) ≤ ancestralZ false s.val.live/(ancestralMembrane false s.val.live : ℝ) ∧
        ancestralZ false s.val.live/(ancestralMembrane false s.val.live : ℝ) ≤ 101/100 :=
      ⟨(le_div_iff₀ hLr).mpr hr.2.1,(div_le_iff₀ hLr).mpr hr.2.2⟩
    have hscalar := population_odds_scalar_drift (N : ℝ)
      (ancestralMembrane true s.val.live) (ancestralMembrane false s.val.live) _ _
      (by exact_mod_cast hN) (by exact_mod_cast hHlower) (by exact_mod_cast hLlower) haH haL
    rw [div_mul_cancel₀ _ (ne_of_gt hHr),div_mul_cancel₀ _ (ne_of_gt hLr)] at hscalar
    rw [oddsValue_growth_high N H0 L0 _ _ hHpos hLpos,
      oddsValue_growth_low N H0 L0 _ _ hHpos hLpos]
    have h := mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg hb (oddsValue_nonneg N H0 L0
        (ancestralMembrane true s.val.live) (ancestralMembrane false s.val.live))) hscalar
    nlinarith only [h]

end ResourceLimitedCompetition

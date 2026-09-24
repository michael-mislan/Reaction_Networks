import proofs.ResourceLimitedCompetition.DeadlineValue
import proofs.ResourceLimitedCompetition.ActiveAncestralGeometry

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy Set

theorem global_deadline_generator (γ : ℝ) (hγ : 0 ≤ γ) (N M W0 : ℕ)
    (hN : 1000 ≤ N) (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (x : StoppedPopulation (activeDomain N M zL zH)) :
    (stoppedPopulationModel γ hγ (4*(N*M)) N M zL zH (activeDomain N M zL zH)).generator
      (activeAncestralObservable N (deadlineValue N W0)) x ≤
      -((9/40000)*(N : ℝ)*γ)*activeAncestralObservable N (deadlineValue N W0) x := by
  classical
  cases x with
  | inr e => simp only [terminal_generator,activeAncestralObservable,mul_zero,le_refl]
  | inl s =>
    have hs := activeDomain_safe N M zL zH s.val s.property
    have hr := safe_ancestral_rates N (by omega) zL zH hzL hzH s.val hs.2.2.2.2.1 hs.2.2.2.2.2
    have hm := active_membrane_lower N M zL zH s
    have htotal := ancestral_membrane_total s.val.live
    have hW : (N : ℝ) ≤ (ancestralMembrane true s.val.live : ℝ)+ancestralMembrane false s.val.live := by
      exact_mod_cast (htotal.symm ▸ hm : N ≤ ancestralMembrane true s.val.live+ancestralMembrane false s.val.live)
    have hWpos : 0 < ancestralMembrane true s.val.live+ancestralMembrane false s.val.live := by
      omega
    have hBH : 0 ≤ (ancestralMembrane true s.val.live : ℝ) := Nat.cast_nonneg _
    have hBL : 0 ≤ (ancestralMembrane false s.val.live : ℝ) := Nat.cast_nonneg _
    have hRmin : (99/100)*((ancestralMembrane true s.val.live : ℝ)+ancestralMembrane false s.val.live) ≤
        ancestralZ true s.val.live+ancestralZ false s.val.live := by
      nlinarith only [hr.1.1,hr.2.1,hBH]
    have hRmax : ancestralZ true s.val.live+ancestralZ false s.val.live ≤
        3*((ancestralMembrane true s.val.live : ℝ)+ancestralMembrane false s.val.live) := by
      nlinarith only [hr.1.2,hr.2.2,hBL]
    have hscalar := deadline_scalar_drift (N : ℝ) _ _ (by exact_mod_cast hN) hW hRmin hRmax
    have hb : 0 ≤ resourceCoefficient γ s.val.resource (4*(N*M)) := by
      unfold resourceCoefficient
      positivity
    have hbmin := active_resource_coefficient_lower γ hγ N M (by omega) zL zH s
    have hraw := active_ancestral_generator_le γ hγ (4*(N*M)) N M zL zH _
      (deadlineValue N W0) (deadlineValue_nonneg N W0) s
    rw [ancestral_generator_binding,deadlineValue_growth_high _ _ _ _ hWpos,
      deadlineValue_growth_low _ _ _ _ hWpos] at hraw
    have hv := deadlineValue_nonneg N W0 (ancestralMembrane true s.val.live) (ancestralMembrane false s.val.live)
    have hscaled := mul_le_mul_of_nonneg_left hscalar (mul_nonneg hb hv)
    have hlast := mul_le_mul_of_nonneg_right hbmin
      (by positivity : 0 ≤ (9/10000)*(N : ℝ)*deadlineValue N W0
        (ancestralMembrane true s.val.live) (ancestralMembrane false s.val.live))
    change _ ≤ -((9/40000)*(N : ℝ)*γ)*deadlineValue N W0
      (ancestralMembrane true s.val.live) (ancestralMembrane false s.val.live)
    nlinarith only [hraw,hscaled,hlast]

end ResourceLimitedCompetition

import proofs.SerialTransferSelection.BatchAncestralBinding
import proofs.SerialTransferSelection.BatchGeometry
import proofs.ResourceLimitedCompetition.ActiveAncestralGeometry

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Set

theorem phase_active_W0_pos (N M W0 : ℕ) (zL zH : ℝ)
    (s : ActiveState (phaseActiveDomain N M W0 zL zH)) : 0 < W0 := by
  have hs := phaseActiveDomain_safe N M W0 zL zH s.val s.property
  have hq := hs.1
  have hmax := hs.2.1
  omega

theorem phase_active_membrane_lower (N M W0 : ℕ) (hM : 0 < M) (zL zH : ℝ)
    (s : ActiveState (phaseActiveDomain N M W0 zL zH)) : N ≤ membrane s.val.live := by
  have hs := phaseActiveDomain_safe N M W0 zL zH s.val s.property
  have hl := membrane_lower N s.val.live (fun c hc => (hs.2.2.2.2.1 c hc).1)
  have hlen := hs.2.2.2.1
  exact (Nat.le_mul_of_pos_right N (by omega : 0 < s.val.live.length)).trans hl

theorem phase_active_resource_coefficient_lower (γ : ℝ) (hγ : 0 ≤ γ)
    (N M W0 : ℕ) (zL zH : ℝ)
    (s : ActiveState (phaseActiveDomain N M W0 zL zH)) :
    γ/4 ≤ resourceCoefficient γ s.val.resource (4*W0) := by
  have hs := phaseActiveDomain_safe N M W0 zL zH s.val s.property
  have hw := phase_active_W0_pos N M W0 zL zH s
  have hΩ : 0 < ((4*W0 : ℕ) : ℝ) := by positivity
  have hq : (W0 : ℝ) ≤ (s.val.resource : ℝ) := by exact_mod_cast hs.1.le
  have hr : (1/4 : ℝ) ≤ (s.val.resource : ℝ)/((4*W0 : ℕ) : ℝ) := by
    apply (le_div_iff₀ hΩ).mpr
    norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hq ⊢
    nlinarith only [hq]
  have h := mul_le_mul_of_nonneg_left hr hγ
  simpa only [resourceCoefficient,div_eq_mul_inv,one_mul] using h

theorem phase_global_deadline_generator (γ : ℝ) (hγ : 0 ≤ γ) (N M W0 : ℕ)
    (hN : 1000 ≤ N) (hM : 0 < M) (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (x : StoppedPopulation (phaseActiveDomain N M W0 zL zH)) :
    (phaseStoppedModel γ hγ (4*W0) N W0 zL zH (phaseActiveDomain N M W0 zL zH)).generator
      (activeAncestralObservable N (deadlineValue N W0)) x ≤
      -((9/40000)*(N : ℝ)*γ)*activeAncestralObservable N (deadlineValue N W0) x := by
  classical
  cases x with
  | inr e => simp only [phase_terminal_generator,activeAncestralObservable,mul_zero,le_refl]
  | inl s =>
    have hs := phaseActiveDomain_safe N M W0 zL zH s.val s.property
    have hr := safe_ancestral_rates N (by omega) zL zH hzL hzH s.val hs.2.2.2.2.1 (phase_active_source_energy N M W0 zL zH s)
    have hm := phase_active_membrane_lower N M W0 hM zL zH s
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
    have hb : 0 ≤ resourceCoefficient γ s.val.resource (4*W0) := by
      unfold resourceCoefficient
      positivity
    have hbmin := phase_active_resource_coefficient_lower γ hγ N M W0 zL zH s
    have hraw := phase_active_ancestral_generator_le γ hγ (4*W0) N W0 zL zH _
      (deadlineValue N W0) (deadlineValue_nonneg N W0) s
    rw [phase_ancestral_generator_binding,deadlineValue_growth_high _ _ _ _ hWpos,
      deadlineValue_growth_low _ _ _ _ hWpos] at hraw
    have hv := deadlineValue_nonneg N W0 (ancestralMembrane true s.val.live) (ancestralMembrane false s.val.live)
    have hscaled := mul_le_mul_of_nonneg_left hscalar (mul_nonneg hb hv)
    have hlast := mul_le_mul_of_nonneg_right hbmin
      (by positivity : 0 ≤ (9/10000)*(N : ℝ)*deadlineValue N W0
        (ancestralMembrane true s.val.live) (ancestralMembrane false s.val.live))
    change _ ≤ -((9/40000)*(N : ℝ)*γ)*deadlineValue N W0
      (ancestralMembrane true s.val.live) (ancestralMembrane false s.val.live)
    nlinarith only [hraw,hscaled,hlast]

end SerialTransferSelection

import proofs.ProductiveMemory.ExtractionAncestralBinding
import proofs.ProductiveMemory.ExtractionOddsScalar
import proofs.ResourceLimitedCompetition.ActiveAncestralGeometry

namespace ProductiveMemory
set_option Elab.async false
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Set

theorem productive_active_W0_pos (N M W0 J : ℕ) (rho zL zH : ℝ)
    (s : ProductiveActive (productiveActiveDomain N M W0 J rho zL zH)) : 0 < W0 := by
  have hs := productive_active_safe N M W0 J rho zL zH s.val s.property
  have hq := hs.1
  have hmax := hs.2.1
  omega

theorem productive_active_membrane_lower (N M W0 J : ℕ) (hM : 0 < M) (rho zL zH : ℝ)
    (s : ProductiveActive (productiveActiveDomain N M W0 J rho zL zH)) : N ≤ membrane s.val.population.live := by
  have hs := productive_active_safe N M W0 J rho zL zH s.val s.property
  have hl := membrane_lower N s.val.population.live (fun c hc => (hs.2.2.2.2.1 c hc).1)
  have hlen := hs.2.2.2.1
  exact (Nat.le_mul_of_pos_right N (by omega : 0 < s.val.population.live.length)).trans hl

theorem productive_active_resource_coefficient_lower (γ : ℝ) (hγ : 0 ≤ γ)
    (N M W0 J : ℕ) (rho zL zH : ℝ)
    (s : ProductiveActive (productiveActiveDomain N M W0 J rho zL zH)) :
    γ/4 ≤ resourceCoefficient γ s.val.population.resource (4*W0) := by
  have hs := productive_active_safe N M W0 J rho zL zH s.val s.property
  have hw := productive_active_W0_pos N M W0 J rho zL zH s
  have hΩ : 0 < ((4*W0 : ℕ) : ℝ) := by positivity
  have hq : (W0 : ℝ) ≤ (s.val.population.resource : ℝ) := by exact_mod_cast hs.1.le
  have hr : (1/4 : ℝ) ≤ (s.val.population.resource : ℝ)/((4*W0 : ℕ) : ℝ) := by
    apply (le_div_iff₀ hΩ).mpr
    norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hq ⊢
    nlinarith only [hq]
  have h := mul_le_mul_of_nonneg_left hr hγ
  simpa only [resourceCoefficient,div_eq_mul_inv,one_mul] using h

theorem productive_global_deadline_generator (γ : ℝ) (hγ : 0 ≤ γ) (N M W0 J : ℕ)
    (hN : 1000 ≤ N) (hM : 0 < M) (rho zL zH : ℝ)
    (hrho : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (x : ProductiveStopped (productiveActiveDomain N M W0 J rho zL zH)) :
    (productiveStoppedModel rho γ (by linarith [hrho.1]) hγ (4*W0) N W0 J zL zH (productiveActiveDomain N M W0 J rho zL zH)).generator
      (productiveActiveAncestralObservable N (deadlineValue N W0)) x ≤
      -((9/40000)*(N : ℝ)*γ)*productiveActiveAncestralObservable N (deadlineValue N W0) x := by
  classical
  cases x with
  | inr e => simp only [productive_terminal_generator,productiveActiveAncestralObservable,mul_zero,le_refl]
  | inl s =>
    have hs := productive_active_safe N M W0 J rho zL zH s.val s.property
    have hr := extraction_ancestral_rates N (by omega) rho zL zH hzL hzH s.val.population hs.2.2.2.2.1 (productive_active_energy N M W0 J rho zL zH s)
    have hm := productive_active_membrane_lower N M W0 J hM rho zL zH s
    have htotal := ancestral_membrane_total s.val.population.live
    have hW : (N : ℝ) ≤ (ancestralMembrane true s.val.population.live : ℝ)+ancestralMembrane false s.val.population.live := by
      exact_mod_cast (htotal.symm ▸ hm : N ≤ ancestralMembrane true s.val.population.live+ancestralMembrane false s.val.population.live)
    have hWpos : 0 < ancestralMembrane true s.val.population.live+ancestralMembrane false s.val.population.live := by
      omega
    have hBH : 0 ≤ (ancestralMembrane true s.val.population.live : ℝ) := Nat.cast_nonneg _
    have hBL : 0 ≤ (ancestralMembrane false s.val.population.live : ℝ) := Nat.cast_nonneg _
    have hRmin : (97/100)*((ancestralMembrane true s.val.population.live : ℝ)+ancestralMembrane false s.val.population.live) ≤
        ancestralZ true s.val.population.live+ancestralZ false s.val.population.live := by
      nlinarith only [hr.1.1,hr.2.1,hBH]
    have hRmax : ancestralZ true s.val.population.live+ancestralZ false s.val.population.live ≤
        3*((ancestralMembrane true s.val.population.live : ℝ)+ancestralMembrane false s.val.population.live) := by
      nlinarith only [hr.1.2,hr.2.2,hBL]
    have hscalar := extraction_deadline_scalar_drift (N : ℝ) _ _ (by exact_mod_cast hN) hW hRmin hRmax
    have hb : 0 ≤ resourceCoefficient γ s.val.population.resource (4*W0) := by
      unfold resourceCoefficient
      positivity
    have hbmin := productive_active_resource_coefficient_lower γ hγ N M W0 J rho zL zH s
    have hraw := productive_active_ancestral_generator_le rho γ (by linarith [hrho.1]) hγ (4*W0) N W0 J zL zH _
      (deadlineValue N W0) (deadlineValue_nonneg N W0) s
    rw [productive_ancestral_generator_binding,deadlineValue_growth_high _ _ _ _ hWpos,
      deadlineValue_growth_low _ _ _ _ hWpos] at hraw
    have hv := deadlineValue_nonneg N W0 (ancestralMembrane true s.val.population.live) (ancestralMembrane false s.val.population.live)
    have hscaled := mul_le_mul_of_nonneg_left hscalar (mul_nonneg hb hv)
    have hlast := mul_le_mul_of_nonneg_right hbmin
      (by positivity : 0 ≤ (9/10000)*(N : ℝ)*deadlineValue N W0
        (ancestralMembrane true s.val.population.live) (ancestralMembrane false s.val.population.live))
    change _ ≤ -((9/40000)*(N : ℝ)*γ)*deadlineValue N W0
      (ancestralMembrane true s.val.population.live) (ancestralMembrane false s.val.population.live)
    nlinarith only [hraw,hscaled,hlast]

end ProductiveMemory

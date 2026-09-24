import proofs.ResourceLimitedCompetition.AncestralRates

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy

theorem ancestral_membrane_lower_of_pos (N : ℕ) (tag : Bool) (cs : List TaggedCell)
    (hv : ∀ c ∈ cs, N ≤ c.compartment.2 ∧ c.compartment.2 ≤ 2*N)
    (hB : 0 < ancestralMembrane tag cs) : N ≤ ancestralMembrane tag cs := by
  have hb := ancestral_count_bounds N tag cs hv
  have hc : 0 < ancestralCount tag cs := by
    by_contra hn
    have hz : ancestralCount tag cs=0 := by omega
    rw [hz,mul_zero] at hb
    omega
  exact (Nat.le_mul_of_pos_right N hc).trans hb.1

theorem active_founder_count_pos (N M : ℕ) (zL zH : ℝ)
    (s : ActiveState (activeDomain N M zL zH)) : 0 < M := by
  have hs := activeDomain_safe N M zL zH s.val s.property
  have hq := hs.1
  have hmax := hs.2.1
  by_contra hm
  have hm0 : M=0 := by omega
  simp only [hm0,mul_zero] at hq hmax
  omega

theorem active_membrane_lower (N M : ℕ) (zL zH : ℝ)
    (s : ActiveState (activeDomain N M zL zH)) : N ≤ membrane s.val.live := by
  have hs := activeDomain_safe N M zL zH s.val s.property
  have hm := active_founder_count_pos N M zL zH s
  have hlen := hs.2.2.2.1
  have hl := membrane_lower N s.val.live (fun c hc => (hs.2.2.2.2.1 c hc).1)
  exact (Nat.le_mul_of_pos_right N (by omega : 0 < s.val.live.length)).trans hl

theorem active_resource_coefficient_lower (γ : ℝ) (hγ : 0 ≤ γ)
    (N M : ℕ) (hN : 0 < N) (zL zH : ℝ)
    (s : ActiveState (activeDomain N M zL zH)) :
    γ/4 ≤ resourceCoefficient γ s.val.resource (4*(N*M)) := by
  have hs := activeDomain_safe N M zL zH s.val s.property
  have hm := active_founder_count_pos N M zL zH s
  have hΩ : 0 < ((4*(N*M) : ℕ) : ℝ) := by positivity
  have hq : ((N*M : ℕ) : ℝ) ≤ (s.val.resource : ℝ) := by exact_mod_cast hs.1.le
  have hr : (1/4 : ℝ) ≤ (s.val.resource : ℝ)/((4*(N*M) : ℕ) : ℝ) := by
    apply (le_div_iff₀ hΩ).mpr
    norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hq ⊢
    nlinarith only [hq]
  have h := mul_le_mul_of_nonneg_left hr hγ
  simpa only [resourceCoefficient,div_eq_mul_inv,one_mul] using h

end ResourceLimitedCompetition

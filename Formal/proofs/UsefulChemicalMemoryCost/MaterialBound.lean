import proofs.UsefulChemicalMemoryCost.Source

namespace UsefulChemicalMemoryCost

/-- Intact free residents and complexes in one daughter. Food does not carry memory. -/
theorem refill_restart (K n c : ℕ) (hm : n+2*c ≤ K)
    (ha : 1 ≤ n+c) (hb : n+c ≤ K-1) :
    restart K ⟨n,c,0,K-(n+2*c)⟩ := by
  dsimp [restart, admissible, mass, residents]
  omega

theorem complementary_daughter_return (K : ℕ) (s : State)
    (hs : admissible K s) (jn jc : ℕ)
    (hn : jn ≤ s.n) (hc : jc ≤ s.c)
    (ha : 1 ≤ jn+jc) (hb : 1 ≤ (s.n-jn)+(s.c-jc)) :
    restart K ⟨jn,jc,0,K-(jn+2*jc)⟩ ∧
    restart K ⟨s.n-jn,s.c-jc,0,K-((s.n-jn)+2*(s.c-jc))⟩ := by
  unfold admissible mass residents at hs
  constructor
  · exact refill_restart K jn jc (by omega) ha (by omega)
  · exact refill_restart K (s.n-jn) (s.c-jc) (by omega) hb (by omega)

theorem actual_refill_account (K p a b : ℕ) (hm : a+b+p=K) :
    (K-a)+(K-b)=K+p := by omega

/-- Encoding the carrier ceiling via its integer exponent avoids rounding logs. -/
theorem reliability_requires_carriers (r : ℕ)
    (h : (999 : ℚ)/1000  ≤  1-1/(2 : ℚ)^(r-1)) : 11 ≤ r := by
  by_contra hh
  have hr : r-1 ≤ 9 := by omega
  have hp : (2 : ℚ)^(r-1) ≤ 2^9 := pow_le_pow_right₀ (by norm_num) hr
  have hpos : (0 : ℚ)<2^(r-1) := by positivity
  have hi : (1 : ℚ)/2^9 ≤ 1/2^(r-1) := one_div_le_one_div_of_le hpos hp
  norm_num at hi
  simp only [one_div] at h
  linarith

theorem material_necessary (K q : ℕ) (s : State)
    (hs : admissible K s) (hq : q ≤ s.p)
    (h : (999 : ℚ)/1000  ≤  1-1/(2 : ℚ)^(residents s-1)) :
    q+11 ≤ K := by
  have := reliability_requires_carriers (residents s) h
  have := quota_limits_carriers K q s hs hq
  omega

end UsefulChemicalMemoryCost

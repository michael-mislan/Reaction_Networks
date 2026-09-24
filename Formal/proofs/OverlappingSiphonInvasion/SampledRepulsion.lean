import Mathlib

noncomputable section
open Filter
namespace OverlappingSiphonInvasion

/-- Uniform growth below one threshold and bounded relative loss everywhere
give an eventual floor independent of the initial positive sample. -/
theorem sampled_growth_eventual_floor (p : ℕ → ℝ) (ε c : ℝ)
    (hε : 0 < ε) (hc : 0 < c) (hc1 : c ≤ 1)
    (hp : ∀ n, 0 < p n)
    (hloss : ∀ n, c*p n ≤ p (n+1))
    (hgrowth : ∀ n, p n ≤ ε → 2*p n ≤ p (n+1)) :
    ∀ᶠ n in atTop, c*ε ≤ p n := by
  have hhit : ∃ N, ε ≤ p N := by
    by_contra hn
    push Not at hn
    have hlin : ∀ n : ℕ, ((n:ℝ)+1)*p 0 ≤ p n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hg := hgrowth n (hn n).le
        have hpn : p 0 ≤ p n := by
          have hnn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
          nlinarith [mul_nonneg hnn (hp 0).le]
        simp only [Nat.cast_succ]
        nlinarith only [ih,hg,hpn]
    obtain ⟨n,hnlarge⟩ := exists_nat_gt (ε/p 0)
    have hmul := (div_lt_iff₀ (hp 0)).mp hnlarge
    have hh := hlin n
    have hsmall := hn n
    nlinarith only [hmul,hh,hsmall,hp 0]
  obtain ⟨N,hN⟩ := hhit
  have hforever : ∀ k : ℕ, c*ε ≤ p (N+k) := by
    intro k
    induction k with
    | zero =>
      have hm := mul_le_mul_of_nonneg_right hc1 hε.le
      simpa only [Nat.add_zero] using le_trans (by simpa using hm) hN
    | succ k ih =>
      by_cases hsmall : p (N+k) ≤ ε
      · have hg := hgrowth (N+k) hsmall
        change c*ε ≤ p (N+k+1)
        linarith [hp (N+k)]
      · have hm := mul_le_mul_of_nonneg_left (lt_of_not_ge hsmall).le hc.le
        have hh := hloss (N+k)
        change c*ε ≤ p (N+k+1)
        exact hm.trans hh
  apply eventually_atTop.2
  refine ⟨N,?_⟩
  intro n hn
  simpa only [Nat.add_sub_of_le hn] using hforever (n-N)

end OverlappingSiphonInvasion

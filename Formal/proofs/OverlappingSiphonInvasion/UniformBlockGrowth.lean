import Mathlib

noncomputable section
namespace OverlappingSiphonInvasion

private theorem cumulative_loss_bound (a : ℕ → ℝ) (M : ℝ)
    (hstep : ∀ t, -M ≤ a (t+1)-a t) :
    ∀ n t : ℕ, -(n:ℝ)*M ≤ a (t+n)-a t := by
  intro n
  induction n with
  | zero => intro t; simp
  | succ n ih =>
    intro t
    have h1 := ih t
    have h2 := hstep (t+n)
    simp only [Nat.cast_succ]
    change -((n:ℝ)+1)*M ≤ a (t+n+1)-a t
    linarith only [h1,h2]

/-- Bounded waiting times for positive growth blocks imply a uniform linear
growth estimate. This closes the quantitative step after a compactness cover;
the source-specific positive-block hypothesis must still be established. -/
theorem bounded_blocks_linear_growth (a : ℕ → ℝ) (M : ℝ) (N : ℕ)
    (hM : 0 ≤ M) (hN : 0 < N)
    (hstep : ∀ t, -M ≤ a (t+1)-a t)
    (hblock : ∀ t, ∃ j : ℕ, 0 < j ∧ j ≤ N ∧ 1 ≤ a (t+j)-a t) :
    ∀ n t : ℕ, (n:ℝ)/N-((N:ℝ)*M+1) ≤ a (t+n)-a t := by
  have hNR : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro t
    by_cases hn : n < N
    · have hrough := cumulative_loss_bound a M hstep n t
      have hle : (n:ℝ) ≤ N := by exact_mod_cast hn.le
      have hfrac : (n:ℝ)/N ≤ 1 := (div_le_one hNR).mpr hle
      have hmul := mul_le_mul_of_nonneg_right hle hM
      linarith only [hrough,hfrac,hmul]
    · obtain ⟨j,hj,hjN,hgain⟩ := hblock t
      have hjn : j ≤ n := hjN.trans (Nat.le_of_not_gt hn)
      have hsm : n-j < n := by omega
      have htail := ih (n-j) hsm (t+j)
      have hidx : t+j+(n-j) = t+n := by omega
      rw [hidx,Nat.cast_sub hjn,sub_div] at htail
      have hjR : (j:ℝ) ≤ N := by exact_mod_cast hjN
      have hjfrac : (j:ℝ)/N ≤ 1 := (div_le_one hNR).mpr hjR
      linarith only [htail,hgain,hjfrac]

theorem bounded_blocks_uniform_window (a : ℕ → ℝ) (M : ℝ) (N : ℕ)
    (hM : 0 ≤ M) (hN : 0 < N)
    (hstep : ∀ t, -M ≤ a (t+1)-a t)
    (hblock : ∀ t, ∃ j : ℕ, 0 < j ∧ j ≤ N ∧ 1 ≤ a (t+j)-a t) :
    ∃ n : ℕ, 0 < n ∧ ∀ t, 1 < a (t+n)-a t := by
  have hNR : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  obtain ⟨n,hn⟩ := exists_nat_gt ((N:ℝ)*((N:ℝ)*M+2))
  have hn0 : 0 < n := by
    have hpos : 0 < (N:ℝ)*((N:ℝ)*M+2) := by positivity
    exact Nat.cast_pos.mp (hpos.trans hn)
  refine ⟨n,hn0,?_⟩
  intro t
  have hh := bounded_blocks_linear_growth a M N hM hN hstep hblock n t
  have hdiv : (N:ℝ)*M+2 < (n:ℝ)/N :=
    (lt_div_iff₀ hNR).mpr (by nlinarith only [hn])
  linarith only [hh,hdiv]

end OverlappingSiphonInvasion

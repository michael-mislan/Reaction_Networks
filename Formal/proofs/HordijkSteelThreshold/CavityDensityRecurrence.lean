import proofs.HordijkSteelThreshold.CavityBranching
import Mathlib.Analysis.ODE.DiscreteGronwall

namespace HordijkSteelThreshold

open Real Finset

/-- Once a normalized cavity cumulative mass has one-step multiplier
`1 + c n`, its entire adaptive history costs only the exponential of the
sum of the generation coefficients.  This is the exact cumulative envelope
used after the target-wise pivotality and factor-cone estimates. -/
theorem cavityCumulative_le_exp {S c : Nat → ℝ} {L n : Nat}
    (hS0 : 0 ≤ S L)
    (hstep : ∀ k ≥ L, S (k + 1) ≤ (1 + c k) * S k)
    (hc : ∀ k ≥ L, 0 ≤ c k) (hLn : L ≤ n) :
    S n ≤ S L * Real.exp (∑ k ∈ Ico L n, c k) := by
  simpa using discrete_gronwall (u := S) (b := fun _ => 0) (c := c)
    hS0 (by simpa using hstep) hc (by simp) hLn

/-- A uniform bound on the remaining coefficient mass gives a uniform bound
on every later cavity generation. -/
theorem cavityCumulative_le_exp_of_sum_le {S c : Nat → ℝ} {L : Nat}
    (hS0 : 0 ≤ S L)
    (hstep : ∀ k ≥ L, S (k + 1) ≤ (1 + c k) * S k)
    (hc : ∀ k ≥ L, 0 ≤ c k) {K : ℝ}
    (hsum : ∀ n ≥ L, (∑ k ∈ Ico L n, c k) ≤ K)
    {n : Nat} (hLn : L ≤ n) :
    S n ≤ S L * Real.exp K := by
  calc
    S n ≤ S L * Real.exp (∑ k ∈ Ico L n, c k) :=
      cavityCumulative_le_exp hS0 hstep hc hLn
    _ ≤ S L * Real.exp K := by
      gcongr
      exact hsum n hLn

/-- If the initial cavity density is at most `ε` and the coefficient tail is
at most `K`, no later cumulative deletion density exceeds `ε * exp K`. -/
theorem cavityCumulative_le_initialBudget {S c : Nat → ℝ} {L : Nat}
    (hS0 : 0 ≤ S L)
    {ε K : ℝ} (hinit : S L ≤ ε)
    (hstep : ∀ k ≥ L, S (k + 1) ≤ (1 + c k) * S k)
    (hc : ∀ k ≥ L, 0 ≤ c k)
    (hsum : ∀ n ≥ L, (∑ k ∈ Ico L n, c k) ≤ K)
    {n : Nat} (hLn : L ≤ n) :
    S n ≤ ε * Real.exp K := by
  exact (cavityCumulative_le_exp_of_sum_le hS0 hstep hc hsum hLn).trans
    (by gcongr)

/-- The normalized factor-cone coefficient has a summable geometric tail. -/
theorem sum_two_mul_pow_Ico_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (L n : Nat) :
    (∑ k ∈ Ico L n, 2 * r ^ k) ≤ 2 * r ^ L / (1 - r) := by
  calc
    (∑ k ∈ Ico L n, 2 * r ^ k) =
        2 * ∑ k ∈ Ico L n, r ^ k := by
      rw [Finset.mul_sum]
    _ ≤ 2 * (r ^ L / (1 - r)) := by
      gcongr
      exact geom_sum_Ico_le_of_lt_one hr0 hr1
    _ = 2 * r ^ L / (1 - r) := by ring

/-- Geometric pivotality coefficients give the explicit cumulative
amplification `exp (2 r^L / (1-r))`. -/
theorem cavityCumulative_geometric_le {S : Nat → ℝ} {r : ℝ} {L n : Nat}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hS0 : 0 ≤ S L)
    (hstep : ∀ k ≥ L, S (k + 1) ≤ (1 + 2 * r ^ k) * S k)
    (hLn : L ≤ n) :
    S n ≤ S L * Real.exp (2 * r ^ L / (1 - r)) := by
  apply cavityCumulative_le_exp_of_sum_le hS0 hstep
  · intro k hk
    positivity
  · intro N hLN
    exact sum_two_mul_pow_Ico_le hr0 hr1 L N
  · exact hLn

/-- For every genuine geometric contraction and every positive desired log
amplification budget, a finite nucleus cutoff realizes that budget. -/
theorem exists_geometric_cavity_cutoff {r K : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hK : 0 < K) :
    ∃ L : Nat, 2 * r ^ L / (1 - r) ≤ K := by
  have heps : 0 < K * (1 - r) / 2 := by positivity
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have hev : ∀ᶠ n : Nat in Filter.atTop, r ^ n < K * (1 - r) / 2 :=
    (tendsto_order.1 ht).2 _ heps
  obtain ⟨L, hL⟩ := Filter.eventually_atTop.1 hev
  refine ⟨L, ?_⟩
  apply (div_le_iff₀ (sub_pos.mpr hr1)).2
  have hpow := hL L (le_refl L)
  nlinarith

end HordijkSteelThreshold

import proofs.SpecimenReliability.Resolution

namespace SpecimenReliability
noncomputable section
open scoped BigOperators

theorem gated_one_bound (p q s : ℝ) (hq : 0 ≤ q) (hqp : q ≤ p)
    (hl : p+p-1 ≤ q) (hs : 0 ≤ s ∧ s ≤ 1) :
    (p+p-2*q)^3 * oneBound p s 2 ≤ (1+(1-s)^2)/2 := by
  have hr := discordance_interval p p q hq hqp hqp hl
  have hu : 0 ≤ (1-s)^2 ∧ (1-s)^2 ≤ 1 := ⟨sq_nonneg _, by nlinarith [hs.1,hs.2]⟩
  have hH : 1/4 ≤ (1+(1-s)^2)/2 ∧ (1+(1-s)^2)/2 ≤ 1 := by
    constructor <;> linarith
  have hq' := mul_nonneg hq (show 0 ≤ 1-(1-s)^2 by linarith)
  have hb : oneBound p s 2 ≤ 1-(p+p-2*q)*(1-(1+(1-s)^2)/2) := by
    unfold oneBound
    nlinarith only [hq']
  exact (mul_le_mul_of_nonneg_left hb (pow_nonneg hr.1 3)).trans
    (cubic_gate_bound _ _ hr hH)

theorem one_resolution {S : Type*} [Fintype S] (μ x y : S → ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (hm : ∑ i, μ i = 1)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1)
    (hequal : mean μ y = mean μ x)
    (s : ℝ) (hs : 0 ≤ s ∧ s ≤ 1) (n : ℕ) (hn : 2 ≤ n) :
    gatedRisk μ x y s 0 n ≤ (1+(1-s)^2)/2 := by
  obtain ⟨hq,hqp,hqr,hl⟩ := moments_feasible μ x y hμ hm hx hy
  have hr := discordance_interval _ _ _ hq hqp hqr hl
  have hvol : s+0 ≤ 1 := by linarith [hs.2]
  have h := (risk_count_mono μ x y hμ hx hy s 0 hs.1 (by norm_num) hvol 2 n hn).trans
    (sharp_upper μ x y hμ hm hx hy s 0 2 hs.1 (by norm_num) hvol)
  rw [hequal] at h hl
  have he (p q : ℝ) : envelope p p q s 0 2 = oneBound p s 2 := by
    simp only [envelope, oneBound, sub_zero, one_pow]
    ring
  rw [he] at h
  rw [gated_identity μ x y hm, hequal]
  rw [hequal] at hr
  exact (mul_le_mul_of_nonneg_left h (pow_nonneg hr.1 3)).trans
    (gated_one_bound _ _ s hq hqp hl hs)

theorem witness_valid :
    (∀ i, 0 ≤ corners (1/2) (1/2) 0 i) ∧
    (∑ i, corners (1/2) (1/2) 0 i) = 1 ∧
    (∀ i, 0 ≤ cornerX i ∧ cornerX i ≤ 1) ∧
    (∀ i, 0 ≤ cornerY i ∧ cornerY i ≤ 1) ∧
    mean (corners (1/2) (1/2) 0) cornerY = mean (corners (1/2) (1/2) 0) cornerX := by
  refine ⟨corners_nonneg _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    corners_normalized _ _ _, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> norm_num [cornerX]
  · intro i; fin_cases i <;> norm_num [cornerY]
  · have h := corners_moments (1/2) (1/2) 0
    exact h.2.1.trans h.1.symm

/-- A single adverse source proves every unequal split has worst risk at least
the balanced risk, which resolution proves attainable as a uniform upper bound. -/
theorem balanced_minimax_witness (a b : ℝ) :
    (1-(a+b)/2)^2 ≤ gatedRisk (corners (1/2) (1/2) 0) cornerX cornerY a b 2 := by
  rw [sharp_gate_witness]
  nlinarith [sq_nonneg (a-b)]

theorem gate_comparison_examples :
    (1-(9/20:ℝ))^2 = 121/400 ∧
    (1+(1-(19/20:ℝ))^2)/2 = 401/800 ∧
    (1-(9/20:ℝ))^2 < (1+(1-(19/20:ℝ))^2)/2 ∧
    (1+(1-(7/10:ℝ))^2)/2 < (1-(1/5:ℝ))^2 := by norm_num

theorem two_pair_failure :
    (19/20:ℝ)^2*(1-(19/20)*(1-(1-(9/20))^2)) > (1-(9/20:ℝ))^2 := by
  norm_num

end
end SpecimenReliability

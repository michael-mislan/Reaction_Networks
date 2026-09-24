import proofs.FunctionalViability.Sampling

namespace FunctionalViability
noncomputable section
open scoped BigOperators

/-- The bound is on the mass of explicit all-negative source histories. -/
theorem finite_negative_certificate {K : Type*} [Fintype K]
    (μ x y : K → ℝ) (p theta d alpha : ℝ) (n : ℕ)
    (hμ : ∀ k, 0 ≤ μ k) (hs : ∑ k, μ k = 1)
    (hx : ∀ k, 0 ≤ x k ∧ x k ≤ 1) (hy : ∀ k, 0 ≤ y k ∧ y k ≤ 1)
    (ha : ∀ k, |x k-y k| ≤ d) (hd : 0 ≤ d ∧ d ≤ 1)
    (hp : 0 ≤ p ∧ p ≤ 1) (ht : 0 ≤ theta ∧ theta ≤ p)
    (budget : (1-theta*floor d)^n ≤ alpha) :
    allNegative (mixturePath μ x y p (1/2)) (fun a => negative a.2) n ≤ alpha := by
  rw [source_sampling_identity μ x y p (1/2) hs n]
  have hL := floor_nonneg d hd
  have hq := mean_floor μ x y d hμ hs ha
  have hq0 : 0 ≤ meanResponse μ x y (1/2) := le_trans hL hq
  have hq1 := mean_le_one μ x y (1/2) hμ hs (by norm_num) hx hy
  have hm : p*meanResponse μ x y (1/2) ≤ 1 := mul_le_one₀ hp.2 hq0 hq1
  have hmul : theta*floor d ≤ p*meanResponse μ x y (1/2) :=
    mul_le_mul ht.2 hq hL hp.1
  exact le_trans (pow_le_pow_left₀ (by linarith : 0 ≤ 1-p*meanResponse μ x y (1/2))
    (by linarith : 1-p*meanResponse μ x y (1/2) ≤ 1-theta*floor d) n) budget

/-- Singleton source witnesses attain the bound for every allocation. -/
theorem sharp_source (p w d : ℝ) (n : ℕ) :
    allNegative (pathWeight p w ((1+d)/2) ((1-d)/2)) negative n =
      (1-p*floor d)^n := by
  rw [negative_factorization, source_negative, sharp_witness]

/-- The randomized rule has the claimed uniform error exactly at this budget.
The quantification is over single source types; the preceding theorem covers
all finite mixtures as well. -/
theorem sharp_budget_iff (theta d alpha : ℝ) (n : ℕ)
    (ht : 0 ≤ theta ∧ theta ≤ 1) (hd : 0 ≤ d ∧ d ≤ 1) :
    (∀ x y : ℝ, (0 ≤ x ∧ x ≤ 1) → (0 ≤ y ∧ y ≤ 1) → |x-y| ≤ d →
      allNegative (pathWeight theta (1/2) x y) negative n ≤ alpha) ↔
      (1-theta*floor d)^n ≤ alpha := by
  constructor
  · intro h
    have hw := witness_admissible d hd
    have he := h _ _ hw.1 hw.2.1 hw.2.2
    rwa [sharp_source] at he
  · intro hb x y hx hy ha
    rw [negative_factorization, source_negative]
    have hL := alignment_floor x y d ha
    have hq0 := response_nonneg (1/2) x y (by norm_num) hx hy
    have hq1 := response_le_one (1/2) x y (by norm_num) hx hy
    have hm := mul_le_one₀ ht.2 hq0 hq1
    have hmul := mul_le_mul_of_nonneg_left hL ht.1
    exact le_trans (pow_le_pow_left₀ (by linarith : 0 ≤ 1-theta*response (1/2) x y)
      (by linarith : 1-theta*response (1/2) x y ≤ 1-theta*floor d) n) hb

/-- Every allocation has an admissible state no better than the equal mixture. -/
theorem minimax_allocation (d : ℝ) (hd : 0 ≤ d ∧ d ≤ 1) :
    (∀ x y : ℝ, |x-y| ≤ d → floor d ≤ response (1/2) x y) ∧
    (∀ w : ℝ, ∃ x y : ℝ, (0 ≤ x ∧ x ≤ 1) ∧ (0 ≤ y ∧ y ≤ 1) ∧
      |x-y| ≤ d ∧ response w x y = floor d) := by
  refine ⟨fun x y h => alignment_floor x y d h, ?_⟩
  intro w
  have h := witness_admissible d hd
  exact ⟨(1+d)/2, (1-d)/2, h.1, h.2.1, h.2.2, sharp_witness w d⟩

/-- Finite calibration environments: conditional good-environment error bounds
compose without requiring calibration to be independent of the experiment. -/
theorem calibration_error {E : Type*} [Fintype E]
    (ν r : E → ℝ) (good : E → Bool) (alpha delta : ℝ)
    (hν : ∀ e, 0 ≤ ν e) (hs : ∑ e, ν e = 1)
    (hr : ∀ e, r e ≤ 1) (hg : ∀ e, good e = true → r e ≤ alpha)
    (ha : 0 ≤ alpha)
    (hb : (∑ e, if good e then 0 else ν e) ≤ delta) :
    (∑ e, ν e*r e) ≤ alpha+delta := by
  have hpoint (e : E) : ν e*r e ≤ alpha*ν e + (if good e then 0 else ν e) := by
    cases he : good e
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have h := mul_le_mul_of_nonneg_left (hr e) (hν e)
      have h0 := mul_nonneg ha (hν e)
      nlinarith
    · simp only [↓reduceIte, add_zero]
      nlinarith [mul_le_mul_of_nonneg_left (hg e he) (hν e)]
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun e _ => hpoint e)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hs, mul_one] at ht
  linarith

/-- Shared failure can never be made smaller than its own probability. -/
theorem shared_failure_floor (rho q : ℝ) (n : ℕ)
    (hr : 0 ≤ rho ∧ rho ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1) :
    rho ≤ rho+(1-rho)*(1-q)^n := by
  have h0 : 0 ≤ (1-rho)*(1-q)^n :=
    mul_nonneg (by linarith) (pow_nonneg (by linarith) n)
  linarith

/-- A small exact arithmetic benchmark: theta=1/5, d=1/2, 100 units. -/
theorem rational_budget : (1-(1/5:ℝ)*floor (1/2))^100 ≤ 1/20 := by
  norm_num [floor]

theorem worked_certificate {K : Type*} [Fintype K]
    (μ x y : K → ℝ) (p : ℝ)
    (hμ : ∀ k, 0 ≤ μ k) (hs : ∑ k, μ k = 1)
    (hx : ∀ k, 0 ≤ x k ∧ x k ≤ 1) (hy : ∀ k, 0 ≤ y k ∧ y k ≤ 1)
    (ha : ∀ k, |x k-y k| ≤ 1/2) (hp : 1/5 ≤ p ∧ p ≤ 1) :
    allNegative (mixturePath μ x y p (1/2)) (fun a => negative a.2) 100 ≤ 1/20 := by
  apply finite_negative_certificate μ x y p (1/5) (1/2) (1/20) 100 hμ hs hx hy ha
    (by norm_num) ⟨by linarith, hp.2⟩ ⟨by norm_num, hp.1⟩ rational_budget

/-- The final calibration-aware source root. Bad environments can have arbitrary
negative-record mass; good environments use the literal finite source experiment. -/
theorem calibrated_source_certificate {K E : Type*} [Fintype K] [Fintype E]
    (ν : E → ℝ) (good : E → Bool) (bad : E → ℝ)
    (μ x y : E → K → ℝ) (p theta d alpha delta : ℝ) (n : ℕ)
    (hν : ∀ e, 0 ≤ ν e) (hνs : ∑ e, ν e = 1)
    (hbad : ∀ e, bad e ≤ 1)
    (hμ : ∀ e, good e = true → ∀ k, 0 ≤ μ e k)
    (hs : ∀ e, good e = true → ∑ k, μ e k = 1)
    (hx : ∀ e, good e = true → ∀ k, 0 ≤ x e k ∧ x e k ≤ 1)
    (hy : ∀ e, good e = true → ∀ k, 0 ≤ y e k ∧ y e k ≤ 1)
    (ha : ∀ e, good e = true → ∀ k, |x e k-y e k| ≤ d)
    (hd : 0 ≤ d ∧ d ≤ 1) (hp : 0 ≤ p ∧ p ≤ 1)
    (ht : 0 ≤ theta ∧ theta ≤ p) (halpha : 0 ≤ alpha ∧ alpha ≤ 1)
    (budget : (1-theta*floor d)^n ≤ alpha)
    (failure : (∑ e, if good e then 0 else ν e) ≤ delta) :
    (∑ e, ν e * (if good e then
      allNegative (mixturePath (μ e) (x e) (y e) p (1/2)) (fun a => negative a.2) n
      else bad e)) ≤ alpha+delta := by
  have hg (e : E) (he : good e = true) :
      allNegative (mixturePath (μ e) (x e) (y e) p (1/2)) (fun a => negative a.2) n ≤ alpha :=
    finite_negative_certificate (μ e) (x e) (y e) p theta d alpha n
      (hμ e he) (hs e he) (hx e he) (hy e he) (ha e he) hd hp ht budget
  apply calibration_error ν _ good alpha delta hν hνs
  · intro e
    cases he : good e
    · simpa using hbad e
    · simpa using le_trans (hg e he) halpha.2
  · intro e he
    simpa [he] using hg e he
  · exact halpha.1
  · exact failure

/-- Exact finite-sample feasibility boundary, with nontrivial error budget. -/
theorem finite_budget_iff_alignment (theta d alpha : ℝ)
    (ht : 0 < theta) (hd : 0 ≤ d ∧ d ≤ 1) (ha : 0 < alpha ∧ alpha < 1) :
    (∃ n : ℕ, (1-theta*floor d)^n ≤ alpha) ↔ d < 1 := by
  constructor
  · rintro ⟨n, hn⟩
    by_contra h
    have he : d = 1 := by linarith
    subst d
    norm_num [floor] at hn
    linarith
  · intro h
    have hL := floor_pos d ⟨hd.1, h⟩
    have hbase : 1-theta*floor d < 1 := by nlinarith [mul_pos ht hL]
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one ha.1 hbase
    exact ⟨n, hn.le⟩

theorem single_condition_negative (p : ℝ) (n : ℕ) :
    allNegative (pathWeight p 1 0 0) negative n = 1 ∧
    allNegative (pathWeight p 0 1 1) negative n = 1 := by
  simp [negative_factorization, source_negative, response]

/-- At the missing-alignment boundary, a fully recoverable latent population
is observationally identical to absence for this finite negative record. -/
theorem invisible_boundary (p w : ℝ) (n : ℕ) :
    allNegative (pathWeight p w 1 0) negative n = 1 := by
  simp [negative_factorization, source_negative, response]

end
end FunctionalViability

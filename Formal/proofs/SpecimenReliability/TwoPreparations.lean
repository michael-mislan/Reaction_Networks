import proofs.SpecimenReliability.RecoveryMoments

namespace SpecimenReliability
noncomputable section
open scoped BigOperators

def mean {S : Type*} [Fintype S] (μ x : S → ℝ) : ℝ := ∑ s, μ s * x s

theorem average_envelope {S : Type*} [Fintype S] (μ x y : S → ℝ)
    (hs : ∑ s, μ s = 1) (a b : ℝ) (n : ℕ) :
    (∑ s, μ s * envelope (x s) (y s) (x s*y s) a b n) =
    envelope (mean μ x) (mean μ y) (mean μ (fun s => x s*y s)) a b n := by
  simp only [envelope, mean, mul_add, mul_sub, mul_one, ← mul_assoc, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.sum_mul, hs]

theorem sharp_upper {S : Type*} [Fintype S] (μ x y : S → ℝ)
    (hμ : ∀ s, 0 ≤ μ s) (hs : ∑ s, μ s = 1)
    (hx : ∀ s, 0 ≤ x s ∧ x s ≤ 1) (hy : ∀ s, 0 ≤ y s ∧ y s ≤ 1)
    (a b : ℝ) (n : ℕ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1) :
    sourceRisk μ x y a b n ≤
      envelope (mean μ x) (mean μ y) (mean μ (fun s => x s*y s)) a b n := by
  rw [source_law, ← average_envelope μ x y hs]
  exact Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left
    (pointwise_envelope a b (x s) (y s) n ha hb hab (hx s) (hy s)) (hμ s))

theorem risk_count_mono {S : Type*} [Fintype S] (μ x y : S → ℝ)
    (hμ : ∀ s, 0 ≤ μ s)
    (hx : ∀ s, 0 ≤ x s ∧ x s ≤ 1) (hy : ∀ s, 0 ≤ y s ∧ y s ≤ 1)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (k n : ℕ) (hkn : k ≤ n) : sourceRisk μ x y a b n ≤ sourceRisk μ x y a b k := by
  simp only [source_law]
  apply Finset.sum_le_sum
  intro s _
  apply mul_le_mul_of_nonneg_left _ (hμ s)
  obtain ⟨h0,h1⟩ := miss_unit_interval a b (x s) (y s) ha hb hab (hx s) (hy s)
  exact pow_le_pow_of_le_one h0 h1 hkn

theorem blank_usefulness {S : Type*} [Fintype S] (μ x y : S → ℝ)
    (hs : ∑ s, μ s = 1) (a b : ℝ) : sourceRisk μ x y a b 0 = 1 := by
  simpa only [source_law, pow_zero, mul_one] using hs

theorem balanced_minimizes (p q a b : ℝ) (n : ℕ)
    (hpq : q ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1) :
    envelope p p q ((a+b)/2) ((a+b)/2) n ≤ envelope p p q a b n := by
  have h := power_chord (1-a) (1-b) (1/2) n (by linarith) (by linarith)
    (by norm_num)
  have he : (1-1/2)*(1-a)+(1/2)*(1-b) = 1-(a+b)/2 := by ring
  rw [he] at h
  have h' := mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hpq)
  have he' : 1-(a+b)/2-(a+b)/2 = 1-a-b := by ring
  unfold envelope
  rw [he']
  nlinarith

end
end SpecimenReliability

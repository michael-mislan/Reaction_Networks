import proofs.SpecimenReliability.Calibration

namespace SpecimenReliability
noncomputable section
open scoped BigOperators

/-- Complete certificate-event mass: three independent matched reference pairs,
followed by an independent future specimen from the same recovery population.
The certificate requires every reference pair discordant and every target mark negative.
Failure of the calibration gate means unresolved, not a negative certificate. -/
def gatedRisk {S : Type*} [Fintype S] (μ x y : S → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  ∑ h : Fin 3 → Fin 4,
    (∏ i, if discordant (h i) then referenceLaw μ x y (h i) else 0) *
      sourceRisk μ x y a b n

theorem gated_identity {S : Type*} [Fintype S] (μ x y : S → ℝ)
    (hs : ∑ s, μ s = 1) (a b : ℝ) (n : ℕ) :
    gatedRisk μ x y a b n =
      (mean μ x+mean μ y-2*mean μ (fun s => x s*y s))^3 * sourceRisk μ x y a b n := by
  unfold gatedRisk
  rw [← Finset.sum_mul]
  simp only [reference_law μ x y hs]
  rw [show (∑ h : Fin 3 → Fin 4, ∏ i,
      if discordant (h i) then corners (mean μ x) (mean μ y)
        (mean μ (fun s => x s*y s)) (h i) else 0) =
      calibrationPass (mean μ x) (mean μ y) (mean μ (fun s => x s*y s)) 3 from rfl]
  rw [calibration_pass]

theorem gated_envelope_bound (p q a : ℝ) (hq : 0 ≤ q) (hqp : q ≤ p)
    (hl : p+p-1 ≤ q) (ha : 0 ≤ a) (ha' : a ≤ 1/2) :
    (p+p-2*q)^3 * envelope p p q a a 2 ≤ (1-a)^2 := by
  have hr := discordance_interval p p q hq hqp hqp hl
  have hH : 1/4 ≤ (1-a)^2 ∧ (1-a)^2 ≤ 1 := by constructor <;> nlinarith
  have hj : (1-2*a)^2 ≤ 1 := by nlinarith
  have hqj : 0 ≤ q*(1-(1-2*a)^2) := mul_nonneg hq (by linarith)
  have he : envelope p p q a a 2 =
      1-(p+p-2*q)*(1-(1-a)^2)-q*(1-(1-2*a)^2) := by unfold envelope; ring
  have hb : envelope p p q a a 2 ≤ 1-(p+p-2*q)*(1-(1-a)^2) := by
    rw [he]; linarith
  exact (mul_le_mul_of_nonneg_left hb (pow_nonneg hr.1 3)).trans
    (cubic_gate_bound _ _ hr hH)

/-- Source-to-report theorem with primitive finite source premises. Neither a
negative-probability bound nor a validated-control conclusion is an input. -/
theorem resolution {S : Type*} [Fintype S] (μ x y : S → ℝ)
    (hμ : ∀ s, 0 ≤ μ s) (hs : ∑ s, μ s = 1)
    (hx : ∀ s, 0 ≤ x s ∧ x s ≤ 1) (hy : ∀ s, 0 ≤ y s ∧ y s ≤ 1)
    (hequal : mean μ y = mean μ x)
    (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1/2)
    (n : ℕ) (hn : 2 ≤ n) : gatedRisk μ x y a a n ≤ (1-a)^2 := by
  obtain ⟨hq,hqp,hqr,hl⟩ := moments_feasible μ x y hμ hs hx hy
  have hr := discordance_interval _ _ _ hq hqp hqr hl
  have hm := risk_count_mono μ x y hμ hx hy a a ha ha (by linarith) 2 n hn
  have hb := sharp_upper μ x y hμ hs hx hy a a 2 ha ha (by linarith)
  rw [gated_identity μ x y hs]
  have h := mul_le_mul_of_nonneg_left (hm.trans hb) (pow_nonneg hr.1 3)
  rw [hequal] at h hl
  rw [hequal]
  exact h.trans (gated_envelope_bound _ _ a hq hqp hl ha ha')

theorem gated_blank_rate {S : Type*} [Fintype S] (μ x y : S → ℝ)
    (hs : ∑ s, μ s = 1) (a b : ℝ) :
    gatedRisk μ x y a b 0 =
      (mean μ x+mean μ y-2*mean μ (fun s => x s*y s))^3 := by
  rw [gated_identity μ x y hs, blank_usefulness μ x y hs, mul_one]

theorem sharp_gate_witness (a b : ℝ) :
    gatedRisk (corners (1/2) (1/2) 0) cornerX cornerY a b 2 =
      ((1-a)^2+(1-b)^2)/2 := by
  rw [gated_identity _ _ _ (corners_normalized _ _ _), envelope_attained]
  have hm := corners_moments (1/2) (1/2) 0
  change (mean (corners (1/2) (1/2) 0) cornerX +
      mean (corners (1/2) (1/2) 0) cornerY -
      2*mean (corners (1/2) (1/2) 0) (fun i => cornerX i*cornerY i))^3 *
      envelope (1/2) (1/2) 0 a b 2 = _
  simp only [mean, hm.1, hm.2.1, hm.2.2, envelope]
  ring

theorem example_certificate {S : Type*} [Fintype S] (μ x y : S → ℝ)
    (hμ : ∀ s, 0 ≤ μ s) (hs : ∑ s, μ s = 1)
    (hx : ∀ s, 0 ≤ x s ∧ x s ≤ 1) (hy : ∀ s, 0 ≤ y s ∧ y s ≤ 1)
    (hequal : mean μ y = mean μ x) (n : ℕ) (hn : 2 ≤ n) :
    gatedRisk μ x y (9/20) (9/20) n ≤ 31/100 := by
  have h := resolution μ x y hμ hs hx hy hequal (9/20) (by norm_num)
    (by norm_num) n hn
  norm_num at h ⊢
  linarith

end
end SpecimenReliability

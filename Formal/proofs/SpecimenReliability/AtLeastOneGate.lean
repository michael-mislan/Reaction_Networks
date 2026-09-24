import proofs.SpecimenReliability.Design

namespace SpecimenReliability
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 20000

def atLeastOne : Fin 4 → Bool := ![false,true,true,true]

def acceptedRisk {S : Type*} [Fintype S] (μ x y : S → ℝ)
    (a b : ℝ) (n m : ℕ) : ℝ :=
  ∑ h : Fin m → Fin 4,
    (∏ i, if atLeastOne (h i) then referenceLaw μ x y (h i) else 0) *
      sourceRisk μ x y a b n

theorem accepted_identity {S : Type*} [Fintype S] (μ x y : S → ℝ)
    (hs : ∑ s, μ s = 1) (a b : ℝ) (n m : ℕ) :
    acceptedRisk μ x y a b n m =
      (mean μ x+mean μ y-mean μ (fun s => x s*y s))^m * sourceRisk μ x y a b n := by
  unfold acceptedRisk
  rw [← Finset.sum_mul,
    ← Fintype.sum_pow (fun j => if atLeastOne j then referenceLaw μ x y j else 0) m]
  rw [reference_law μ x y hs]
  have he (p r q : ℝ) : (∑ j, if atLeastOne j then corners p r q j else 0) = p+r-q := by
    norm_num [atLeastOne, corners, Fin.sum_univ_succ]
    ring
  rw [he]

theorem acceptance_interval (p r q : ℝ) (hq : 0 ≤ q) (hp : q ≤ p)
    (hr : q ≤ r) (hl : p+r-1 ≤ q) : 0 ≤ p+r-q ∧ p+r-q ≤ 1 := by
  constructor <;> linarith

theorem balanced_envelope_identity (p r q a : ℝ) (k : ℕ) :
    envelope p r q a a k =
      1-(p+r-q)*(1-(1-a)^k)-q*((1-a)^k-(1-2*a)^k) := by
  unfold envelope
  rw [show 1-a-a = 1-2*a by ring]
  ring

theorem balanced_envelope_le (p r q a : ℝ) (k : ℕ)
    (hq : 0 ≤ q) (ha : 0 ≤ a) (ha' : a ≤ 1/2) :
    envelope p r q a a k ≤ 1-(p+r-q)*(1-(1-a)^k) := by
  have hpow : (1-2*a)^k ≤ (1-a)^k :=
    pow_le_pow_left₀ (by linarith) (by linarith) k
  rw [balanced_envelope_identity]
  exact sub_le_self _ (mul_nonneg hq (sub_nonneg.mpr hpow))

theorem accepted_reduction {S : Type*} [Fintype S] (μ x y : S → ℝ)
    (hμ : ∀ s, 0 ≤ μ s) (hs : ∑ s, μ s = 1)
    (hx : ∀ s, 0 ≤ x s ∧ x s ≤ 1) (hy : ∀ s, 0 ≤ y s ∧ y s ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1/2) (k n m : ℕ) (hkn : k ≤ n) :
    acceptedRisk μ x y a a n m ≤
      (mean μ x+mean μ y-mean μ (fun s => x s*y s))^m *
      (1-(mean μ x+mean μ y-mean μ (fun s => x s*y s))*(1-(1-a)^k)) := by
  obtain ⟨hq,hp,hr,hl⟩ := moments_feasible μ x y hμ hs hx hy
  have hw := acceptance_interval _ _ _ hq hp hr hl
  have h := (risk_count_mono μ x y hμ hx hy a a ha ha (by linarith) k n hkn).trans
    ((sharp_upper μ x y hμ hs hx hy a a k ha ha (by linarith)).trans
      (balanced_envelope_le _ _ _ a k hq ha ha'))
  rw [accepted_identity μ x y hs]
  exact mul_le_mul_of_nonneg_left h (pow_nonneg hw.1 m)

/-- Three-pair, two-target closure; no equal-marginal assumption. -/
theorem accepted_resolution {S : Type*} [Fintype S] (μ x y : S → ℝ)
    (hμ : ∀ s, 0 ≤ μ s) (hs : ∑ s, μ s = 1)
    (hx : ∀ s, 0 ≤ x s ∧ x s ≤ 1) (hy : ∀ s, 0 ≤ y s ∧ y s ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1/2) (n : ℕ) (hn : 2 ≤ n) :
    acceptedRisk μ x y a a n 3 ≤ (1-a)^2 := by
  obtain ⟨hq,hp,hr,hl⟩ := moments_feasible μ x y hμ hs hx hy
  have hw := acceptance_interval _ _ _ hq hp hr hl
  exact (accepted_reduction μ x y hμ hs hx hy a ha ha' 2 n 3 hn).trans
    (cubic_gate_bound _ _ hw (by constructor <;> nlinarith only [ha,ha']))

theorem accepted_witness (z a : ℝ) (k m : ℕ) :
    acceptedRisk (corners (z/2) (z/2) 0) cornerX cornerY a a k m =
      z^m*(1-z*(1-(1-a)^k)) := by
  rw [accepted_identity _ _ _ (corners_normalized _ _ _), envelope_attained]
  have hm := corners_moments (z/2) (z/2) 0
  simp only [mean, hm.1, hm.2.1, hm.2.2, sub_zero]
  have he : z/2+z/2 = z := by ring
  rw [he]
  unfold envelope
  ring

theorem accepted_sharp (a : ℝ) :
    acceptedRisk (corners (1/2) (1/2) 0) cornerX cornerY a a 2 3 = (1-a)^2 := by
  simpa using accepted_witness 1 a 2 3

theorem witness_family_valid (z : ℝ) (hz : 0 ≤ z ∧ z ≤ 1) :
    (∀ i, 0 ≤ corners (z/2) (z/2) 0 i) ∧ ∑ i, corners (z/2) (z/2) 0 i = 1 := by
  exact ⟨corners_nonneg _ _ _ (by norm_num) (by linarith) (by linarith)
    (by linarith), corners_normalized _ _ _⟩

theorem discordance_subset (i : Fin 4) : discordant i = true → atLeastOne i = true := by
  fin_cases i <;> simp [discordant, atLeastOne]

theorem accepted_blank_rate {S : Type*} [Fintype S] (μ x y : S → ℝ)
    (hs : ∑ s, μ s = 1) (a b : ℝ) (m : ℕ) :
    acceptedRisk μ x y a b 0 m =
      (mean μ x+mean μ y-mean μ (fun s => x s*y s))^m := by
  rw [accepted_identity μ x y hs, blank_usefulness μ x y hs, mul_one]

theorem utility_comparison (p r q : ℝ) (m : ℕ) (hq : 0 ≤ q)
    (hp : q ≤ p) (hr : q ≤ r) : (p+r-2*q)^m ≤ (p+r-q)^m := by
  exact pow_le_pow_left₀ (by linarith) (by linarith) m

theorem utility_examples :
    ((4/5:ℝ)+(4/5)-2*(16/25))^3 = 512/15625 ∧
    ((4/5:ℝ)+(4/5)-(16/25))^3 = 13824/15625 := by norm_num

end
end SpecimenReliability

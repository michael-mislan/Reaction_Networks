import proofs.SpecimenReliability.GateTradeoff

namespace SpecimenReliability
noncomputable section
open scoped BigOperators

/-- Each reference preparation receives an independent `Poisson lam` number of
native targets instead of exactly one, so a pair is accepted with probability
`1-exp (-lam*(x+y))` conditional on the recovery state.  For every `lam ≤ 1`
this never exceeds the exactly-one-target acceptance probability `x+y-x*y`;
positivity of `lam` is not needed for the comparison. -/
theorem poisson_pointwise (lam x y : ℝ) (hlam1 : lam ≤ 1)
    (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    1-Real.exp (-(lam*(x+y))) ≤ x+y-x*y := by
  have key : ∀ t : ℝ, 0 ≤ t → 1-t ≤ Real.exp (-(lam*t)) := by
    intro t ht
    have h1 : 1-t ≤ Real.exp (-t) := by
      have h := Real.add_one_le_exp (-t)
      linarith
    have h2 : Real.exp (-t) ≤ Real.exp (-(lam*t)) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hlam1) ht])
    linarith
  have hsplit : Real.exp (-(lam*(x+y))) = Real.exp (-(lam*x)) * Real.exp (-(lam*y)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hprod : (1-x)*(1-y) ≤ Real.exp (-(lam*x)) * Real.exp (-(lam*y)) :=
    mul_le_mul (key x hx.1) (key y hy.1) (by linarith [hy.2])
      (le_of_lt (Real.exp_pos _))
  have he : x+y-x*y = 1-(1-x)*(1-y) := by ring
  rw [hsplit, he]
  linarith

/-- Pair-acceptance probability under Poisson reference loading. -/
def poissonAccept {S : Type*} [Fintype S] (μ x y : S → ℝ) (lam : ℝ) : ℝ :=
  ∑ s, μ s * (1-Real.exp (-(lam*(x s+y s))))

/-- Gate-and-report risk with Poisson reference loading. -/
def poissonRisk {S : Type*} [Fintype S] (μ x y : S → ℝ) (lam a b : ℝ) (n m : ℕ) : ℝ :=
  (poissonAccept μ x y lam)^m * sourceRisk μ x y a b n

theorem poisson_accept_nonneg {S : Type*} [Fintype S] (μ x y : S → ℝ)
    (hμ : ∀ s, 0 ≤ μ s) (hx : ∀ s, 0 ≤ x s) (hy : ∀ s, 0 ≤ y s)
    (lam : ℝ) (hlam : 0 ≤ lam) : 0 ≤ poissonAccept μ x y lam := by
  apply Finset.sum_nonneg
  intro s _
  refine mul_nonneg (hμ s) ?_
  have h : Real.exp (-(lam*(x s+y s))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [hx s, hy s])
  linarith

theorem poisson_accept_le {S : Type*} [Fintype S] (μ x y : S → ℝ)
    (hμ : ∀ s, 0 ≤ μ s)
    (hx : ∀ s, 0 ≤ x s ∧ x s ≤ 1) (hy : ∀ s, 0 ≤ y s ∧ y s ≤ 1)
    (lam : ℝ) (hlam1 : lam ≤ 1) :
    poissonAccept μ x y lam ≤ mean μ x + mean μ y - mean μ (fun s => x s*y s) := by
  have hid : mean μ x + mean μ y - mean μ (fun s => x s*y s)
      = ∑ s, μ s * (x s + y s - x s * y s) := by
    simp only [mean, mul_sub, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hid]
  apply Finset.sum_le_sum
  intro s _
  exact mul_le_mul_of_nonneg_left
    (poisson_pointwise lam (x s) (y s) hlam1 (hx s) (hy s)) (hμ s)

theorem sourceRisk_nonneg {S : Type*} [Fintype S] (μ x y : S → ℝ)
    (hμ : ∀ s, 0 ≤ μ s)
    (hx : ∀ s, 0 ≤ x s ∧ x s ≤ 1) (hy : ∀ s, 0 ≤ y s ∧ y s ≤ 1)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1) (n : ℕ) :
    0 ≤ sourceRisk μ x y a b n := by
  rw [source_law]
  apply Finset.sum_nonneg
  intro s _
  exact mul_nonneg (hμ s)
    (pow_nonneg (miss_unit_interval a b (x s) (y s) ha hb hab (hx s) (hy s)).1 n)

/-- The certified level survives Poisson reference loading unchanged, for every
`0 < lam ≤ 1`. -/
theorem poisson_general {S : Type*} [Fintype S] (μ x y : S → ℝ)
    (hμ : ∀ s, 0 ≤ μ s) (hs : ∑ s, μ s = 1)
    (hx : ∀ s, 0 ≤ x s ∧ x s ≤ 1) (hy : ∀ s, 0 ≤ y s ∧ y s ≤ 1)
    (lam a : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (ha : 0 ≤ a) (ha' : a ≤ 1/2) (k n m : ℕ) (hkn : k ≤ n) (hm : 1 ≤ m) :
    poissonRisk μ x y lam a a n m ≤ gateBound m ((1-a)^k) := by
  have hnn : 0 ≤ poissonAccept μ x y lam :=
    poisson_accept_nonneg μ x y hμ (fun s => (hx s).1) (fun s => (hy s).1) lam
      (le_of_lt hlam)
  have hle : poissonAccept μ x y lam
      ≤ mean μ x + mean μ y - mean μ (fun s => x s*y s) :=
    poisson_accept_le μ x y hμ hx hy lam hlam1
  have hsrc : 0 ≤ sourceRisk μ x y a a n :=
    sourceRisk_nonneg μ x y hμ hx hy a a ha ha (by linarith) n
  have hstep : poissonRisk μ x y lam a a n m ≤ acceptedRisk μ x y a a n m := by
    rw [accepted_identity μ x y hs]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hnn hle m) hsrc
  exact hstep.trans (accepted_general μ x y hμ hs hx hy a ha ha' k n m hkn hm)

end
end SpecimenReliability

import Mathlib.Tactic

namespace RandomViability

/-- A mass-conserving internal reaction contributes zero. Removing a present
molecule of arbitrary length gives at least this cubic restoring drift. -/
theorem cubic_removal_bound (M l : ℝ) (hl : 0 ≤ l) (hlM : l ≤ M) :
    (M - l)^3 - M^3 ≤ -l * M^2 := by
  have hp := mul_nonneg (mul_nonneg hl (sub_nonneg.mpr hlM))
    (show 0 ≤ 2 * M - l by linarith)
  nlinarith

theorem cubic_removal_sum {ι : Type*} [Fintype ι]
    (N len : ι → ℝ) (M : ℝ)
    (hN : ∀ x, 0 ≤ N x) (hlen : ∀ x, 0 ≤ len x)
    (hpresent : ∀ x, 0 < N x → len x ≤ M)
    (hmass : ∑ x, N x * len x = M) :
    (∑ x, N x * ((M - len x)^3 - M^3)) ≤ -M^3 := by
  have ht : ∀ x, N x * ((M - len x)^3 - M^3) ≤
      -(N x * len x) * M^2 := by
    intro x
    by_cases hz : N x = 0
    · simp [hz]
    · have hpos : 0 < N x := lt_of_le_of_ne (hN x) (Ne.symm hz)
      have hb := mul_le_mul_of_nonneg_left
        (cubic_removal_bound M (len x) (hlen x) (hpresent x hpos)) (hN x)
      nlinarith
  calc
    _ ≤ ∑ x, -(N x * len x) * M^2 := Finset.sum_le_sum (fun x _ => ht x)
    _ = -M^3 := by rw [← Finset.sum_mul, Finset.sum_neg_distrib, hmass]; ring

/-- The two monomer and four dimer feeds give the exact cubic input term. -/
theorem cubic_food_input (M : ℝ) :
    2 * ((M + 1)^3 - M^3) + 4 * ((M + 2)^3 - M^3) =
      30 * M^2 + 54 * M + 34 := by ring

/-- Uniform Lyapunov drift algebra for the common-turnover physical reactor.
The probabilistic Dynkin/expectation step is a separate obligation. -/
theorem physical_cubic_drift_bound (L V D : ℝ)
    (hL : 0 ≤ L) (hV : 1 ≤ V) (hD : 0 ≤ D) :
    D * (30 * L^2 + 54 * L / V + 34 / V^2 - L^3) ≤
      D * (19000 - L^3 / 2) := by
  have hVp : 0 < V := by linarith
  have hV2 : (1 : ℝ) ≤ V^2 := by nlinarith
  have hdiv : 54 * L / V ≤ 54 * L := by
    apply (div_le_iff₀ hVp).2
    nlinarith [mul_nonneg hL (show 0 ≤ V - 1 by linarith)]
  have hdiv2 : (34 : ℝ) / V^2 ≤ 34 := by
    apply (div_le_iff₀ (sq_pos_of_pos hVp)).2
    nlinarith
  have hp := mul_nonneg (sq_nonneg (L - 41)) (show 0 ≤ L + 22 by linarith)
  apply mul_le_mul_of_nonneg_left _ hD
  nlinarith

end RandomViability

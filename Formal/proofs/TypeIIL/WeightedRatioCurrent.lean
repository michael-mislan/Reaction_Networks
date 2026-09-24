import Mathlib

namespace TypeIIL

/-- Net current of a reversible weighted edge `X ⇌ sY` at the base state. -/
def weightedEdgeCurrent (p q : ℝ) : ℝ := p - q

/-- Net current of the same edge at a second state, expressed using the
concentration ratios relative to the base state. -/
def weightedEdgeRatioCurrent
    (rhoX rhoY p q : ℝ) (s : ℕ) : ℝ :=
  rhoX * p - rhoY ^ s * q

/-- Residual current after subtracting the product-species ratio times the
base current.  This normalization exposes both ordinary ratio descent and
the obstruction created by a weighted reverse monomial. -/
def weightedProductResidual
    (rhoX rhoY p q : ℝ) (s : ℕ) : ℝ :=
  weightedEdgeRatioCurrent rhoX rhoY p q s -
    rhoY * weightedEdgeCurrent p q

/-- Exact residual identity on one reversible weighted edge. -/
theorem weighted_product_residual_identity
    (rhoX rhoY p q : ℝ) (s : ℕ) (hs : 0 < s) :
    weightedProductResidual rhoX rhoY p q s =
      (rhoX - rhoY) * p + rhoY * (1 - rhoY ^ (s - 1)) * q := by
  cases s with
  | zero => simp at hs
  | succ n =>
      simp only [weightedProductResidual, weightedEdgeRatioCurrent,
        weightedEdgeCurrent, Nat.succ_sub_one]
      rw [pow_succ]
      ring

/-- At a strict ratio maximum above one, the product-normalized residual is
strictly negative.  This is the robust local sign statement that survives an
arbitrary positive output multiplicity. -/
theorem weighted_product_residual_nonpos_at_upper_step
    {rhoX rhoY p q : ℝ} {s : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hs : 0 < s)
    (hstep : rhoX ≤ rhoY) (hone : 1 ≤ rhoY) :
    weightedProductResidual rhoX rhoY p q s ≤ 0 := by
  rw [weighted_product_residual_identity rhoX rhoY p q s hs]
  have hrhoY : 0 < rhoY := lt_of_lt_of_le zero_lt_one hone
  have hpow : 1 ≤ rhoY ^ (s - 1) := by
    exact one_le_pow₀ hone
  have hfirst : (rhoX - rhoY) * p ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hstep) (le_of_lt hp)
  have hsecond : rhoY * (1 - rhoY ^ (s - 1)) * q ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (le_of_lt hrhoY)
        (sub_nonpos.mpr hpow)) (le_of_lt hq)
  linarith

/-- Sharp strict form: equality survives on a unit edge with equal adjacent
ratios, so strictness requires either a strict step or a genuinely weighted
edge. -/
theorem weighted_product_residual_neg_at_upper_step
    {rhoX rhoY p q : ℝ} {s : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hs : 0 < s)
    (hstep : rhoX ≤ rhoY) (hone : 1 < rhoY)
    (hstrict : rhoX < rhoY ∨ 1 < s) :
    weightedProductResidual rhoX rhoY p q s < 0 := by
  rw [weighted_product_residual_identity rhoX rhoY p q s hs]
  have hsecond : rhoY * (1 - rhoY ^ (s - 1)) * q ≤ 0 := by
    have hpow : 1 ≤ rhoY ^ (s - 1) := one_le_pow₀ (le_of_lt hone)
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (le_of_lt (lt_trans zero_lt_one hone))
        (sub_nonpos.mpr hpow)) (le_of_lt hq)
  rcases hstrict with hxy | hs'
  · have hfirst : (rhoX - rhoY) * p < 0 :=
      mul_neg_of_neg_of_pos (sub_neg.mpr hxy) hp
    linarith
  · have hexp : 0 < s - 1 := by omega
    have hpow : 1 < rhoY ^ (s - 1) :=
      one_lt_pow₀ hone (Nat.ne_of_gt hexp)
    have hsecondStrict : rhoY * (1 - rhoY ^ (s - 1)) * q < 0 := by
      have hmid : 1 - rhoY ^ (s - 1) < 0 := sub_neg.mpr hpow
      exact mul_neg_of_neg_of_pos
        (mul_neg_of_pos_of_neg (lt_trans zero_lt_one hone) hmid) hq
    have hfirst : (rhoX - rhoY) * p ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hstep) (le_of_lt hp)
    linarith

/-- Exact balance recurrence at an internally degraded species.  Edge `i`
delivers `s * J` copies of its current and the following edge removes
`JNext`; the same degradation rate is evaluated at two positive states. -/
theorem weighted_product_residual_balance
    {s : ℕ} {rho rhoNext J JNext JR JNextR e : ℝ}
    (hbase : (s : ℝ) * J - JNext = e)
    (hratio : (s : ℝ) * JR - JNextR = rho * e) :
    (s : ℝ) * (JR - rho * J) - (JNextR - rhoNext * JNext) =
      (rhoNext - rho) * JNext := by
  linear_combination hratio - rho * hbase

/-- The reactant-normalized residual has the especially simple edge sign:
it compares `rhoX` directly with the weighted product ratio `rhoY^s`. -/
theorem weighted_reactant_residual_identity
    (rhoX rhoY p q : ℝ) (s : ℕ) :
    weightedEdgeRatioCurrent rhoX rhoY p q s -
        rhoX * weightedEdgeCurrent p q =
      q * (rhoX - rhoY ^ s) := by
  unfold weightedEdgeRatioCurrent weightedEdgeCurrent
  ring

end TypeIIL

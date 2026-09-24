import proofs.SparseLinearRAF.GrowthBounds

namespace SparseLinearRAF
open RAF RAF.Polymer RAF.Concrete Filter Topology

/-- The large-rank activity input survives a polynomial intensity envelope.
This is a scalar input lemma, not the variable-intensity RAF theorem. -/
theorem polynomial_activity_universe_decay (t C a : Nat) {L : ℝ}
    (intensity : Nat → ℝ) (hpos : ∀ n, 0 ≤ intensity n)
    (henv : ∀ᶠ n : Nat in atTop, intensity n ≤ L*(n:ℝ)^a) :
    ∀ᶠ n : Nat in atTop,
      ((Fintype.card (Molecule t):ℝ)+3*C*n)*
        (activityParameter n (intensity n):ℝ) ≤ (9/16:ℝ)^n := by
  let f : ℝ := Fintype.card (Molecule t)
  have ht2 := (tendsto_pow_const_div_const_pow_of_one_lt (a+2)
    (by norm_num : (1:ℝ)<9/8)).const_mul (L*f)
  have ht3 := (tendsto_pow_const_div_const_pow_of_one_lt (a+3)
    (by norm_num : (1:ℝ)<9/8)).const_mul (L*3*C)
  have ht : Tendsto (fun n : Nat =>
      L*(f*(n:ℝ)^(a+2)+3*C*(n:ℝ)^(a+3))/(9/8:ℝ)^n) atTop (𝓝 0) := by
    convert ht2.add ht3 using 1
    · funext n; ring
    · simp only [mul_zero,add_zero]
  filter_upwards [henv,ht.eventually_lt_const (by norm_num : (0:ℝ)<1),
    eventually_ge_atTop 2] with n hn hs hn2
  have hnum := (div_lt_one (by positivity : (0:ℝ)<(9/8:ℝ)^n)).mp hs
  have hp := activity_le_polynomial_exp (hpos n) hn2
  have hp' : (activityParameter n (intensity n):ℝ) ≤ L*(n:ℝ)^a*(n:ℝ)^2/(2:ℝ)^n := by
    apply hp.trans
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hn (by positivity)) (by positivity)
  have hm := mul_le_mul_of_nonneg_left hp' (show 0 ≤ f+3*C*n by dsimp [f]; positivity)
  calc
    _ ≤ L*(f*(n:ℝ)^(a+2)+3*C*(n:ℝ)^(a+3))/(2:ℝ)^n := by
      convert hm using 1
      simp only [pow_add]
      dsimp [f]
      ring
    _ ≤ (9/8:ℝ)^n/(2:ℝ)^n := div_le_div_of_nonneg_right hnum.le (by positivity)
    _ = (9/16:ℝ)^n := by rw [← div_pow]; norm_num

/-- Exact cancellation at the proposed depth, before clipping and probability
assembly. This isolates the variable-intensity fixed-rank algebra. -/
theorem polynomial_rank_mass_identity (n a k : Nat) (hn : 0 < n) (L : ℝ) :
    (n:ℝ)*(Fintype.card (Molecule n):ℝ)^k*(rawActivity n (L*(n:ℝ)^a))^k*
      (channelParameter n:ℝ)^((a+1)*k+1) =
      (L*(n:ℝ)*(Fintype.card (Molecule n):ℝ)/(Fintype.card (Reaction n):ℝ))^k := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  unfold rawActivity channelParameter
  simp only [pow_add,pow_mul,mul_pow,div_pow,inv_pow]
  field_simp
  ring

end SparseLinearRAF

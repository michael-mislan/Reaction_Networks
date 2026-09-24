import proofs.PowerLawSmallRAF.LowDegreeGrammarEnvelope

namespace PowerLawSmallRAF

open Filter Topology

/-- A deterministic ratio lemma for the low-degree split.  The room condition
keeps every construction prefix away from exhausting the reaction catalogue,
while `degree * n^3 ≤ reactionCount` is the floor-free form of the cutoff. -/
theorem conditionedRatio_le_two_div_cube
    (n reactionCount degree s : Nat) (hn : 1 ≤ n)
    (hs : s ≤ n) (hroom : 2 * n ≤ reactionCount)
    (hscale : degree * n ^ 3 ≤ reactionCount) :
    (((degree - 1 : Nat) : ℝ) /
        (reactionCount - (s - 1) : Nat)) ≤
      2 / (n : ℝ) ^ 3 := by
  have hprefix : 2 * (s - 1) ≤ reactionCount := by omega
  have hdenNat : 0 < reactionCount - (s - 1) := by omega
  have hnReal : 0 < (n : ℝ) ^ 3 := by positivity
  have hdenReal : 0 < ((reactionCount - (s - 1) : Nat) : ℝ) := by positivity
  rw [div_le_div_iff₀ hdenReal hnReal]
  exact_mod_cast (show (degree - 1) * n ^ 3 ≤
      2 * (reactionCount - (s - 1)) by
    calc
      (degree - 1) * n ^ 3 ≤ degree * n ^ 3 :=
        Nat.mul_le_mul_right _ (Nat.sub_le degree 1)
      _ ≤ reactionCount := hscale
      _ ≤ 2 * (reactionCount - (s - 1)) := by omega)

theorem sourceReactionCount_has_prefix_room {n : Nat} (hn : 4 ≤ n) :
    2 * n ≤ sourceReactionCount n := by
  exact (Nat.mul_le_pow (by norm_num : 2 ≠ 1) n).trans
    (sourceReactionCount_bounds hn).1

theorem sourceLowDegree_has_cube_scale {n degree : Nat} (hn : 1 ≤ n)
    (hdegree : degree ≤ sourceReactionCount n / n ^ 3) :
    degree * n ^ 3 ≤ sourceReactionCount n := by
  exact (Nat.le_div_iff_mul_le (by positivity : 0 < n ^ 3)).mp hdegree

theorem sourceConditionedRatio_le_two_div_cube
    {n degree s : Nat} (hn : 4 ≤ n) (hs : s ≤ n)
    (hdegree : degree ≤ sourceReactionCount n / n ^ 3) :
    (((degree - 1 : Nat) : ℝ) /
        (sourceReactionCount n - (s - 1) : Nat)) ≤
      2 / (n : ℝ) ^ 3 :=
  conditionedRatio_le_two_div_cube n (sourceReactionCount n) degree s
    (by omega) hs (sourceReactionCount_has_prefix_room hn)
    (sourceLowDegree_has_cube_scale (by omega) hdegree)

/-- Concrete finite low-degree grammar estimate for the source binary-polymer
catalogue.  The cap `min n degree` loses no candidate that needs one distinct
catalysed channel per instruction. -/
theorem sourceLowDegreeGrammarEnvelope_le_budget
    {n degree : Nat} (hn : 4 ≤ n) (hdegree1 : 1 ≤ degree)
    (hdegree : degree ≤ sourceReactionCount n / n ^ 3)
    (hcontract : (((n : ℝ) + 6) ^ 2) * (2 / (n : ℝ) ^ 3) ≤ 1) :
    gatewayGrammarEnvelope 6 (sourceMoleculeCount n) (sourceReactionCount n)
        degree (min n degree) ≤
      (n : ℝ) * (((n : ℝ) + 6) ^ 2 / (sourceMoleculeCount n : ℝ)) := by
  let A : ℝ := ((n : ℝ) + 6) ^ 2
  let q : ℝ := 2 / (n : ℝ) ^ 3
  have hdegreeR : degree ≤ sourceReactionCount n :=
    hdegree.trans (Nat.div_le_self _ _)
  have hmain := gatewayGrammarEnvelope_le_uniformTerm
    6 (sourceMoleculeCount n) (sourceReactionCount n) degree (min n degree)
    A q (by positivity) (by positivity) hcontract
    (fun s hs => by
      have hsn : s ≤ n := (Finset.mem_Icc.mp hs).2.trans (Nat.min_le_left _ _)
      simpa [A, Nat.add_comm] using programCode_cast_le_cap 6 s n hsn)
    (fun s hs => by
      have hsdegree : s ≤ degree :=
        (Finset.mem_Icc.mp hs).2.trans (Nat.min_le_right _ _)
      have hpower := gatewayConditionedContain_le_power
        (sourceReactionCount n) (s - 1) degree hdegree1 hdegreeR (by omega)
      refine hpower.trans (pow_le_pow_left₀ ?_ ?_ (s - 1))
      · exact div_nonneg (by positivity) (by positivity)
      · exact sourceConditionedRatio_le_two_div_cube hn
          ((Finset.mem_Icc.mp hs).2.trans (Nat.min_le_left _ _)) hdegree)
    (fun s hs => by
      have hsdegree : s ≤ degree :=
        (Finset.mem_Icc.mp hs).2.trans (Nat.min_le_right _ _)
      rw [gatewayConditionedContain_eq_symmetricChoose
        (sourceReactionCount n) (s - 1) degree hdegree1 hdegreeR (by omega)]
      exact div_nonneg (by positivity) (by positivity))
  calc
    gatewayGrammarEnvelope 6 (sourceMoleculeCount n) (sourceReactionCount n)
        degree (min n degree) ≤
        ((min n degree : Nat) : ℝ) * (A / sourceMoleculeCount n) := hmain
    _ ≤ (n : ℝ) * (A / sourceMoleculeCount n) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Nat.min_le_left n degree
      · exact div_nonneg (by positivity) (by positivity)
    _ = (n : ℝ) * (((n : ℝ) + 6) ^ 2 /
        (sourceMoleculeCount n : ℝ)) := by rfl

theorem sourceGrammarContraction {n : Nat} (hn : 7 ≤ n) :
    (((n : ℝ) + 6) ^ 2) * (2 / (n : ℝ) ^ 3) ≤ 1 := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hnReal : (7 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : (0 : ℝ) ≤ (n : ℝ) - 7 := by linarith
  have hx2 : 0 ≤ ((n : ℝ) - 7) ^ 2 := pow_nonneg hx 2
  have hx3 : 0 ≤ ((n : ℝ) - 7) ^ 3 := pow_nonneg hx 3
  calc
    ((n : ℝ) + 6) ^ 2 * (2 / (n : ℝ) ^ 3) =
        (((n : ℝ) + 6) ^ 2 * 2) / (n : ℝ) ^ 3 := by ring
    _ ≤ 1 := (div_le_iff₀ (pow_pos hn0 3)).2 (by
      nlinarith [hx2, hx3])

/-- The polynomial prefactor in the low-degree grammar bound is negligible on
the binary-molecule scale. -/
theorem sourceGrammarPolynomial_div_pow_tendsto_zero :
    Tendsto (fun n : Nat =>
      (n : ℝ) * ((n : ℝ) + 6) ^ 2 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
  have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1
    (by norm_num : (1 : ℝ) < 2)
  have h2 := tendsto_pow_const_div_const_pow_of_one_lt 2
    (by norm_num : (1 : ℝ) < 2)
  have h3 := tendsto_pow_const_div_const_pow_of_one_lt 3
    (by norm_num : (1 : ℝ) < 2)
  have h2c : Tendsto (fun n : Nat =>
      12 * ((n : ℝ) ^ 2 / (2 : ℝ) ^ n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : Nat => (12 : ℝ)) atTop (𝓝 12)).mul h2)
  have h1c : Tendsto (fun n : Nat =>
      36 * ((n : ℝ) ^ 1 / (2 : ℝ) ^ n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : Nat => (36 : ℝ)) atTop (𝓝 36)).mul h1)
  have hsum := (h3.add h2c).add h1c
  have hsum' : Tendsto (fun n : Nat =>
      (n : ℝ) ^ 3 / (2 : ℝ) ^ n +
        12 * ((n : ℝ) ^ 2 / (2 : ℝ) ^ n) +
        36 * ((n : ℝ) ^ 1 / (2 : ℝ) ^ n)) atTop (𝓝 0) := by
    simpa only [zero_add, add_zero, mul_zero] using hsum
  apply hsum'.congr'
  filter_upwards with n
  ring

/-- Consequently the complete permissive-grammar budget tends to zero after
normalizing by the number of possible marked binary molecules. -/
theorem sourceGrammarBudget_tendsto_zero :
    Tendsto (fun n : Nat =>
      (n : ℝ) * ((n : ℝ) + 6) ^ 2 / (sourceMoleculeCount n : ℝ))
      atTop (𝓝 0) := by
  have hhalf : Tendsto (fun n : Nat =>
      ((n : ℝ) * ((n : ℝ) + 6) ^ 2 / (2 : ℝ) ^ n) / 2)
      atTop (𝓝 0) := by
    simpa only [zero_div] using
      sourceGrammarPolynomial_div_pow_tendsto_zero.div_const 2
  have hpower : Tendsto (fun n : Nat =>
      ((2 ^ (n + 1) : Nat) : ℝ) / (sourceMoleculeCount n : ℝ))
      atTop (𝓝 1) := sourcePower_div_moleculeCount_tendsto_one
  have hmul := hhalf.mul hpower
  have hmul' : Tendsto (fun n : Nat =>
      (((n : ℝ) * ((n : ℝ) + 6) ^ 2 / (2 : ℝ) ^ n) / 2) *
        (((2 ^ (n + 1) : Nat) : ℝ) / (sourceMoleculeCount n : ℝ)))
      atTop (𝓝 0) := by simpa only [zero_mul] using hmul
  apply hmul'.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hX : (sourceMoleculeCount n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt
      ((pow_pos (by norm_num) n).trans_le (sourceMoleculeCount_bounds hn).1)
  norm_num [Nat.cast_pow, pow_succ]
  field_simp

/-- Uniform extinction of the counted low-degree construction grammars for
any degree sequence below the source cutoff. -/
theorem sourceLowDegreeGrammarEnvelope_tendsto_zero
    (degree : Nat → Nat)
    (hdegree1 : ∀ᶠ n : Nat in atTop, 1 ≤ degree n)
    (hdegree : ∀ᶠ n : Nat in atTop,
      degree n ≤ sourceReactionCount n / n ^ 3) :
    Tendsto (fun n : Nat =>
      gatewayGrammarEnvelope 6 (sourceMoleculeCount n) (sourceReactionCount n)
        (degree n) (min n (degree n))) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ℝ)) atTop (𝓝 0))
    sourceGrammarBudget_tendsto_zero
  · filter_upwards [eventually_ge_atTop 7, hdegree1, hdegree] with n hn hd1 hd
    apply gatewayGrammarEnvelope_nonneg
    · exact hd1
    · exact hd.trans (Nat.div_le_self _ _)
    · exact Nat.min_le_right n (degree n)
  · filter_upwards [eventually_ge_atTop 7, hdegree1, hdegree] with n hn hd1 hd
    simpa only [mul_div_assoc] using
      sourceLowDegreeGrammarEnvelope_le_budget (by omega) hd1 hd
        (sourceGrammarContraction hn)

end PowerLawSmallRAF
